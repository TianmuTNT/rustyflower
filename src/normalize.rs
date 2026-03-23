use crate::bytecode::jump_target;
use crate::error::{DecompileError, Result};
use crate::loader::LoadedMethod;
use rust_asm::class_reader::ExceptionTableEntry;
use rust_asm::insn::Insn;
use rust_asm::opcodes;
use std::collections::{BTreeSet, HashMap, HashSet, VecDeque};

pub fn normalize_method(method: &LoadedMethod) -> Result<LoadedMethod> {
    if !contains_legacy_subroutine(method) {
        return Ok(method.clone());
    }
    let mut normalizer = Normalizer::new(method)?;
    let normalized = normalizer.normalize()?;

    let mut method = method.clone();
    method.instructions = normalized.instructions;
    method.instruction_offsets = normalized.instruction_offsets;
    method.exception_table = normalized.exception_table;
    method.insn_nodes.clear();
    method.try_catch_blocks.clear();
    Ok(method)
}

fn contains_legacy_subroutine(method: &LoadedMethod) -> bool {
    method.instructions.iter().any(|insn| {
        matches!(
            insn,
            Insn::Jump(node) if matches!(node.insn.opcode, opcodes::JSR | opcodes::JSR_W)
        ) || matches!(insn, Insn::Var(node) if node.insn.opcode == opcodes::RET)
    })
}

struct NormalizedMethod {
    instructions: Vec<Insn>,
    instruction_offsets: Vec<u16>,
    exception_table: Vec<ExceptionTableEntry>,
}

#[derive(Debug, Clone)]
struct Subroutine {
    target_offset: u16,
    offsets: Vec<u16>,
    offset_set: HashSet<u16>,
    internal_exception_entries: Vec<ExceptionTableEntry>,
}

struct Normalizer<'a> {
    method: &'a LoadedMethod,
    offset_to_index: HashMap<u16, usize>,
    subroutines: HashMap<u16, Subroutine>,
    subroutine_offsets: HashSet<u16>,
    emitted: Vec<Insn>,
    emitted_offsets: Vec<u16>,
    top_mapping: HashMap<u16, u16>,
    top_offsets: Vec<u16>,
    top_patches: Vec<TopPatch>,
    exception_table: Vec<ExceptionTableEntry>,
}

#[derive(Debug, Clone)]
struct TopPatch {
    emitted_index: usize,
    original_offset: u16,
}

impl<'a> Normalizer<'a> {
    fn new(method: &'a LoadedMethod) -> Result<Self> {
        let mut offset_to_index = HashMap::new();
        for (index, offset) in method.instruction_offsets.iter().copied().enumerate() {
            offset_to_index.insert(offset, index);
        }

        let mut subroutines = HashMap::new();
        let mut subroutine_offsets = HashSet::new();
        for (index, insn) in method.instructions.iter().enumerate() {
            let Insn::Jump(node) = insn else {
                continue;
            };
            if !matches!(node.insn.opcode, opcodes::JSR | opcodes::JSR_W) {
                continue;
            }
            let current_offset = method.instruction_offsets[index];
            let target_offset = jump_target(current_offset, node.offset)?;
            if subroutines.contains_key(&target_offset) {
                continue;
            }
            let subroutine =
                compute_subroutine(method, &offset_to_index, target_offset).ok_or_else(|| {
                    DecompileError::Unsupported(format!(
                        "legacy subroutine at offset {target_offset} is not supported"
                    ))
                })?;
            subroutine_offsets.extend(subroutine.offsets.iter().copied());
            subroutines.insert(target_offset, subroutine);
        }

        Ok(Self {
            method,
            offset_to_index,
            subroutines,
            subroutine_offsets,
            emitted: Vec::new(),
            emitted_offsets: Vec::new(),
            top_mapping: HashMap::new(),
            top_offsets: Vec::new(),
            top_patches: Vec::new(),
            exception_table: Vec::new(),
        })
    }

    fn normalize(&mut self) -> Result<NormalizedMethod> {
        for (index, insn) in self.method.instructions.iter().enumerate() {
            let original_offset = self.method.instruction_offsets[index];
            if self.subroutine_offsets.contains(&original_offset) {
                continue;
            }
            match insn {
                Insn::Jump(node) if matches!(node.insn.opcode, opcodes::JSR | opcodes::JSR_W) => {
                    let target_offset = jump_target(original_offset, node.offset)?;
                    let continuation_offset = self
                        .method
                        .instruction_offsets
                        .get(index + 1)
                        .copied()
                        .ok_or_else(|| {
                            DecompileError::Unsupported(
                                "legacy jsr without continuation".to_string(),
                            )
                        })?;
                    self.emit_subroutine_copy(target_offset, continuation_offset)?;
                }
                Insn::Var(node) if node.insn.opcode == opcodes::RET => {}
                _ => {
                    let emitted_index = self.push_emitted(insn.clone());
                    self.top_mapping
                        .insert(original_offset, self.emitted_offsets[emitted_index]);
                    self.top_offsets.push(original_offset);
                    if needs_patch(insn) {
                        self.top_patches.push(TopPatch {
                            emitted_index,
                            original_offset,
                        });
                    }
                }
            }
        }

        self.patch_top_level_instructions()?;
        self.rewrite_top_level_exception_table()?;

        Ok(NormalizedMethod {
            instructions: self.emitted.clone(),
            instruction_offsets: self.emitted_offsets.clone(),
            exception_table: self.exception_table.clone(),
        })
    }

    fn emit_subroutine_copy(&mut self, target_offset: u16, continuation_offset: u16) -> Result<()> {
        let subroutine = self
            .subroutines
            .get(&target_offset)
            .cloned()
            .ok_or_else(|| {
                DecompileError::Unsupported(format!(
                    "missing legacy subroutine at offset {target_offset}"
                ))
            })?;

        let mut local_mapping = HashMap::new();
        let mut local_offsets = Vec::new();
        let mut local_patches = Vec::new();

        for offset in &subroutine.offsets {
            let index = *self.offset_to_index.get(offset).ok_or_else(|| {
                DecompileError::InvalidClass(format!("missing instruction at offset {offset}"))
            })?;
            let insn = &self.method.instructions[index];
            if *offset == subroutine.target_offset && is_return_address_store(insn) {
                continue;
            }
            if matches!(insn, Insn::Var(node) if node.insn.opcode == opcodes::RET) {
                continue;
            }
            if matches!(insn, Insn::Jump(node) if matches!(node.insn.opcode, opcodes::JSR | opcodes::JSR_W))
            {
                return Err(DecompileError::Unsupported(
                    "nested legacy subroutines are not implemented".to_string(),
                ));
            }

            let emitted_index = self.push_emitted(insn.clone());
            let emitted_offset = self.emitted_offsets[emitted_index];
            local_mapping.insert(*offset, emitted_offset);
            local_offsets.push(*offset);
            if needs_patch(insn) {
                local_patches.push((emitted_index, *offset));
            }
        }

        for (emitted_index, original_offset) in local_patches {
            patch_instruction(
                &mut self.emitted[emitted_index],
                self.emitted_offsets[emitted_index],
                original_offset,
                |target_offset| {
                    local_mapping
                        .get(&target_offset)
                        .copied()
                        .or_else(|| self.top_mapping.get(&target_offset).copied())
                        .or_else(|| {
                            if subroutine.offset_set.contains(&target_offset)
                                && is_ret_offset(self.method, &self.offset_to_index, target_offset)
                            {
                                Some(map_boundary(&self.top_offsets, &self.top_mapping, continuation_offset))
                            } else {
                                None
                            }
                        })
                        .or_else(|| {
                            if target_offset == continuation_offset {
                                Some(map_boundary(&self.top_offsets, &self.top_mapping, target_offset))
                            } else {
                                None
                            }
                        })
                        .ok_or_else(|| {
                            DecompileError::Unsupported(format!(
                                "legacy subroutine jumps outside its region to {target_offset}"
                            ))
                        })
                },
            )?;
        }

        for entry in &subroutine.internal_exception_entries {
            let Some(start_pc) = map_local_boundary(&local_offsets, &local_mapping, entry.start_pc) else {
                continue;
            };
            let Some(end_pc) = map_local_boundary(&local_offsets, &local_mapping, entry.end_pc) else {
                continue;
            };
            let Some(handler_pc) = local_mapping.get(&entry.handler_pc).copied() else {
                continue;
            };
            self.exception_table.push(ExceptionTableEntry {
                start_pc,
                end_pc,
                handler_pc,
                catch_type: entry.catch_type,
            });
        }

        Ok(())
    }

    fn patch_top_level_instructions(&mut self) -> Result<()> {
        for patch in self.top_patches.clone() {
            let target_lookup = |target_offset| {
                self.top_mapping
                    .get(&target_offset)
                    .copied()
                    .or_else(|| Some(map_boundary(&self.top_offsets, &self.top_mapping, target_offset)))
                    .ok_or_else(|| {
                        DecompileError::Unsupported(format!(
                            "missing rewritten jump target {target_offset}"
                        ))
                    })
            };
            patch_instruction(
                &mut self.emitted[patch.emitted_index],
                self.emitted_offsets[patch.emitted_index],
                patch.original_offset,
                target_lookup,
            )?;
        }
        Ok(())
    }

    fn rewrite_top_level_exception_table(&mut self) -> Result<()> {
        for entry in &self.method.exception_table {
            let start_in_sub = self.subroutine_offsets.contains(&entry.start_pc);
            let end_in_sub = self.subroutine_offsets.contains(&entry.end_pc);
            let handler_in_sub = self.subroutine_offsets.contains(&entry.handler_pc);
            if start_in_sub || end_in_sub || handler_in_sub {
                continue;
            }

            let start_pc = map_boundary(&self.top_offsets, &self.top_mapping, entry.start_pc);
            let end_pc = map_boundary(&self.top_offsets, &self.top_mapping, entry.end_pc);
            let handler_pc = *self.top_mapping.get(&entry.handler_pc).ok_or_else(|| {
                DecompileError::Unsupported(format!(
                    "missing rewritten exception handler {}",
                    entry.handler_pc
                ))
            })?;
            self.exception_table.push(ExceptionTableEntry {
                start_pc,
                end_pc,
                handler_pc,
                catch_type: entry.catch_type,
            });
        }
        Ok(())
    }

    fn push_emitted(&mut self, insn: Insn) -> usize {
        let offset = self.emitted.len() as u16;
        self.emitted_offsets.push(offset);
        self.emitted.push(insn);
        self.emitted.len() - 1
    }
}

fn compute_subroutine(
    method: &LoadedMethod,
    offset_to_index: &HashMap<u16, usize>,
    target_offset: u16,
) -> Option<Subroutine> {
    let mut visited = BTreeSet::new();
    let mut queue = VecDeque::from([target_offset]);

    while let Some(offset) = queue.pop_front() {
        if !visited.insert(offset) {
            continue;
        }
        let index = *offset_to_index.get(&offset)?;
        for successor in instruction_successors(method, offset_to_index, index) {
            queue.push_back(successor);
        }
        for entry in &method.exception_table {
            if offset >= entry.start_pc && offset < entry.end_pc {
                queue.push_back(entry.handler_pc);
            }
        }
    }

    let offsets = visited.into_iter().collect::<Vec<_>>();
    if offsets.is_empty() {
        return None;
    }
    let offset_set = offsets.iter().copied().collect::<HashSet<_>>();
    if !offsets.iter().any(|offset| {
        matches!(
            method.instructions[*offset_to_index.get(offset).unwrap()],
            Insn::Var(ref node) if node.insn.opcode == opcodes::RET
        )
    }) {
        return None;
    }

    let internal_exception_entries = method
        .exception_table
        .iter()
        .filter(|entry| {
            offset_set.contains(&entry.handler_pc)
                && offsets
                    .iter()
                    .any(|offset| *offset >= entry.start_pc && *offset < entry.end_pc)
        })
        .cloned()
        .collect::<Vec<_>>();

    Some(Subroutine {
        target_offset,
        offsets,
        offset_set,
        internal_exception_entries,
    })
}

fn instruction_successors(
    method: &LoadedMethod,
    _offset_to_index: &HashMap<u16, usize>,
    index: usize,
) -> Vec<u16> {
    let current_offset = method.instruction_offsets[index];
    let next_offset = method.instruction_offsets.get(index + 1).copied();
    match &method.instructions[index] {
        Insn::Jump(node) if matches!(node.insn.opcode, opcodes::GOTO | opcodes::GOTO_W) => {
            jump_target(current_offset, node.offset).ok().into_iter().collect()
        }
        Insn::Jump(node)
            if matches!(
                node.insn.opcode,
                opcodes::IFEQ
                    | opcodes::IFNE
                    | opcodes::IFLT
                    | opcodes::IFGE
                    | opcodes::IFGT
                    | opcodes::IFLE
                    | opcodes::IF_ICMPEQ
                    | opcodes::IF_ICMPNE
                    | opcodes::IF_ICMPLT
                    | opcodes::IF_ICMPGE
                    | opcodes::IF_ICMPGT
                    | opcodes::IF_ICMPLE
                    | opcodes::IF_ACMPEQ
                    | opcodes::IF_ACMPNE
                    | opcodes::IFNULL
                    | opcodes::IFNONNULL
                    | opcodes::JSR
                    | opcodes::JSR_W
            ) =>
        {
            let mut out = Vec::new();
            if let Ok(target) = jump_target(current_offset, node.offset) {
                out.push(target);
            }
            if let Some(next_offset) = next_offset {
                out.push(next_offset);
            }
            out
        }
        Insn::LookupSwitch(node) => {
            let mut out = Vec::new();
            if let Ok(target) = jump_target(current_offset, node.default_offset) {
                out.push(target);
            }
            for (_, delta) in &node.pairs {
                if let Ok(target) = jump_target(current_offset, *delta) {
                    out.push(target);
                }
            }
            out
        }
        Insn::TableSwitch(node) => {
            let mut out = Vec::new();
            if let Ok(target) = jump_target(current_offset, node.default_offset) {
                out.push(target);
            }
            for delta in &node.offsets {
                if let Ok(target) = jump_target(current_offset, *delta) {
                    out.push(target);
                }
            }
            out
        }
        Insn::Var(node) if node.insn.opcode == opcodes::RET => Vec::new(),
        Insn::Simple(node)
            if matches!(
                node.opcode,
                opcodes::IRETURN
                    | opcodes::LRETURN
                    | opcodes::FRETURN
                    | opcodes::DRETURN
                    | opcodes::ARETURN
                    | opcodes::RETURN
                    | opcodes::ATHROW
            ) =>
        {
            Vec::new()
        }
        _ => next_offset.into_iter().collect(),
    }
}

fn is_return_address_store(insn: &Insn) -> bool {
    matches!(
        insn,
        Insn::Var(node)
            if matches!(
                node.insn.opcode,
                opcodes::ASTORE
                    | opcodes::ASTORE_0
                    | opcodes::ASTORE_1
                    | opcodes::ASTORE_2
                    | opcodes::ASTORE_3
            )
    ) || matches!(
        insn,
        Insn::Simple(node)
            if matches!(
                node.opcode,
                opcodes::ASTORE_0 | opcodes::ASTORE_1 | opcodes::ASTORE_2 | opcodes::ASTORE_3
            )
    )
}

fn needs_patch(insn: &Insn) -> bool {
    matches!(
        insn,
        Insn::Jump(_) | Insn::LookupSwitch(_) | Insn::TableSwitch(_)
    )
}

fn patch_instruction(
    insn: &mut Insn,
    emitted_offset: u16,
    original_offset: u16,
    mut lookup: impl FnMut(u16) -> Result<u16>,
) -> Result<()> {
    match insn {
        Insn::Jump(node) => {
            let target_offset = jump_target(original_offset, node.offset)?;
            let new_target = lookup(target_offset)?;
            node.offset = new_target as i32 - emitted_offset as i32;
        }
        Insn::LookupSwitch(node) => {
            let default_target = jump_target(original_offset, node.default_offset)?;
            let new_default = lookup(default_target)?;
            node.default_offset = new_default as i32 - emitted_offset as i32;
            for (_, delta) in &mut node.pairs {
                let target_offset = jump_target(original_offset, *delta)?;
                let new_target = lookup(target_offset)?;
                *delta = new_target as i32 - emitted_offset as i32;
            }
        }
        Insn::TableSwitch(node) => {
            let default_target = jump_target(original_offset, node.default_offset)?;
            let new_default = lookup(default_target)?;
            node.default_offset = new_default as i32 - emitted_offset as i32;
            for delta in &mut node.offsets {
                let target_offset = jump_target(original_offset, *delta)?;
                let new_target = lookup(target_offset)?;
                *delta = new_target as i32 - emitted_offset as i32;
            }
        }
        _ => {}
    }
    Ok(())
}

fn map_boundary(offsets: &[u16], mapping: &HashMap<u16, u16>, offset: u16) -> u16 {
    mapping
        .get(&offset)
        .copied()
        .or_else(|| {
            offsets
                .iter()
                .copied()
                .find(|candidate| *candidate >= offset)
                .and_then(|candidate| mapping.get(&candidate).copied())
        })
        .unwrap_or(offsets.len() as u16)
}

fn map_local_boundary(
    offsets: &[u16],
    mapping: &HashMap<u16, u16>,
    offset: u16,
) -> Option<u16> {
    mapping.get(&offset).copied().or_else(|| {
        offsets
            .iter()
            .copied()
            .find(|candidate| *candidate >= offset)
            .and_then(|candidate| mapping.get(&candidate).copied())
    })
}

fn is_ret_offset(
    method: &LoadedMethod,
    offset_to_index: &HashMap<u16, usize>,
    offset: u16,
) -> bool {
    offset_to_index
        .get(&offset)
        .and_then(|index| method.instructions.get(*index))
        .is_some_and(|insn| matches!(insn, Insn::Var(node) if node.insn.opcode == opcodes::RET))
}
