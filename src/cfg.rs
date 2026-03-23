use crate::bytecode::jump_target;
use crate::error::{DecompileError, Result};
use crate::loader::LoadedMethod;
use rust_asm::insn::Insn;
use rust_asm::opcodes;
use std::collections::{BTreeSet, HashMap, HashSet, VecDeque};

#[derive(Debug, Clone)]
pub struct BasicBlock {
    pub id: usize,
    pub start_offset: u16,
    pub end_offset: u16,
    pub first_index: usize,
    pub last_index: usize,
    pub successors: Vec<usize>,
    pub exception_successors: Vec<usize>,
}

#[derive(Debug, Clone)]
pub struct ControlFlowGraph {
    pub blocks: Vec<BasicBlock>,
    pub entry: usize,
    pub offset_to_block: HashMap<u16, usize>,
    pub order: Vec<usize>,
}

impl ControlFlowGraph {
    pub fn block_by_offset(&self, offset: u16) -> Option<&BasicBlock> {
        self.offset_to_block
            .get(&offset)
            .and_then(|id| self.blocks.get(*id))
    }
}

pub fn build_cfg(method: &LoadedMethod) -> Result<ControlFlowGraph> {
    if method.instructions.is_empty() {
        return Ok(ControlFlowGraph {
            blocks: Vec::new(),
            entry: 0,
            offset_to_block: HashMap::new(),
            order: Vec::new(),
        });
    }
    if method.instruction_offsets.len() != method.instructions.len() {
        return Err(DecompileError::Unsupported(
            "method is missing instruction offsets".to_string(),
        ));
    }

    let mut offset_to_index = HashMap::new();
    for (index, offset) in method.instruction_offsets.iter().copied().enumerate() {
        offset_to_index.insert(offset, index);
    }

    let mut block_starts = BTreeSet::new();
    block_starts.insert(method.instruction_offsets[0]);

    for (index, insn) in method.instructions.iter().enumerate() {
        let offset = method.instruction_offsets[index];
        match insn {
            Insn::Jump(node) => {
                block_starts.insert(jump_target(offset, node.offset)?);
                if is_conditional_jump(node.insn.opcode)
                    && let Some(next_offset) = method.instruction_offsets.get(index + 1)
                {
                    block_starts.insert(*next_offset);
                }
            }
            Insn::LookupSwitch(node) => {
                block_starts.insert(jump_target(offset, node.default_offset)?);
                for (_, case_offset) in &node.pairs {
                    block_starts.insert(jump_target(offset, *case_offset)?);
                }
                if let Some(next_offset) = method.instruction_offsets.get(index + 1) {
                    block_starts.insert(*next_offset);
                }
            }
            Insn::TableSwitch(node) => {
                block_starts.insert(jump_target(offset, node.default_offset)?);
                for case_offset in &node.offsets {
                    block_starts.insert(jump_target(offset, *case_offset)?);
                }
                if let Some(next_offset) = method.instruction_offsets.get(index + 1) {
                    block_starts.insert(*next_offset);
                }
            }
            _ if ends_block(insn) => {
                if let Some(next_offset) = method.instruction_offsets.get(index + 1) {
                    block_starts.insert(*next_offset);
                }
            }
            _ => {}
        }
    }

    for entry in &method.exception_table {
        if offset_to_index.contains_key(&entry.start_pc) {
            block_starts.insert(entry.start_pc);
        }
        if offset_to_index.contains_key(&entry.end_pc) {
            block_starts.insert(entry.end_pc);
        }
        if offset_to_index.contains_key(&entry.handler_pc) {
            block_starts.insert(entry.handler_pc);
        }
    }

    let starts = block_starts.into_iter().collect::<Vec<_>>();
    let mut blocks = Vec::with_capacity(starts.len());
    let mut offset_to_block = HashMap::new();
    for (id, start_offset) in starts.iter().copied().enumerate() {
        let first_index = *offset_to_index.get(&start_offset).ok_or_else(|| {
            DecompileError::InvalidClass(format!("missing instruction for offset {start_offset}"))
        })?;
        let next_start = starts.get(id + 1).copied();
        let last_index = next_start
            .and_then(|offset| offset_to_index.get(&offset).copied())
            .map(|index| index.saturating_sub(1))
            .unwrap_or(method.instructions.len() - 1);
        let end_offset = method.instruction_offsets[last_index];
        blocks.push(BasicBlock {
            id,
            start_offset,
            end_offset,
            first_index,
            last_index,
            successors: Vec::new(),
            exception_successors: Vec::new(),
        });
        offset_to_block.insert(start_offset, id);
    }

    for block_index in 0..blocks.len() {
        let last_index = blocks[block_index].last_index;
        let last_offset = method.instruction_offsets[last_index];
        let last_insn = &method.instructions[last_index];
        let mut successors = Vec::new();
        match last_insn {
            Insn::Jump(node) if is_goto(node.insn.opcode) => {
                successors.push(block_id_for_offset(
                    &offset_to_block,
                    jump_target(last_offset, node.offset)?,
                )?);
            }
            Insn::Jump(node) if matches!(node.insn.opcode, opcodes::JSR | opcodes::JSR_W) => {
                successors.push(block_id_for_offset(
                    &offset_to_block,
                    jump_target(last_offset, node.offset)?,
                )?);
                if let Some(next_offset) = method.instruction_offsets.get(last_index + 1) {
                    successors.push(block_id_for_offset(&offset_to_block, *next_offset)?);
                }
            }
            Insn::Jump(node) if is_conditional_jump(node.insn.opcode) => {
                successors.push(block_id_for_offset(
                    &offset_to_block,
                    jump_target(last_offset, node.offset)?,
                )?);
                if let Some(next_offset) = method.instruction_offsets.get(last_index + 1) {
                    successors.push(block_id_for_offset(&offset_to_block, *next_offset)?);
                }
            }
            Insn::LookupSwitch(node) => {
                successors.push(block_id_for_offset(
                    &offset_to_block,
                    jump_target(last_offset, node.default_offset)?,
                )?);
                for (_, case_offset) in &node.pairs {
                    successors.push(block_id_for_offset(
                        &offset_to_block,
                        jump_target(last_offset, *case_offset)?,
                    )?);
                }
            }
            Insn::TableSwitch(node) => {
                successors.push(block_id_for_offset(
                    &offset_to_block,
                    jump_target(last_offset, node.default_offset)?,
                )?);
                for case_offset in &node.offsets {
                    successors.push(block_id_for_offset(
                        &offset_to_block,
                        jump_target(last_offset, *case_offset)?,
                    )?);
                }
            }
            _ if ends_method(last_insn) => {}
            _ => {
                if let Some(next_offset) = method.instruction_offsets.get(last_index + 1) {
                    successors.push(block_id_for_offset(&offset_to_block, *next_offset)?);
                }
            }
        }
        successors.sort_unstable();
        successors.dedup();
        blocks[block_index].successors = successors;
    }

    for block in &mut blocks {
        let protected_offsets = method.instruction_offsets[block.first_index..=block.last_index]
            .iter()
            .copied()
            .collect::<Vec<_>>();
        let mut handlers = Vec::new();
        for entry in &method.exception_table {
            if protected_offsets
                .iter()
                .any(|offset| *offset >= entry.start_pc && *offset < entry.end_pc)
                && let Some(handler) = offset_to_block.get(&entry.handler_pc)
            {
                handlers.push(*handler);
            }
        }
        handlers.sort_unstable();
        handlers.dedup();
        block.exception_successors = handlers;
    }

    prune_dead_blocks(blocks, 0)
}

fn prune_dead_blocks(mut blocks: Vec<BasicBlock>, entry: usize) -> Result<ControlFlowGraph> {
    let mut reachable = HashSet::new();
    let mut queue = VecDeque::from([entry]);
    while let Some(block_id) = queue.pop_front() {
        if !reachable.insert(block_id) {
            continue;
        }
        let block = &blocks[block_id];
        for succ in block
            .successors
            .iter()
            .chain(block.exception_successors.iter())
            .copied()
        {
            queue.push_back(succ);
        }
    }

    let mut remap = HashMap::new();
    let mut retained = Vec::new();
    for block in blocks.drain(..) {
        if reachable.contains(&block.id) {
            let new_id = retained.len();
            remap.insert(block.id, new_id);
            retained.push(block);
        }
    }
    for block in &mut retained {
        block.id = *remap
            .get(&block.id)
            .ok_or_else(|| DecompileError::InvalidClass("block remap failed".to_string()))?;
        block.successors = block
            .successors
            .iter()
            .filter_map(|id| remap.get(id).copied())
            .collect();
        block.exception_successors = block
            .exception_successors
            .iter()
            .filter_map(|id| remap.get(id).copied())
            .collect();
    }
    let order = retained.iter().map(|block| block.id).collect::<Vec<_>>();
    let offset_to_block = retained
        .iter()
        .map(|block| (block.start_offset, block.id))
        .collect::<HashMap<_, _>>();
    Ok(ControlFlowGraph {
        blocks: retained,
        entry: *remap.get(&entry).unwrap_or(&0),
        offset_to_block,
        order,
    })
}

fn block_id_for_offset(offset_to_block: &HashMap<u16, usize>, offset: u16) -> Result<usize> {
    offset_to_block.get(&offset).copied().ok_or_else(|| {
        DecompileError::InvalidClass(format!("missing basic block at offset {offset}"))
    })
}

fn is_conditional_jump(opcode: u8) -> bool {
    matches!(
        opcode,
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
    )
}

fn is_goto(opcode: u8) -> bool {
    matches!(opcode, opcodes::GOTO | opcodes::GOTO_W)
}

fn ends_method(insn: &Insn) -> bool {
    matches!(
        insn,
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
            )
    )
}

fn ends_block(insn: &Insn) -> bool {
    matches!(
        insn,
        Insn::Jump(_) | Insn::LookupSwitch(_) | Insn::TableSwitch(_)
    ) || ends_method(insn)
}
