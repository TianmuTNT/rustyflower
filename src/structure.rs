use crate::cfg::{ControlFlowGraph, build_cfg};
use crate::error::{DecompileError, Result};
use crate::expr::{
    BlockSemantics, Stmt, StructuredExpr, Terminator, negate_condition, translate_block,
};
use crate::loader::{LoadedClass, LoadedMethod};
use std::collections::HashSet;

#[derive(Debug, Clone)]
pub enum StructuredStmt {
    Sequence(Vec<StructuredStmt>),
    Basic(Vec<Stmt>),
    Switch {
        expr: StructuredExpr,
        arms: Vec<SwitchArm>,
    },
    If {
        condition: StructuredExpr,
        then_branch: Box<StructuredStmt>,
        else_branch: Option<Box<StructuredStmt>>,
    },
    While {
        condition: StructuredExpr,
        body: Box<StructuredStmt>,
    },
    Comment(String),
    Empty,
}

#[derive(Debug, Clone)]
pub struct SwitchArm {
    pub labels: Vec<i32>,
    pub has_default: bool,
    pub body: Box<StructuredStmt>,
}

pub fn decompile_method(class: &LoadedClass, method: &LoadedMethod) -> Result<StructuredStmt> {
    let cfg = build_cfg(method)?;
    if cfg.blocks.is_empty() {
        return Ok(StructuredStmt::Sequence(Vec::new()));
    }

    let semantics = translate_blocks(class, method, &cfg)?;
    let mut builder = Builder {
        class,
        method,
        cfg: &cfg,
        semantics: &semantics,
        visited: HashSet::new(),
    };
    Ok(StructuredStmt::Sequence(builder.build_range(
        0,
        cfg.blocks.len(),
        GotoHandling::Comment,
    )?))
}

struct Builder<'a> {
    class: &'a LoadedClass,
    method: &'a LoadedMethod,
    cfg: &'a ControlFlowGraph,
    semantics: &'a [BlockSemantics],
    visited: HashSet<usize>,
}

#[derive(Debug, Clone, Copy)]
enum GotoHandling {
    Comment,
    Suppress(u16),
    Break(u16),
}

impl<'a> Builder<'a> {
    fn build_range(
        &mut self,
        start_pos: usize,
        end_pos: usize,
        goto_handling: GotoHandling,
    ) -> Result<Vec<StructuredStmt>> {
        let mut statements = Vec::new();
        let mut pos = start_pos;
        while pos < end_pos {
            let block_id = self.cfg.order[pos];
            if self.visited.contains(&block_id) {
                pos += 1;
                continue;
            }
            if let Some((stmt, next_pos, consumed)) =
                self.try_build_switch(pos, end_pos, goto_handling)?
            {
                self.visited.extend(consumed);
                statements.push(stmt);
                pos = next_pos;
                continue;
            }
            if let Some((stmt, next_pos, consumed)) =
                self.try_build_while(pos, end_pos, goto_handling)?
            {
                self.visited.extend(consumed);
                statements.push(stmt);
                pos = next_pos;
                continue;
            }
            if let Some((stmt, next_pos, consumed)) =
                self.try_build_if(pos, end_pos, goto_handling)?
            {
                self.visited.extend(consumed);
                statements.push(stmt);
                pos = next_pos;
                continue;
            }

            self.visited.insert(block_id);
            statements.push(self.basic_statement(block_id, goto_handling));
            pos += 1;
        }
        Ok(statements)
    }

    fn basic_statement(&self, block_id: usize, goto_handling: GotoHandling) -> StructuredStmt {
        let mut stmts = self.semantics[block_id].stmts.clone();
        match &self.semantics[block_id].terminator {
            Terminator::Return(value) => stmts.push(Stmt::Return(value.clone())),
            Terminator::Throw(value) => stmts.push(Stmt::Throw(value.clone())),
            Terminator::Goto(target) => match goto_handling {
                GotoHandling::Comment => stmts.push(Stmt::Comment(format!(
                    "rustyflower: unsupported goto to offset {target}"
                ))),
                GotoHandling::Suppress(suppressed) if suppressed == *target => {}
                GotoHandling::Break(merge) if merge == *target => {
                    stmts.push(Stmt::Break);
                }
                _ => stmts.push(Stmt::Comment(format!(
                    "rustyflower: unsupported goto to offset {target}"
                ))),
            },
            Terminator::Switch { .. } => {
                stmts.push(Stmt::Comment(
                    "rustyflower: switch reconstruction is not implemented yet".to_string(),
                ));
            }
            Terminator::Fallthrough(_) | Terminator::If { .. } => {}
        }
        if block_has_exception_successors(self.cfg, block_id) {
            stmts.push(Stmt::Comment(
                "rustyflower: try/catch reconstruction is not implemented yet".to_string(),
            ));
        }
        StructuredStmt::Basic(stmts)
    }

    fn try_build_switch(
        &mut self,
        pos: usize,
        end_pos: usize,
        goto_handling: GotoHandling,
    ) -> Result<Option<(StructuredStmt, usize, Vec<usize>)>> {
        let block_id = self.cfg.order[pos];
        let Terminator::Switch {
            expr,
            default_target,
            cases,
        } = &self.semantics[block_id].terminator
        else {
            return Ok(None);
        };

        let mut labels_by_offset = std::collections::BTreeMap::<u16, (Vec<i32>, bool)>::new();
        for (value, offset) in cases {
            labels_by_offset
                .entry(*offset)
                .or_insert_with(|| (Vec::new(), false))
                .0
                .push(*value);
        }
        labels_by_offset
            .entry(*default_target)
            .or_insert_with(|| (Vec::new(), false))
            .1 = true;

        let mut arm_entries = Vec::new();
        for (offset, (labels, has_default)) in labels_by_offset {
            let start_pos = self.position_for_offset(offset)?;
            arm_entries.push((start_pos, offset, labels, has_default));
        }
        arm_entries.sort_by_key(|(start_pos, _, _, _)| *start_pos);
        if arm_entries.is_empty() {
            return Ok(None);
        }

        let merge_pos = self.find_switch_merge_pos(pos, end_pos, &arm_entries)?;
        let merge_offset = if merge_pos < self.cfg.order.len() {
            Some(self.cfg.blocks[self.cfg.order[merge_pos]].start_offset)
        } else {
            None
        };

        let mut arms = Vec::new();
        let mut consumed = vec![block_id];
        let mut previous_end = arm_entries[0].0;
        let mut synthetic_merge_arms: Vec<SwitchArm> = Vec::new();
        for (index, entry) in arm_entries.iter().enumerate() {
            let start_pos = entry.0;
            let mut labels = entry.2.clone();
            let has_default = entry.3;
            if start_pos >= merge_pos {
                labels.sort_unstable();
                synthetic_merge_arms.push(SwitchArm {
                    labels,
                    has_default,
                    body: Box::new(StructuredStmt::Basic(vec![Stmt::Break])),
                });
                continue;
            }
            let arm_end = arm_entries
                .get(index + 1)
                .map(|(next_pos, _, _, _)| *next_pos)
                .unwrap_or(merge_pos)
                .min(merge_pos);
            labels.sort_unstable();
            let body = wrap_sequence(self.build_range(
                start_pos,
                arm_end,
                match merge_offset {
                    Some(merge_offset) => GotoHandling::Break(merge_offset),
                    None => goto_handling,
                },
            )?);
            for region_pos in start_pos..arm_end {
                consumed.push(self.cfg.order[region_pos]);
            }
            previous_end = arm_end;
            arms.push(SwitchArm {
                labels,
                has_default,
                body: Box::new(body),
            });
        }

        if !synthetic_merge_arms.is_empty() {
            arms.extend(synthetic_merge_arms);
        }

        if arms.is_empty() {
            return Ok(None);
        }

        let next_pos = merge_pos.max(previous_end);
        let switch_stmt = StructuredStmt::Switch {
            expr: expr.clone(),
            arms,
        };
        if self.semantics[block_id].stmts.is_empty() {
            Ok(Some((switch_stmt, next_pos, consumed)))
        } else {
            Ok(Some((
                StructuredStmt::Sequence(vec![
                    StructuredStmt::Basic(self.semantics[block_id].stmts.clone()),
                    switch_stmt,
                ]),
                next_pos,
                consumed,
            )))
        }
    }

    fn try_build_while(
        &mut self,
        pos: usize,
        end_pos: usize,
        _goto_handling: GotoHandling,
    ) -> Result<Option<(StructuredStmt, usize, Vec<usize>)>> {
        let block_id = self.cfg.order[pos];
        let terminator = &self.semantics[block_id].terminator;
        let Terminator::If {
            condition,
            jump_target,
            fallthrough_target,
        } = terminator
        else {
            return Ok(None);
        };

        let next_pos = pos + 1;
        if next_pos >= end_pos {
            return Ok(None);
        }
        let next_offset = self.cfg.blocks[self.cfg.order[next_pos]].start_offset;

        let (body_start_pos, exit_pos, loop_condition) = if *fallthrough_target == next_offset {
            let exit_pos = self.position_for_offset(*jump_target)?;
            if exit_pos <= next_pos {
                return Ok(None);
            }
            (next_pos, exit_pos, negate_condition(condition.clone()))
        } else if *jump_target == next_offset {
            let exit_pos = self.position_for_offset(*fallthrough_target)?;
            if exit_pos <= next_pos {
                return Ok(None);
            }
            (next_pos, exit_pos, condition.clone())
        } else {
            return Ok(None);
        };

        let loop_header_offset = self.cfg.blocks[block_id].start_offset;
        let mut backedge_pos = None;
        for candidate_pos in body_start_pos..exit_pos {
            let candidate_id = self.cfg.order[candidate_pos];
            if matches!(
                self.semantics[candidate_id].terminator,
                Terminator::Goto(target) if target == loop_header_offset
            ) {
                backedge_pos = Some(candidate_pos);
            }
        }
        let Some(backedge_pos) = backedge_pos else {
            return Ok(None);
        };

        let body_stmts = self.build_range(
            body_start_pos,
            backedge_pos + 1,
            GotoHandling::Suppress(loop_header_offset),
        )?;
        let mut consumed = vec![block_id];
        for region_pos in body_start_pos..=backedge_pos {
            consumed.push(self.cfg.order[region_pos]);
        }
        Ok(Some((
            StructuredStmt::While {
                condition: loop_condition,
                body: Box::new(wrap_sequence(body_stmts)),
            },
            exit_pos,
            consumed,
        )))
    }

    fn try_build_if(
        &mut self,
        pos: usize,
        end_pos: usize,
        goto_handling: GotoHandling,
    ) -> Result<Option<(StructuredStmt, usize, Vec<usize>)>> {
        let block_id = self.cfg.order[pos];
        let terminator = &self.semantics[block_id].terminator;
        let Terminator::If {
            condition,
            jump_target,
            fallthrough_target,
        } = terminator
        else {
            return Ok(None);
        };

        let next_pos = pos + 1;
        if next_pos >= end_pos {
            return Ok(None);
        }
        let next_offset = self.cfg.blocks[self.cfg.order[next_pos]].start_offset;

        let (then_start_pos, split_pos, source_condition, else_is_jump_target) =
            if *fallthrough_target == next_offset {
                (
                    next_pos,
                    self.position_for_offset(*jump_target)?,
                    negate_condition(condition.clone()),
                    true,
                )
            } else if *jump_target == next_offset {
                (
                    next_pos,
                    self.position_for_offset(*fallthrough_target)?,
                    condition.clone(),
                    false,
                )
            } else {
                return Ok(None);
            };

        if split_pos <= then_start_pos || split_pos > end_pos {
            return Ok(None);
        }

        let before_split = split_pos.saturating_sub(1);
        let before_split_id = self.cfg.order[before_split];
        let else_goto = match &self.semantics[before_split_id].terminator {
            Terminator::Goto(target) => Some(*target),
            _ => None,
        };

        let (then_end_pos, else_branch, next_pos_after, consumed) =
            if let Some(merge_target) = else_goto {
                let merge_pos = self.position_for_offset(merge_target)?;
                if merge_pos <= split_pos {
                    return Ok(None);
                }
                let then_body = self.build_range(
                    then_start_pos,
                    split_pos,
                    GotoHandling::Suppress(merge_target),
                )?;
                let else_body = self.build_range(split_pos, merge_pos, goto_handling)?;
                let mut consumed = vec![block_id];
                for region_pos in then_start_pos..merge_pos {
                    consumed.push(self.cfg.order[region_pos]);
                }
                (
                    split_pos,
                    Some(wrap_sequence(if else_is_jump_target {
                        else_body
                    } else {
                        then_body.clone()
                    })),
                    merge_pos,
                    consumed,
                )
            } else {
                let then_body = self.build_range(then_start_pos, split_pos, goto_handling)?;
                let mut consumed = vec![block_id];
                for region_pos in then_start_pos..split_pos {
                    consumed.push(self.cfg.order[region_pos]);
                }
                let stmt = StructuredStmt::If {
                    condition: source_condition,
                    then_branch: Box::new(wrap_sequence(then_body)),
                    else_branch: None,
                };
                return Ok(Some((stmt, split_pos, consumed)));
            };

        let then_body = if else_is_jump_target {
            self.build_range(
                then_start_pos,
                then_end_pos,
                GotoHandling::Suppress(
                    self.cfg.blocks[self.cfg.order[next_pos_after]].start_offset,
                ),
            )
            .unwrap_or_default()
        } else {
            self.build_range(split_pos, next_pos_after, goto_handling)
                .unwrap_or_default()
        };
        let stmt = StructuredStmt::If {
            condition: source_condition,
            then_branch: Box::new(wrap_sequence(then_body)),
            else_branch: else_branch.map(Box::new),
        };
        Ok(Some((stmt, next_pos_after, consumed)))
    }

    fn position_for_offset(&self, offset: u16) -> Result<usize> {
        self.cfg
            .order
            .iter()
            .position(|block_id| self.cfg.blocks[*block_id].start_offset == offset)
            .ok_or_else(|| {
                DecompileError::Unsupported(format!("no block starts at offset {offset}"))
            })
    }

    fn find_switch_merge_pos(
        &self,
        _header_pos: usize,
        end_pos: usize,
        arm_entries: &[(usize, u16, Vec<i32>, bool)],
    ) -> Result<usize> {
        let arm_positions = arm_entries
            .iter()
            .map(|(start_pos, _, _, _)| *start_pos)
            .collect::<HashSet<_>>();
        let first_arm_pos = arm_entries
            .iter()
            .map(|(start_pos, _, _, _)| *start_pos)
            .min()
            .ok_or_else(|| DecompileError::Unsupported("switch has no arms".to_string()))?;
        let mut goto_target_positions = Vec::new();
        for pos in first_arm_pos..end_pos {
            let block_id = self.cfg.order[pos];
            if let Terminator::Goto(target) = self.semantics[block_id].terminator
                && let Some(block) = self.cfg.block_by_offset(target)
            {
                let target_pos = position_for_block(self.cfg, block.id);
                if target_pos > pos {
                    goto_target_positions.push(target_pos);
                }
            }
        }
        if let Some(merge_pos) = goto_target_positions
            .iter()
            .copied()
            .filter(|candidate| arm_positions.contains(candidate) && *candidate > first_arm_pos)
            .min()
        {
            return Ok(merge_pos);
        }

        let max_arm_pos = arm_entries
            .iter()
            .filter(|(_, _, labels, _)| !labels.is_empty())
            .map(|(start_pos, _, _, _)| *start_pos)
            .max()
            .or_else(|| {
                arm_entries
                    .iter()
                    .map(|(start_pos, _, _, _)| *start_pos)
                    .max()
            })
            .ok_or_else(|| DecompileError::Unsupported("switch has no arms".to_string()))?;

        let mut merge_candidates = Vec::new();
        for pos in arm_entries[0].0..end_pos {
            let block_id = self.cfg.order[pos];
            for successor_pos in successor_positions(self.cfg, &self.semantics[block_id]) {
                if successor_pos > max_arm_pos {
                    merge_candidates.push(successor_pos);
                }
            }
        }

        Ok(merge_candidates.into_iter().min().unwrap_or(end_pos))
    }
}

fn translate_blocks(
    class: &LoadedClass,
    method: &LoadedMethod,
    cfg: &ControlFlowGraph,
) -> Result<Vec<BlockSemantics>> {
    let mut temp_counter = 0;
    let mut semantics = Vec::with_capacity(cfg.blocks.len());
    for (position, block_id) in cfg.order.iter().copied().enumerate() {
        let next_offset = cfg
            .order
            .get(position + 1)
            .map(|next_id| cfg.blocks[*next_id].start_offset);
        semantics.push(translate_block(
            class,
            method,
            &cfg.blocks[block_id],
            next_offset,
            &mut temp_counter,
        )?);
    }
    Ok(semantics)
}

fn block_has_exception_successors(cfg: &ControlFlowGraph, block_id: usize) -> bool {
    cfg.blocks
        .get(block_id)
        .map(|block| !block.exception_successors.is_empty())
        .unwrap_or(false)
}

fn wrap_sequence(statements: Vec<StructuredStmt>) -> StructuredStmt {
    match statements.len() {
        0 => StructuredStmt::Empty,
        1 => statements
            .into_iter()
            .next()
            .unwrap_or(StructuredStmt::Empty),
        _ => StructuredStmt::Sequence(statements),
    }
}

fn successor_positions(cfg: &ControlFlowGraph, semantics: &BlockSemantics) -> Vec<usize> {
    let mut positions = Vec::new();
    match &semantics.terminator {
        Terminator::Fallthrough(Some(offset)) | Terminator::Goto(offset) => {
            if let Some(block) = cfg.block_by_offset(*offset) {
                positions.push(position_for_block(cfg, block.id));
            }
        }
        Terminator::If {
            jump_target,
            fallthrough_target,
            ..
        } => {
            if let Some(block) = cfg.block_by_offset(*jump_target) {
                positions.push(position_for_block(cfg, block.id));
            }
            if let Some(block) = cfg.block_by_offset(*fallthrough_target) {
                positions.push(position_for_block(cfg, block.id));
            }
        }
        Terminator::Switch {
            default_target,
            cases,
            ..
        } => {
            if let Some(block) = cfg.block_by_offset(*default_target) {
                positions.push(position_for_block(cfg, block.id));
            }
            for (_, target) in cases {
                if let Some(block) = cfg.block_by_offset(*target) {
                    positions.push(position_for_block(cfg, block.id));
                }
            }
        }
        Terminator::Return(_) | Terminator::Throw(_) | Terminator::Fallthrough(None) => {}
    }
    positions.sort_unstable();
    positions.dedup();
    positions
}

fn position_for_block(cfg: &ControlFlowGraph, block_id: usize) -> usize {
    cfg.order
        .iter()
        .position(|candidate| *candidate == block_id)
        .unwrap_or(cfg.order.len())
}
