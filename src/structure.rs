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
        None,
    )?))
}

struct Builder<'a> {
    class: &'a LoadedClass,
    method: &'a LoadedMethod,
    cfg: &'a ControlFlowGraph,
    semantics: &'a [BlockSemantics],
    visited: HashSet<usize>,
}

impl<'a> Builder<'a> {
    fn build_range(
        &mut self,
        start_pos: usize,
        end_pos: usize,
        suppress_goto_target: Option<u16>,
    ) -> Result<Vec<StructuredStmt>> {
        let mut statements = Vec::new();
        let mut pos = start_pos;
        while pos < end_pos {
            let block_id = self.cfg.order[pos];
            if self.visited.contains(&block_id) {
                pos += 1;
                continue;
            }
            if let Some((stmt, next_pos, consumed)) = self.try_build_while(pos, end_pos)? {
                self.visited.extend(consumed);
                statements.push(stmt);
                pos = next_pos;
                continue;
            }
            if let Some((stmt, next_pos, consumed)) = self.try_build_if(pos, end_pos)? {
                self.visited.extend(consumed);
                statements.push(stmt);
                pos = next_pos;
                continue;
            }

            self.visited.insert(block_id);
            statements.push(self.basic_statement(block_id, suppress_goto_target));
            pos += 1;
        }
        Ok(statements)
    }

    fn basic_statement(
        &self,
        block_id: usize,
        suppress_goto_target: Option<u16>,
    ) -> StructuredStmt {
        let mut stmts = self.semantics[block_id].stmts.clone();
        match &self.semantics[block_id].terminator {
            Terminator::Return(value) => stmts.push(Stmt::Return(value.clone())),
            Terminator::Throw(value) => stmts.push(Stmt::Throw(value.clone())),
            Terminator::Goto(target) => {
                if suppress_goto_target != Some(*target) {
                    stmts.push(Stmt::Comment(format!(
                        "rustyflower: unsupported goto to offset {target}"
                    )));
                }
            }
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

    fn try_build_while(
        &mut self,
        pos: usize,
        end_pos: usize,
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

        let body_stmts =
            self.build_range(body_start_pos, backedge_pos + 1, Some(loop_header_offset))?;
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
                let then_body = self.build_range(then_start_pos, split_pos, Some(merge_target))?;
                let else_body = self.build_range(split_pos, merge_pos, None)?;
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
                let then_body = self.build_range(then_start_pos, split_pos, None)?;
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
                Some(self.cfg.blocks[self.cfg.order[next_pos_after]].start_offset),
            )
            .unwrap_or_default()
        } else {
            self.build_range(split_pos, next_pos_after, None)
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
