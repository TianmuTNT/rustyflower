use crate::cfg::{ControlFlowGraph, build_cfg};
use crate::error::{DecompileError, Result};
use crate::expr::{
    BlockSemantics, Stmt, StructuredExpr, Terminator, negate_condition, translate_block,
};
use crate::loader::{LoadedClass, LoadedMethod};
use std::collections::HashSet;

#[derive(Debug, Clone, PartialEq)]
pub enum StructuredStmt {
    Sequence(Vec<StructuredStmt>),
    Basic(Vec<Stmt>),
    Try {
        try_body: Box<StructuredStmt>,
        catches: Vec<CatchArm>,
        finally_body: Option<Box<StructuredStmt>>,
    },
    Synchronized {
        expr: StructuredExpr,
        body: Box<StructuredStmt>,
    },
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

#[derive(Debug, Clone, PartialEq)]
pub struct SwitchArm {
    pub labels: Vec<SwitchLabel>,
    pub has_default: bool,
    pub body: Box<StructuredStmt>,
}

#[derive(Debug, Clone, PartialEq)]
pub struct CatchArm {
    pub catch_type: String,
    pub catch_var: String,
    pub body: Box<StructuredStmt>,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum SwitchLabel {
    Int(i32),
    String(String),
    Enum(String),
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
        suppressed_try_starts: HashSet::new(),
    };
    let root = StructuredStmt::Sequence(builder.build_range(
        0,
        cfg.blocks.len(),
        GotoHandling::Comment,
    )?);
    Ok(rewrite_synchronized_stmt(root))
}

struct Builder<'a> {
    class: &'a LoadedClass,
    method: &'a LoadedMethod,
    cfg: &'a ControlFlowGraph,
    semantics: &'a [BlockSemantics],
    visited: HashSet<usize>,
    suppressed_try_starts: HashSet<u16>,
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
            let block_start = self.cfg.blocks[block_id].start_offset;
            if self.visited.contains(&block_id) {
                pos += 1;
                continue;
            }
            if let Some((stmt, next_pos, consumed)) =
                self.try_build_synchronized(pos, end_pos, goto_handling)?
            {
                self.visited.extend(consumed);
                statements.push(stmt);
                pos = next_pos;
                continue;
            }
            if !self.suppressed_try_starts.contains(&block_start)
                && let Some((stmt, next_pos, consumed)) =
                    self.try_build_try_catch(pos, end_pos, goto_handling)?
            {
                self.visited.extend(consumed);
                statements.push(stmt);
                pos = next_pos;
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

    fn try_build_synchronized(
        &mut self,
        pos: usize,
        end_pos: usize,
        goto_handling: GotoHandling,
    ) -> Result<Option<(StructuredStmt, usize, Vec<usize>)>> {
        let next_pos = pos + 1;
        if next_pos >= end_pos {
            return Ok(None);
        }
        let prefix_block_id = self.cfg.order[pos];
        let prefix_stmts = &self.semantics[prefix_block_id].stmts;
        let Some((monitor_expr, prefix_consumed)) = extract_monitor_enter(prefix_stmts) else {
            return Ok(None);
        };

        let region_start_offset = self.cfg.blocks[self.cfg.order[next_pos]].start_offset;
        let mut catch_all_entries = self
            .method
            .exception_table
            .iter()
            .filter(|entry| entry.start_pc == region_start_offset && entry.catch_type == 0)
            .cloned()
            .collect::<Vec<_>>();
        if catch_all_entries.is_empty() {
            return Ok(None);
        }
        let end_pc = catch_all_entries[0].end_pc;
        catch_all_entries.retain(|entry| entry.end_pc == end_pc && entry.catch_type == 0);
        if catch_all_entries.is_empty() {
            return Ok(None);
        }
        let handler_pc = catch_all_entries[0].handler_pc;
        let try_end_pos = self.position_for_offset(end_pc)?;
        let handler_pos = self.position_for_offset(handler_pc)?;
        if handler_pos < try_end_pos {
            return Ok(None);
        }

        let merge_pos = self.find_try_catch_merge_pos(
            next_pos,
            try_end_pos,
            &[],
            Some((handler_pos, handler_pc)),
            end_pos,
        );
        let merge_offset = if merge_pos < self.cfg.order.len() {
            Some(self.cfg.blocks[self.cfg.order[merge_pos]].start_offset)
        } else {
            None
        };

        self.suppressed_try_starts.insert(region_start_offset);
        self.suppressed_try_starts
            .insert(self.cfg.blocks[self.cfg.order[handler_pos]].start_offset);
        let try_body = wrap_sequence(self.build_range(
            next_pos,
            try_end_pos,
            match merge_offset {
                Some(offset) => GotoHandling::Suppress(offset),
                None => goto_handling,
            },
        )?);
        let mut try_body = strip_try_comments(try_body);
        let handler_body = wrap_sequence(self.build_range(
            handler_pos,
            merge_pos,
            match merge_offset {
                Some(offset) => GotoHandling::Suppress(offset),
                None => goto_handling,
            },
        )?);
        let handler_body = strip_try_comments(handler_body);
        self.suppressed_try_starts
            .remove(&self.cfg.blocks[self.cfg.order[handler_pos]].start_offset);
        self.suppressed_try_starts.remove(&region_start_offset);

        let (canonical_finally, _slot) = extract_finally_from_handler(handler_body)?;
        if !is_monitor_only_finally(&canonical_finally) {
            return Ok(None);
        }
        let sync_body = strip_monitor_exit_suffix(try_body, &canonical_finally)
            .ok_or_else(|| {
                DecompileError::Unsupported(
                    "synchronized body does not match monitor exit pattern".to_string(),
                )
            })?;

        let mut items = Vec::new();
        let mut prefix_remaining = prefix_stmts.clone();
        prefix_remaining.truncate(prefix_remaining.len().saturating_sub(prefix_consumed));
        if !prefix_remaining.is_empty() {
            items.push(StructuredStmt::Basic(prefix_remaining));
        }
        items.push(StructuredStmt::Synchronized {
            expr: monitor_expr,
            body: Box::new(sync_body),
        });

        let consumed = (pos..merge_pos.min(self.cfg.order.len()))
            .map(|region_pos| self.cfg.order[region_pos])
            .collect::<Vec<_>>();
        Ok(Some((wrap_sequence(items), merge_pos, consumed)))
    }

    fn try_build_try_catch(
        &mut self,
        pos: usize,
        end_pos: usize,
        goto_handling: GotoHandling,
    ) -> Result<Option<(StructuredStmt, usize, Vec<usize>)>> {
        let start_offset = self.cfg.blocks[self.cfg.order[pos]].start_offset;
        let mut entries = self
            .method
            .exception_table
            .iter()
            .filter(|entry| entry.start_pc == start_offset)
            .cloned()
            .collect::<Vec<_>>();
        if entries.is_empty() {
            return Ok(None);
        }

        let end_pc = entries[0].end_pc;
        entries.retain(|entry| entry.end_pc == end_pc);
        if entries.is_empty() {
            return Ok(None);
        }

        let try_end_pos = self.position_for_offset(end_pc)?;
        if try_end_pos <= pos || try_end_pos > end_pos {
            return Ok(None);
        }
        if (pos..try_end_pos).any(|region_pos| self.visited.contains(&self.cfg.order[region_pos])) {
            return Ok(None);
        }

        let mut typed_handlers = Vec::new();
        let mut catch_all_handler = None;
        for entry in entries {
            let handler_pos = self.position_for_offset(entry.handler_pc)?;
            if handler_pos < try_end_pos {
                return Ok(None);
            }
            if entry.catch_type == 0 {
                catch_all_handler = Some((handler_pos, entry.handler_pc));
            } else {
                let catch_type =
                    crate::bytecode::cp_class_name(&self.class.constant_pool, entry.catch_type)
                        .map(str::to_string)
                        .map_err(|_| DecompileError::Unsupported("invalid catch type".to_string()))?;
                typed_handlers.push((handler_pos, catch_type));
            }
        }
        typed_handlers.sort_by_key(|(handler_pos, _)| *handler_pos);
        typed_handlers.dedup_by_key(|(handler_pos, _)| *handler_pos);

        let merge_pos =
            self.find_try_catch_merge_pos(pos, try_end_pos, &typed_handlers, catch_all_handler, end_pos);
        let merge_offset = if merge_pos < self.cfg.order.len() {
            Some(self.cfg.blocks[self.cfg.order[merge_pos]].start_offset)
        } else {
            None
        };
        let catch_all_end = catch_all_handler
            .map(|(handler_pos, _)| self.catch_all_handler_end_pos(handler_pos, end_pos))
            .unwrap_or(merge_pos);

        self.suppressed_try_starts.insert(start_offset);
        let mut try_body = wrap_sequence(self.build_range(
            pos,
            try_end_pos,
            match merge_offset {
                Some(offset) => GotoHandling::Suppress(offset),
                None => goto_handling,
            },
        )?);
        let mut try_body = strip_try_comments(try_body);

        let mut catches = Vec::new();
        let mut consumed = (pos..merge_pos.min(self.cfg.order.len()))
            .map(|region_pos| self.cfg.order[region_pos])
            .collect::<Vec<_>>();

        let first_handler_pos = typed_handlers
            .first()
            .map(|(handler_pos, _)| *handler_pos)
            .or_else(|| catch_all_handler.map(|(handler_pos, _)| handler_pos))
            .unwrap_or(merge_pos);

        let mut finally_body = None;
        if let Some((catch_all_pos, _handler_pc)) = catch_all_handler {
            let catch_all_start_offset = self.cfg.blocks[self.cfg.order[catch_all_pos]].start_offset;
            self.suppressed_try_starts.insert(catch_all_start_offset);
            let canonical_handler_body = wrap_sequence(self.build_range(
                catch_all_pos,
                catch_all_end,
                match merge_offset {
                    Some(offset) => GotoHandling::Suppress(offset),
                    None => goto_handling,
                },
            )?);
            let canonical_handler_body = strip_try_comments(canonical_handler_body);
            let (canonical_finally, catch_var_slot) =
                extract_finally_from_handler(canonical_handler_body)?;

            let mut rendered_finally = canonical_finally.clone();
            if try_end_pos < first_handler_pos {
                let normal_tail = wrap_sequence(self.build_range(
                    try_end_pos,
                    first_handler_pos,
                    match merge_offset {
                        Some(offset) => GotoHandling::Suppress(offset),
                        None => goto_handling,
                    },
                )?);
                let normal_tail = strip_try_comments(normal_tail);
                if let Some(stripped) =
                    remove_duplicate_finally(self.method, normal_tail.clone(), &canonical_finally)
                {
                    if !matches!(stripped, StructuredStmt::Empty) {
                        let mut items = top_level_items(try_body);
                        items.extend(top_level_items(stripped));
                        try_body = wrap_sequence(items);
                    } else if top_level_items(normal_tail.clone()).len()
                        == top_level_items(canonical_finally.clone()).len()
                    {
                        rendered_finally = normal_tail;
                    }
                } else if !is_monitor_only_finally(&canonical_finally) {
                    return Ok(None);
                }
            }

            for (index, (handler_pos, catch_type)) in typed_handlers.iter().enumerate() {
                let catch_end = typed_handlers
                    .get(index + 1)
                    .map(|(next_pos, _)| *next_pos)
                    .unwrap_or(catch_all_pos)
                    .min(catch_all_pos);
                let catch_body = wrap_sequence(self.build_range(
                    *handler_pos,
                    catch_end,
                    match merge_offset {
                        Some(offset) => GotoHandling::Suppress(offset),
                        None => goto_handling,
                    },
                )?);
                let catch_body = strip_try_comments(catch_body);
                let (catch_var, catch_body) =
                    extract_catch_binding(self.method, catch_body, catch_type);
                let catch_body = remove_duplicate_finally(self.method, catch_body, &canonical_finally)
                    .ok_or_else(|| {
                        DecompileError::Unsupported(
                            "catch body does not match canonical finally".to_string(),
                        )
                    })?;
                catches.push(CatchArm {
                    catch_type: catch_type.clone(),
                    catch_var,
                    body: Box::new(catch_body),
                });
            }

            let synchronized =
                try_rewrite_synchronized(self.method, &try_body, &rendered_finally, catch_var_slot);
            finally_body = Some(Box::new(rendered_finally));

            self.suppressed_try_starts.remove(&catch_all_start_offset);
            self.suppressed_try_starts.remove(&start_offset);
            let try_stmt = if let Some((monitor_expr, sync_body)) = synchronized {
                StructuredStmt::Synchronized {
                    expr: monitor_expr,
                    body: Box::new(sync_body),
                }
            } else {
                StructuredStmt::Try {
                    try_body: Box::new(try_body),
                    catches,
                    finally_body,
                }
            };

            return Ok(Some((try_stmt, merge_pos, consumed)));
        }

        for (index, (handler_pos, catch_type)) in typed_handlers.iter().enumerate() {
            let catch_end = typed_handlers
                .get(index + 1)
                .map(|(next_pos, _)| *next_pos)
                .unwrap_or(merge_pos)
                .min(merge_pos);
            let catch_body = wrap_sequence(self.build_range(
                *handler_pos,
                catch_end,
                match merge_offset {
                    Some(offset) => GotoHandling::Suppress(offset),
                    None => goto_handling,
                },
            )?);
            let catch_body = strip_try_comments(catch_body);
            let (catch_var, catch_body) =
                extract_catch_binding(self.method, catch_body, catch_type);
            catches.push(CatchArm {
                catch_type: catch_type.clone(),
                catch_var,
                body: Box::new(catch_body),
            });
        }
        self.suppressed_try_starts.remove(&start_offset);

        if catches.is_empty() {
            return Ok(None);
        }

        Ok(Some((
            StructuredStmt::Try {
                try_body: Box::new(try_body),
                catches,
                finally_body: None,
            },
            merge_pos,
            consumed,
        )))
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
                    labels: labels.into_iter().map(SwitchLabel::Int).collect(),
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
                labels: labels.into_iter().map(SwitchLabel::Int).collect(),
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

    fn find_try_catch_merge_pos(
        &self,
        try_start_pos: usize,
        try_end_pos: usize,
        handlers: &[(usize, String)],
        catch_all_handler: Option<(usize, u16)>,
        end_pos: usize,
    ) -> usize {
        let last_handler_pos = handlers
            .iter()
            .map(|(handler_pos, _)| *handler_pos)
            .max()
            .max(catch_all_handler.map(|(handler_pos, _)| handler_pos))
            .unwrap_or(try_end_pos);
        let mut candidates = Vec::new();

        for pos in try_start_pos..end_pos {
            let block_id = self.cfg.order[pos];
            let block = &self.cfg.blocks[block_id];
            let successors = successor_positions(self.cfg, &self.semantics[block_id]);
            for successor in successors {
                if successor > last_handler_pos {
                    candidates.push(successor);
                }
            }
            if pos >= last_handler_pos
                && block.successors.is_empty()
                && block.exception_successors.is_empty()
            {
                candidates.push(pos + 1);
            }
        }

        candidates.into_iter().min().unwrap_or(end_pos)
    }

    fn catch_all_handler_end_pos(&self, handler_pos: usize, end_pos: usize) -> usize {
        let mut pos = handler_pos;
        while pos + 1 < end_pos {
            let next = pos + 1;
            if !matches!(
                self.semantics[self.cfg.order[pos]].terminator,
                Terminator::Fallthrough(Some(offset))
                    if self.cfg.blocks[self.cfg.order[next]].start_offset == offset
            ) {
                break;
            }
            pos = next;
        }
        pos + 1
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

fn rewrite_synchronized_stmt(stmt: StructuredStmt) -> StructuredStmt {
    match stmt {
        StructuredStmt::Sequence(items) => rewrite_synchronized_sequence(items),
        StructuredStmt::Try {
            try_body,
            catches,
            finally_body,
        } => StructuredStmt::Try {
            try_body: Box::new(rewrite_synchronized_stmt(*try_body)),
            catches: catches
                .into_iter()
                .map(|catch| CatchArm {
                    catch_type: catch.catch_type,
                    catch_var: catch.catch_var,
                    body: Box::new(rewrite_synchronized_stmt(*catch.body)),
                })
                .collect(),
            finally_body: finally_body.map(|body| Box::new(rewrite_synchronized_stmt(*body))),
        },
        StructuredStmt::Switch { expr, arms } => StructuredStmt::Switch {
            expr,
            arms: arms
                .into_iter()
                .map(|arm| SwitchArm {
                    labels: arm.labels,
                    has_default: arm.has_default,
                    body: Box::new(rewrite_synchronized_stmt(*arm.body)),
                })
                .collect(),
        },
        StructuredStmt::If {
            condition,
            then_branch,
            else_branch,
        } => StructuredStmt::If {
            condition,
            then_branch: Box::new(rewrite_synchronized_stmt(*then_branch)),
            else_branch: else_branch.map(|branch| Box::new(rewrite_synchronized_stmt(*branch))),
        },
        StructuredStmt::While { condition, body } => StructuredStmt::While {
            condition,
            body: Box::new(rewrite_synchronized_stmt(*body)),
        },
        other => other,
    }
}

fn rewrite_synchronized_sequence(items: Vec<StructuredStmt>) -> StructuredStmt {
    let mut rewritten = items
        .into_iter()
        .map(rewrite_synchronized_stmt)
        .flat_map(top_level_items)
        .collect::<Vec<_>>();
    let mut output = Vec::new();
    let mut index = 0;
    while index < rewritten.len() {
        if let Some((stmt, consumed)) = try_fold_synchronized_pair(&rewritten[index..]) {
            output.push(stmt);
            index += consumed;
            continue;
        }
        output.push(rewritten[index].clone());
        index += 1;
    }
    wrap_sequence(output)
}

fn try_fold_synchronized_pair(items: &[StructuredStmt]) -> Option<(StructuredStmt, usize)> {
    if items.len() < 2 {
        return None;
    }
    let StructuredStmt::Basic(prefix_stmts) = &items[0] else {
        return None;
    };
    let StructuredStmt::Try {
        try_body,
        catches,
        finally_body: Some(finally_body),
    } = &items[1]
    else {
        return None;
    };
    if !catches.is_empty() {
        return None;
    }

    let (monitor_expr, prefix_consumed) = extract_monitor_enter(prefix_stmts)?;
    let stripped_try_body = strip_monitor_exit_suffix(*try_body.clone(), finally_body)?;

    let mut seq_items = Vec::new();
    let mut prefix_remaining = prefix_stmts.clone();
    prefix_remaining.truncate(prefix_remaining.len().saturating_sub(prefix_consumed));
    if !prefix_remaining.is_empty() {
        seq_items.push(StructuredStmt::Basic(prefix_remaining));
    }
    seq_items.push(StructuredStmt::Synchronized {
        expr: monitor_expr,
        body: Box::new(stripped_try_body),
    });
    Some((wrap_sequence(seq_items), 2))
}

fn extract_monitor_enter(stmts: &[Stmt]) -> Option<(StructuredExpr, usize)> {
    match stmts {
        [.., Stmt::Assign {
            target: StructuredExpr::Var(_slot),
            value,
        }, Stmt::MonitorEnter(expr)] if expr == value => Some((value.clone(), 2)),
        [.., Stmt::Assign {
            target: StructuredExpr::Var(_slot),
            value,
        }, Stmt::MonitorEnter(_expr)] => Some((value.clone(), 2)),
        [.., Stmt::MonitorEnter(expr)] => Some((expr.clone(), 1)),
        _ => None,
    }
}

fn strip_monitor_exit_suffix(body: StructuredStmt, finally_body: &StructuredStmt) -> Option<StructuredStmt> {
    let finally_items = top_level_items(finally_body.clone());
    if finally_items.len() != 1 {
        return None;
    }
    let StructuredStmt::Basic(finally_stmts) = &finally_items[0] else {
        return None;
    };
    if finally_stmts.len() != 1 {
        return None;
    }
    if !matches!(finally_stmts[0], Stmt::MonitorExit(_)) {
        return None;
    }

    let mut items = top_level_items(body);
    let last = items.pop()?;
    match last {
        StructuredStmt::Basic(mut stmts) => {
            if !matches!(stmts.last(), Some(Stmt::MonitorExit(_))) {
                return None;
            }
            stmts.pop();
            if !stmts.is_empty() {
                items.push(StructuredStmt::Basic(stmts));
            }
            Some(wrap_sequence(items))
        }
        _ => None,
    }
}

fn top_level_items(stmt: StructuredStmt) -> Vec<StructuredStmt> {
    match stmt {
        StructuredStmt::Sequence(items) => items
            .into_iter()
            .filter(|item| !matches!(item, StructuredStmt::Empty))
            .collect(),
        other => vec![other],
    }
}

fn extract_finally_from_handler(
    stmt: StructuredStmt,
) -> Result<(StructuredStmt, Option<u16>)> {
    let (slot, without_binding) = extract_catch_binding_slot(stmt);
    let without_throw = strip_terminal_rethrow(without_binding.clone(), slot).ok_or_else(|| {
        DecompileError::Unsupported(format!(
            "catch-all handler is not a canonical finally: {without_binding:?}"
        ))
    })?;
    Ok((without_throw, slot))
}

fn extract_catch_binding_slot(stmt: StructuredStmt) -> (Option<u16>, StructuredStmt) {
    match stmt {
        StructuredStmt::Basic(mut stmts) => {
            if let Some(Stmt::Assign {
                target: StructuredExpr::Var(slot),
                value: StructuredExpr::CaughtException(_),
            }) = stmts.first()
            {
                let slot = *slot;
                stmts.remove(0);
                let body = if stmts.is_empty() {
                    StructuredStmt::Empty
                } else {
                    StructuredStmt::Basic(stmts)
                };
                return (Some(slot), body);
            }
            (None, StructuredStmt::Basic(stmts))
        }
        StructuredStmt::Sequence(mut items) => {
            while matches!(items.first(), Some(StructuredStmt::Empty)) {
                items.remove(0);
            }
            if let Some(first) = items.first_mut() {
                let (slot, rewritten) = extract_catch_binding_slot(first.clone());
                *first = rewritten;
                return (slot, wrap_sequence(items));
            }
            (None, StructuredStmt::Sequence(Vec::new()))
        }
        other => (None, other),
    }
}

fn strip_terminal_rethrow(stmt: StructuredStmt, slot: Option<u16>) -> Option<StructuredStmt> {
    match stmt {
        StructuredStmt::Basic(mut stmts) => {
            let should_strip = matches!(
                stmts.last(),
                Some(Stmt::Throw(StructuredExpr::Var(value_slot))) if slot == Some(*value_slot)
            ) || matches!(stmts.last(), Some(Stmt::Throw(StructuredExpr::CaughtException(_))));
            if !should_strip {
                return None;
            }
            stmts.pop();
            Some(if stmts.is_empty() {
                StructuredStmt::Empty
            } else {
                StructuredStmt::Basic(stmts)
            })
        }
        StructuredStmt::Sequence(mut items) => {
            while matches!(items.last(), Some(StructuredStmt::Empty)) {
                items.pop();
            }
            let last = items.pop()?;
            let stripped = strip_terminal_rethrow(last, slot)?;
            if !matches!(stripped, StructuredStmt::Empty) {
                items.push(stripped);
            }
            Some(wrap_sequence(items))
        }
        _ => None,
    }
}

fn remove_duplicate_finally(
    method: &LoadedMethod,
    body: StructuredStmt,
    finally_body: &StructuredStmt,
) -> Option<StructuredStmt> {
    if let (StructuredStmt::Basic(body_stmts), StructuredStmt::Basic(finally_stmts)) =
        (&body, finally_body)
    {
        let stripped = remove_stmt_subsequence(method, body_stmts, finally_stmts)?;
        return Some(if stripped.is_empty() {
            StructuredStmt::Empty
        } else {
            StructuredStmt::Basic(stripped)
        });
    }
    let body_items = top_level_items(body);
    let finally_items = top_level_items(finally_body.clone());
    if finally_items.is_empty() {
        return Some(wrap_sequence(body_items));
    }
    if body_items.len() < finally_items.len() {
        return None;
    }
    for start in (0..=body_items.len() - finally_items.len()).rev() {
        if statement_slice_equivalent(
            method,
            &body_items[start..start + finally_items.len()],
            &finally_items,
        ) {
            let mut stripped = body_items.clone();
            stripped.drain(start..start + finally_items.len());
            return Some(wrap_sequence(stripped));
        }
    }
    None
}

fn remove_stmt_subsequence(
    method: &LoadedMethod,
    body: &[Stmt],
    finally_body: &[Stmt],
) -> Option<Vec<Stmt>> {
    if finally_body.is_empty() {
        return Some(body.to_vec());
    }
    if body.len() < finally_body.len() {
        return None;
    }
    for start in (0..=body.len() - finally_body.len()).rev() {
        let mut slot_map = std::collections::HashMap::new();
        let mut reverse_slot_map = std::collections::HashMap::new();
        let mut temp_map = std::collections::HashMap::new();
        let mut reverse_temp_map = std::collections::HashMap::new();
        let matched = body[start..start + finally_body.len()]
            .iter()
            .zip(finally_body.iter())
            .all(|(left, right)| {
                stmt_item_equivalent(
                    method,
                    left,
                    right,
                    &mut slot_map,
                    &mut reverse_slot_map,
                    &mut temp_map,
                    &mut reverse_temp_map,
                )
            });
        if matched {
            let mut stripped = body.to_vec();
            stripped.drain(start..start + finally_body.len());
            return Some(stripped);
        }
    }
    None
}

fn is_monitor_only_finally(finally_body: &StructuredStmt) -> bool {
    let items = top_level_items(finally_body.clone());
    items.len() == 1
        && matches!(
            &items[0],
            StructuredStmt::Basic(stmts)
                if stmts.len() == 1 && matches!(stmts[0], Stmt::MonitorExit(_))
        )
}

fn statement_slice_equivalent(
    method: &LoadedMethod,
    left: &[StructuredStmt],
    right: &[StructuredStmt],
) -> bool {
    if left.len() != right.len() {
        return false;
    }
    let mut slot_map = std::collections::HashMap::new();
    let mut reverse_slot_map = std::collections::HashMap::new();
    let mut temp_map = std::collections::HashMap::new();
    let mut reverse_temp_map = std::collections::HashMap::new();
    left.iter().zip(right.iter()).all(|(left, right)| {
        stmt_equivalent(
            method,
            left,
            right,
            &mut slot_map,
            &mut reverse_slot_map,
            &mut temp_map,
            &mut reverse_temp_map,
        )
    })
}

fn stmt_equivalent(
    method: &LoadedMethod,
    left: &StructuredStmt,
    right: &StructuredStmt,
    slot_map: &mut std::collections::HashMap<u16, u16>,
    reverse_slot_map: &mut std::collections::HashMap<u16, u16>,
    temp_map: &mut std::collections::HashMap<u32, u32>,
    reverse_temp_map: &mut std::collections::HashMap<u32, u32>,
) -> bool {
    match (left, right) {
        (StructuredStmt::Empty, StructuredStmt::Empty) => true,
        (StructuredStmt::Basic(left), StructuredStmt::Basic(right)) => {
            if left.len() != right.len() {
                return false;
            }
            left.iter().zip(right.iter()).all(|(left, right)| {
                stmt_item_equivalent(
                    method,
                    left,
                    right,
                    slot_map,
                    reverse_slot_map,
                    temp_map,
                    reverse_temp_map,
                )
            })
        }
        (StructuredStmt::Sequence(left), StructuredStmt::Sequence(right)) => {
            statement_slice_equivalent(method, left, right)
        }
        (
            StructuredStmt::If {
                condition: left_condition,
                then_branch: left_then,
                else_branch: left_else,
            },
            StructuredStmt::If {
                condition: right_condition,
                then_branch: right_then,
                else_branch: right_else,
            },
        ) => {
            expr_equivalent(
                method,
                left_condition,
                right_condition,
                slot_map,
                reverse_slot_map,
                temp_map,
                reverse_temp_map,
            ) && stmt_equivalent(
                method,
                left_then,
                right_then,
                slot_map,
                reverse_slot_map,
                temp_map,
                reverse_temp_map,
            ) && match (left_else, right_else) {
                (None, None) => true,
                (Some(left), Some(right)) => stmt_equivalent(
                    method,
                    left,
                    right,
                    slot_map,
                    reverse_slot_map,
                    temp_map,
                    reverse_temp_map,
                ),
                _ => false,
            }
        }
        (
            StructuredStmt::While {
                condition: left_condition,
                body: left_body,
            },
            StructuredStmt::While {
                condition: right_condition,
                body: right_body,
            },
        ) => {
            expr_equivalent(
                method,
                left_condition,
                right_condition,
                slot_map,
                reverse_slot_map,
                temp_map,
                reverse_temp_map,
            ) && stmt_equivalent(
                method,
                left_body,
                right_body,
                slot_map,
                reverse_slot_map,
                temp_map,
                reverse_temp_map,
            )
        }
        (StructuredStmt::Comment(left), StructuredStmt::Comment(right)) => left == right,
        _ => false,
    }
}

fn stmt_item_equivalent(
    method: &LoadedMethod,
    left: &Stmt,
    right: &Stmt,
    slot_map: &mut std::collections::HashMap<u16, u16>,
    reverse_slot_map: &mut std::collections::HashMap<u16, u16>,
    temp_map: &mut std::collections::HashMap<u32, u32>,
    reverse_temp_map: &mut std::collections::HashMap<u32, u32>,
) -> bool {
    match (left, right) {
        (
            Stmt::Assign {
                target: left_target,
                value: left_value,
            },
            Stmt::Assign {
                target: right_target,
                value: right_value,
            },
        ) => {
            expr_equivalent(
                method,
                left_target,
                right_target,
                slot_map,
                reverse_slot_map,
                temp_map,
                reverse_temp_map,
            ) && expr_equivalent(
                method,
                left_value,
                right_value,
                slot_map,
                reverse_slot_map,
                temp_map,
                reverse_temp_map,
            )
        }
        (
            Stmt::TempAssign {
                id: left_id,
                ty: left_ty,
                value: left_value,
            },
            Stmt::TempAssign {
                id: right_id,
                ty: right_ty,
                value: right_value,
            },
        ) => {
            left_ty == right_ty
                && map_temp(left_id, right_id, temp_map, reverse_temp_map)
                && expr_equivalent(
                    method,
                    left_value,
                    right_value,
                    slot_map,
                    reverse_slot_map,
                    temp_map,
                    reverse_temp_map,
                )
        }
        (Stmt::Expr(left), Stmt::Expr(right))
        | (Stmt::Throw(left), Stmt::Throw(right))
        | (Stmt::MonitorEnter(left), Stmt::MonitorEnter(right))
        | (Stmt::MonitorExit(left), Stmt::MonitorExit(right)) => expr_equivalent(
            method,
            left,
            right,
            slot_map,
            reverse_slot_map,
            temp_map,
            reverse_temp_map,
        ),
        (Stmt::Break, Stmt::Break) => true,
        (Stmt::Return(left), Stmt::Return(right)) => match (left, right) {
            (None, None) => true,
            (Some(left), Some(right)) => expr_equivalent(
                method,
                left,
                right,
                slot_map,
                reverse_slot_map,
                temp_map,
                reverse_temp_map,
            ),
            _ => false,
        },
        (
            Stmt::ConstructorCall {
                is_super: left_super,
                args: left_args,
            },
            Stmt::ConstructorCall {
                is_super: right_super,
                args: right_args,
            },
        ) => {
            left_super == right_super
                && left_args.len() == right_args.len()
                && left_args.iter().zip(right_args.iter()).all(|(left, right)| {
                    expr_equivalent(
                        method,
                        left,
                        right,
                        slot_map,
                        reverse_slot_map,
                        temp_map,
                        reverse_temp_map,
                    )
                })
        }
        (Stmt::Comment(left), Stmt::Comment(right)) => left == right,
        _ => false,
    }
}

fn expr_equivalent(
    method: &LoadedMethod,
    left: &StructuredExpr,
    right: &StructuredExpr,
    slot_map: &mut std::collections::HashMap<u16, u16>,
    reverse_slot_map: &mut std::collections::HashMap<u16, u16>,
    temp_map: &mut std::collections::HashMap<u32, u32>,
    reverse_temp_map: &mut std::collections::HashMap<u32, u32>,
) -> bool {
    match (left, right) {
        (StructuredExpr::This, StructuredExpr::This) => true,
        (StructuredExpr::Var(left), StructuredExpr::Var(right)) => {
            map_slot(method, *left, *right, slot_map, reverse_slot_map)
        }
        (StructuredExpr::Temp(left), StructuredExpr::Temp(right)) => {
            map_temp(left, right, temp_map, reverse_temp_map)
        }
        (StructuredExpr::CaughtException(_), StructuredExpr::CaughtException(_)) => true,
        (StructuredExpr::Literal(left), StructuredExpr::Literal(right)) => left == right,
        (
            StructuredExpr::Field {
                target: left_target,
                owner: left_owner,
                name: left_name,
                descriptor: left_descriptor,
                is_static: left_static,
            },
            StructuredExpr::Field {
                target: right_target,
                owner: right_owner,
                name: right_name,
                descriptor: right_descriptor,
                is_static: right_static,
            },
        ) => {
            left_owner == right_owner
                && left_name == right_name
                && left_descriptor == right_descriptor
                && left_static == right_static
                && match (left_target, right_target) {
                    (None, None) => true,
                    (Some(left), Some(right)) => expr_equivalent(
                        method,
                        left,
                        right,
                        slot_map,
                        reverse_slot_map,
                        temp_map,
                        reverse_temp_map,
                    ),
                    _ => false,
                }
        }
        (
            StructuredExpr::ArrayAccess {
                array: left_array,
                index: left_index,
            },
            StructuredExpr::ArrayAccess {
                array: right_array,
                index: right_index,
            },
        ) => {
            expr_equivalent(
                method,
                left_array,
                right_array,
                slot_map,
                reverse_slot_map,
                temp_map,
                reverse_temp_map,
            ) && expr_equivalent(
                method,
                left_index,
                right_index,
                slot_map,
                reverse_slot_map,
                temp_map,
                reverse_temp_map,
            )
        }
        (StructuredExpr::ArrayLength(left), StructuredExpr::ArrayLength(right)) => expr_equivalent(
            method,
            left,
            right,
            slot_map,
            reverse_slot_map,
            temp_map,
            reverse_temp_map,
        ),
        (
            StructuredExpr::Binary {
                op: left_op,
                left: left_left,
                right: left_right,
            },
            StructuredExpr::Binary {
                op: right_op,
                left: right_left,
                right: right_right,
            },
        ) => {
            left_op == right_op
                && expr_equivalent(
                    method,
                    left_left,
                    right_left,
                    slot_map,
                    reverse_slot_map,
                    temp_map,
                    reverse_temp_map,
                )
                && expr_equivalent(
                    method,
                    left_right,
                    right_right,
                    slot_map,
                    reverse_slot_map,
                    temp_map,
                    reverse_temp_map,
                )
        }
        (
            StructuredExpr::Unary {
                op: left_op,
                expr: left_expr,
            },
            StructuredExpr::Unary {
                op: right_op,
                expr: right_expr,
            },
        ) => {
            left_op == right_op
                && expr_equivalent(
                    method,
                    left_expr,
                    right_expr,
                    slot_map,
                    reverse_slot_map,
                    temp_map,
                    reverse_temp_map,
                )
        }
        (
            StructuredExpr::Call {
                receiver: left_receiver,
                owner: left_owner,
                name: left_name,
                descriptor: left_descriptor,
                args: left_args,
                is_static: left_static,
            },
            StructuredExpr::Call {
                receiver: right_receiver,
                owner: right_owner,
                name: right_name,
                descriptor: right_descriptor,
                args: right_args,
                is_static: right_static,
            },
        ) => {
            left_owner == right_owner
                && left_name == right_name
                && left_descriptor == right_descriptor
                && left_static == right_static
                && left_args.len() == right_args.len()
                && match (left_receiver, right_receiver) {
                    (None, None) => true,
                    (Some(left), Some(right)) => expr_equivalent(
                        method,
                        left,
                        right,
                        slot_map,
                        reverse_slot_map,
                        temp_map,
                        reverse_temp_map,
                    ),
                    _ => false,
                }
                && left_args.iter().zip(right_args.iter()).all(|(left, right)| {
                    expr_equivalent(
                        method,
                        left,
                        right,
                        slot_map,
                        reverse_slot_map,
                        temp_map,
                        reverse_temp_map,
                    )
                })
        }
        (
            StructuredExpr::New {
                class_name: left_class,
                args: left_args,
            },
            StructuredExpr::New {
                class_name: right_class,
                args: right_args,
            },
        ) => {
            left_class == right_class
                && left_args.len() == right_args.len()
                && left_args.iter().zip(right_args.iter()).all(|(left, right)| {
                    expr_equivalent(
                        method,
                        left,
                        right,
                        slot_map,
                        reverse_slot_map,
                        temp_map,
                        reverse_temp_map,
                    )
                })
        }
        (
            StructuredExpr::NewArray {
                element_type: left_type,
                size: left_size,
            },
            StructuredExpr::NewArray {
                element_type: right_type,
                size: right_size,
            },
        ) => {
            left_type == right_type
                && expr_equivalent(
                    method,
                    left_size,
                    right_size,
                    slot_map,
                    reverse_slot_map,
                    temp_map,
                    reverse_temp_map,
                )
        }
        (
            StructuredExpr::Cast {
                ty: left_ty,
                expr: left_expr,
            },
            StructuredExpr::Cast {
                ty: right_ty,
                expr: right_expr,
            },
        ) => {
            left_ty == right_ty
                && expr_equivalent(
                    method,
                    left_expr,
                    right_expr,
                    slot_map,
                    reverse_slot_map,
                    temp_map,
                    reverse_temp_map,
                )
        }
        (
            StructuredExpr::InstanceOf {
                expr: left_expr,
                ty: left_ty,
            },
            StructuredExpr::InstanceOf {
                expr: right_expr,
                ty: right_ty,
            },
        ) => {
            left_ty == right_ty
                && expr_equivalent(
                    method,
                    left_expr,
                    right_expr,
                    slot_map,
                    reverse_slot_map,
                    temp_map,
                    reverse_temp_map,
                )
        }
        _ => false,
    }
}

fn map_slot(
    method: &LoadedMethod,
    left: u16,
    right: u16,
    slot_map: &mut std::collections::HashMap<u16, u16>,
    reverse_slot_map: &mut std::collections::HashMap<u16, u16>,
) -> bool {
    let is_stable_left = stable_slot(method, left);
    let is_stable_right = stable_slot(method, right);
    if is_stable_left || is_stable_right {
        return left == right;
    }
    match slot_map.get(&left) {
        Some(mapped) => *mapped == right,
        None => {
            if reverse_slot_map.insert(right, left).is_some() {
                return false;
            }
            slot_map.insert(left, right);
            true
        }
    }
}

fn map_temp(
    left: &u32,
    right: &u32,
    temp_map: &mut std::collections::HashMap<u32, u32>,
    reverse_temp_map: &mut std::collections::HashMap<u32, u32>,
) -> bool {
    match temp_map.get(left) {
        Some(mapped) => *mapped == *right,
        None => {
            if reverse_temp_map.insert(*right, *left).is_some() {
                return false;
            }
            temp_map.insert(*left, *right);
            true
        }
    }
}

fn stable_slot(method: &LoadedMethod, slot: u16) -> bool {
    (!method.is_static() && slot == 0)
        || method.parameters.iter().any(|parameter| parameter.slot == slot)
}

fn try_rewrite_synchronized(
    _method: &LoadedMethod,
    try_body: &StructuredStmt,
    finally_body: &StructuredStmt,
    _catch_slot: Option<u16>,
) -> Option<(StructuredExpr, StructuredStmt)> {
    let try_items = top_level_items(try_body.clone());
    let first = try_items.first()?;
    let StructuredStmt::Basic(first_stmts) = first else {
        return None;
    };

    let (monitor_expr, consumed_from_first) = match first_stmts.as_slice() {
        [Stmt::Assign {
            target: StructuredExpr::Var(_slot),
            value,
        }, Stmt::MonitorEnter(expr), ..] if expr == value => (value.clone(), 2),
        [Stmt::Assign {
            target: StructuredExpr::Var(_slot),
            value,
        }, Stmt::MonitorEnter(_), ..] => (value.clone(), 2),
        [Stmt::MonitorEnter(expr), ..] => (expr.clone(), 1),
        _ => return None,
    };

    let finally_items = top_level_items(finally_body.clone());
    if finally_items.len() != 1 {
        return None;
    }
    let StructuredStmt::Basic(finally_stmts) = &finally_items[0] else {
        return None;
    };
    if finally_stmts.len() != 1 {
        return None;
    }
    if !matches!(&finally_stmts[0], Stmt::MonitorExit(_)) {
        return None;
    }

    let mut body_items = try_items;
    let StructuredStmt::Basic(mut first_stmts_owned) = body_items.remove(0) else {
        return None;
    };
    first_stmts_owned.drain(0..consumed_from_first);
    if !first_stmts_owned.is_empty() {
        body_items.insert(0, StructuredStmt::Basic(first_stmts_owned));
    }
    Some((monitor_expr, wrap_sequence(body_items)))
}

fn strip_try_comments(stmt: StructuredStmt) -> StructuredStmt {
    match stmt {
        StructuredStmt::Sequence(statements) => {
            let stripped = statements
                .into_iter()
                .map(strip_try_comments)
                .filter(|statement| !matches!(statement, StructuredStmt::Empty))
                .collect::<Vec<_>>();
            wrap_sequence(stripped)
        }
        StructuredStmt::Basic(stmts) => {
            let stmts = stmts
                .into_iter()
                .filter(|stmt| {
                    !matches!(
                        stmt,
                        Stmt::Comment(message)
                            if message == "rustyflower: try/catch reconstruction is not implemented yet"
                    )
                })
                .collect::<Vec<_>>();
            if stmts.is_empty() {
                StructuredStmt::Empty
            } else {
                StructuredStmt::Basic(stmts)
            }
        }
        StructuredStmt::If {
            condition,
            then_branch,
            else_branch,
        } => StructuredStmt::If {
            condition,
            then_branch: Box::new(strip_try_comments(*then_branch)),
            else_branch: else_branch.map(|branch| Box::new(strip_try_comments(*branch))),
        },
        StructuredStmt::While { condition, body } => StructuredStmt::While {
            condition,
            body: Box::new(strip_try_comments(*body)),
        },
        StructuredStmt::Switch { expr, arms } => StructuredStmt::Switch {
            expr,
            arms: arms
                .into_iter()
                .map(|arm| SwitchArm {
                    labels: arm.labels,
                    has_default: arm.has_default,
                    body: Box::new(strip_try_comments(*arm.body)),
                })
                .collect(),
        },
        StructuredStmt::Try {
            try_body,
            catches,
            finally_body,
        } => StructuredStmt::Try {
            try_body: Box::new(strip_try_comments(*try_body)),
            catches: catches
                .into_iter()
                .map(|catch| CatchArm {
                    catch_type: catch.catch_type,
                    catch_var: catch.catch_var,
                    body: Box::new(strip_try_comments(*catch.body)),
                })
                .collect(),
            finally_body: finally_body.map(|body| Box::new(strip_try_comments(*body))),
        },
        StructuredStmt::Synchronized { expr, body } => StructuredStmt::Synchronized {
            expr,
            body: Box::new(strip_try_comments(*body)),
        },
        other => other,
    }
}

fn extract_catch_binding(
    method: &LoadedMethod,
    stmt: StructuredStmt,
    catch_type: &str,
) -> (String, StructuredStmt) {
    match stmt {
        StructuredStmt::Basic(mut stmts) => {
            if let Some(Stmt::Assign {
                target: StructuredExpr::Var(slot),
                value: StructuredExpr::CaughtException(_),
            }) = stmts.first()
            {
                let name = method.slot_name(*slot);
                stmts.remove(0);
                let body = if stmts.is_empty() {
                    StructuredStmt::Empty
                } else {
                    StructuredStmt::Basic(stmts)
                };
                return (name, body);
            }
            ("var_catch".to_string(), StructuredStmt::Basic(stmts))
        }
        StructuredStmt::Sequence(mut stmts) => {
            if let Some(first) = stmts.first_mut() {
                let (name, rewritten) = extract_catch_binding(method, first.clone(), catch_type);
                *first = rewritten;
                let rewritten = wrap_sequence(stmts);
                return (name, rewritten);
            }
            (
                fallback_catch_var(catch_type),
                StructuredStmt::Sequence(Vec::new()),
            )
        }
        other => (fallback_catch_var(catch_type), other),
    }
}

fn fallback_catch_var(catch_type: &str) -> String {
    let short = catch_type.rsplit('/').next().unwrap_or(catch_type);
    let first = short.chars().next().unwrap_or('e').to_ascii_lowercase();
    format!("{first}0")
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
