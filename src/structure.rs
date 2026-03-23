use crate::cfg::{ControlFlowGraph, build_cfg};
use crate::error::{DecompileError, Result};
use crate::expr::{
    BlockSemantics, Stmt, StructuredExpr, Terminator, negate_condition, translate_block,
};
use crate::loader::{LoadedClass, LoadedMethod};
use rust_asm::types::Type;
use std::collections::{HashSet, VecDeque};

#[derive(Debug, Clone, PartialEq)]
pub enum StructuredStmt {
    Sequence(Vec<StructuredStmt>),
    Basic(Vec<Stmt>),
    Try {
        try_body: Box<StructuredStmt>,
        catches: Vec<CatchArm>,
        finally_body: Option<Box<StructuredStmt>>,
    },
    TryWithResources {
        resources: Vec<TryResource>,
        body: Box<StructuredStmt>,
        catches: Vec<CatchArm>,
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
    DoWhile {
        condition: StructuredExpr,
        body: Box<StructuredStmt>,
    },
    For {
        init: Vec<Stmt>,
        condition: StructuredExpr,
        update: Vec<Stmt>,
        body: Box<StructuredStmt>,
    },
    ForEach {
        var_type: Type,
        var_name: String,
        iterable: StructuredExpr,
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

#[derive(Debug, Clone, PartialEq)]
pub struct TryResource {
    pub var_type: Type,
    pub var_name: String,
    pub initializer: StructuredExpr,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum SwitchLabel {
    Int(i32),
    String(String),
    Enum(String),
}

pub fn decompile_method(class: &LoadedClass, method: &LoadedMethod) -> Result<StructuredStmt> {
    let normalized = crate::normalize::normalize_method(method)?;
    let method = &normalized;
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
        GotoHandling::comment(),
    )?);
    Ok(rewrite_synchronized_stmt(root))
}

pub fn rewrite_control_flow(stmt: StructuredStmt) -> StructuredStmt {
    rewrite_control_flow_stmt(stmt)
}

pub fn decompile_expression_fallback(
    class: &LoadedClass,
    method: &LoadedMethod,
) -> Result<Option<StructuredStmt>> {
    if !method.exception_table.is_empty() {
        return Ok(None);
    }
    let normalized = crate::normalize::normalize_method(method)?;
    let method = &normalized;
    let cfg = build_cfg(method)?;
    if cfg.blocks.is_empty() {
        return Ok(Some(StructuredStmt::Sequence(Vec::new())));
    }
    let mut visiting = HashSet::new();
    let Some(expr) = build_expression_from_block(
        class,
        method,
        &cfg,
        cfg.entry,
        &method.parsed_descriptor.return_type,
        &mut visiting,
    ) else {
        return Ok(None);
    };
    Ok(Some(StructuredStmt::Basic(vec![Stmt::Return(Some(expr))])))
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
enum BranchResolution {
    Offset(u16),
    RangeEnd(usize),
}

fn build_expression_from_block(
    class: &LoadedClass,
    method: &LoadedMethod,
    cfg: &ControlFlowGraph,
    block_id: usize,
    return_type: &Type,
    visiting: &mut HashSet<usize>,
) -> Option<StructuredExpr> {
    if !visiting.insert(block_id) {
        return None;
    }
    let block = &cfg.blocks[block_id];
    let fallthrough = method.instruction_offsets.get(block.last_index + 1).copied();
    let mut temp_counter = 0u32;
    let expr = match translate_block(class, method, block, fallthrough, &mut temp_counter).ok()? {
        BlockSemantics { stmts, terminator } if stmts.is_empty() => match terminator {
            Terminator::Return(Some(expr)) => Some(normalize_expression(expr, return_type)),
            Terminator::Goto(target) => {
                if let Some(expr) = constant_block_expr(method, block, return_type)
                    && cfg
                        .block_by_offset(target)
                        .is_some_and(|target_block| is_return_only_block(method, target_block))
                {
                    Some(expr)
                } else {
                    cfg.block_by_offset(target).and_then(|target_block| {
                        build_expression_from_block(
                            class,
                            method,
                            cfg,
                            target_block.id,
                            return_type,
                            visiting,
                        )
                    })
                }
            }
            Terminator::Fallthrough(Some(target)) => {
                if let Some(expr) = constant_block_expr(method, block, return_type)
                    && cfg
                        .block_by_offset(target)
                        .is_some_and(|target_block| is_return_only_block(method, target_block))
                {
                    Some(expr)
                } else {
                    None
                }
            }
            Terminator::If {
                condition,
                jump_target,
                fallthrough_target,
            } => {
                let then_expr = cfg.block_by_offset(jump_target).and_then(|target_block| {
                    build_expression_from_block(
                        class,
                        method,
                        cfg,
                        target_block.id,
                        return_type,
                        visiting,
                    )
                })?;
                let else_expr = cfg
                    .block_by_offset(fallthrough_target)
                    .and_then(|target_block| {
                        build_expression_from_block(
                            class,
                            method,
                            cfg,
                            target_block.id,
                            return_type,
                            visiting,
                        )
                    })?;
                Some(combine_conditional_expression(
                    condition,
                    then_expr,
                    else_expr,
                    return_type,
                ))
            }
            _ => None,
        },
        _ => None,
    };
    visiting.remove(&block_id);
    expr
}

fn constant_block_expr(
    method: &LoadedMethod,
    block: &crate::cfg::BasicBlock,
    return_type: &Type,
) -> Option<StructuredExpr> {
    let first = &method.instructions[block.first_index];
    let expr = match first {
        rust_asm::insn::Insn::Simple(node) => match node.opcode {
            rust_asm::opcodes::ICONST_M1 => StructuredExpr::Literal(crate::expr::Literal::Int(-1)),
            rust_asm::opcodes::ICONST_0 => StructuredExpr::Literal(crate::expr::Literal::Int(0)),
            rust_asm::opcodes::ICONST_1 => StructuredExpr::Literal(crate::expr::Literal::Int(1)),
            rust_asm::opcodes::ICONST_2 => StructuredExpr::Literal(crate::expr::Literal::Int(2)),
            rust_asm::opcodes::ICONST_3 => StructuredExpr::Literal(crate::expr::Literal::Int(3)),
            rust_asm::opcodes::ICONST_4 => StructuredExpr::Literal(crate::expr::Literal::Int(4)),
            rust_asm::opcodes::ICONST_5 => StructuredExpr::Literal(crate::expr::Literal::Int(5)),
            _ => return None,
        },
        _ => return None,
    };
    Some(normalize_expression(expr, return_type))
}

fn is_return_only_block(method: &LoadedMethod, block: &crate::cfg::BasicBlock) -> bool {
    block.first_index == block.last_index
        && matches!(
            method.instructions[block.first_index],
            rust_asm::insn::Insn::Simple(ref node)
                if matches!(
                    node.opcode,
                    rust_asm::opcodes::IRETURN
                        | rust_asm::opcodes::ARETURN
                        | rust_asm::opcodes::LRETURN
                        | rust_asm::opcodes::FRETURN
                        | rust_asm::opcodes::DRETURN
                )
        )
}

fn combine_conditional_expression(
    condition: StructuredExpr,
    then_expr: StructuredExpr,
    else_expr: StructuredExpr,
    return_type: &Type,
) -> StructuredExpr {
    let then_expr = normalize_expression(then_expr, return_type);
    let else_expr = normalize_expression(else_expr, return_type);
    if is_boolean_true(&then_expr) && is_boolean_false(&else_expr) {
        condition
    } else if is_boolean_false(&then_expr) && is_boolean_true(&else_expr) {
        negate_condition(condition)
    } else {
        StructuredExpr::Ternary {
            condition: Box::new(condition),
            then_expr: Box::new(then_expr),
            else_expr: Box::new(else_expr),
        }
    }
}

fn normalize_expression(expr: StructuredExpr, return_type: &Type) -> StructuredExpr {
    if matches!(return_type, Type::Boolean) {
        match expr {
            StructuredExpr::Literal(crate::expr::Literal::Int(0)) => {
                StructuredExpr::Literal(crate::expr::Literal::Boolean(false))
            }
            StructuredExpr::Literal(crate::expr::Literal::Int(1)) => {
                StructuredExpr::Literal(crate::expr::Literal::Boolean(true))
            }
            other => other,
        }
    } else {
        expr
    }
}

fn is_boolean_true(expr: &StructuredExpr) -> bool {
    matches!(expr, StructuredExpr::Literal(crate::expr::Literal::Boolean(true)))
}

fn is_boolean_false(expr: &StructuredExpr) -> bool {
    matches!(expr, StructuredExpr::Literal(crate::expr::Literal::Boolean(false)))
}

#[derive(Debug, Clone)]
struct GotoHandling {
    suppressed: Vec<u16>,
    break_target: Option<u16>,
    continue_target: Option<u16>,
}

impl GotoHandling {
    fn comment() -> Self {
        Self {
            suppressed: Vec::new(),
            break_target: None,
            continue_target: None,
        }
    }

    fn suppress(target: u16) -> Self {
        Self {
            suppressed: vec![target],
            break_target: None,
            continue_target: None,
        }
    }

    fn break_to(target: u16) -> Self {
        Self {
            suppressed: Vec::new(),
            break_target: Some(target),
            continue_target: None,
        }
    }

    fn continue_to(target: u16) -> Self {
        Self {
            suppressed: Vec::new(),
            break_target: None,
            continue_target: Some(target),
        }
    }

    fn loop_targets(continue_target: u16, break_target: u16) -> Self {
        Self {
            suppressed: Vec::new(),
            break_target: Some(break_target),
            continue_target: Some(continue_target),
        }
    }

    fn with_suppressed(&self, target: u16) -> Self {
        let mut next = self.clone();
        if !next.suppressed.contains(&target) {
            next.suppressed.push(target);
        }
        next
    }
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
            if !self.suppressed_try_starts.contains(&block_start)
                && let Some((stmt, next_pos, consumed)) =
                    self.try_build_try_catch(pos, end_pos, goto_handling.clone())?
            {
                self.visited.extend(consumed);
                statements.push(stmt);
                pos = next_pos;
                continue;
            }
            if let Some((stmt, next_pos, consumed)) =
                self.try_build_synchronized(pos, end_pos, goto_handling.clone())?
            {
                self.visited.extend(consumed);
                statements.push(stmt);
                pos = next_pos;
                continue;
            }
            if let Some((stmt, next_pos, consumed)) =
                self.try_build_switch(pos, end_pos, goto_handling.clone())?
            {
                self.visited.extend(consumed);
                statements.push(stmt);
                pos = next_pos;
                continue;
            }
            if let Some((stmt, next_pos, consumed)) =
                self.try_build_do_while(pos, end_pos, goto_handling.clone())?
            {
                self.visited.extend(consumed);
                statements.push(stmt);
                pos = next_pos;
                continue;
            }
            if let Some((stmt, next_pos, consumed)) =
                self.try_build_chained_while(pos, end_pos, goto_handling.clone())?
            {
                self.visited.extend(consumed);
                statements.push(stmt);
                pos = next_pos;
                continue;
            }
            if let Some((stmt, next_pos, consumed)) =
                self.try_build_chained_if(pos, end_pos, goto_handling.clone())?
            {
                self.visited.extend(consumed);
                statements.push(stmt);
                pos = next_pos;
                continue;
            }
            if let Some((stmt, next_pos, consumed)) =
                self.try_build_while(pos, end_pos, goto_handling.clone())?
            {
                self.visited.extend(consumed);
                statements.push(stmt);
                pos = next_pos;
                continue;
            }
            if let Some((stmt, next_pos, consumed)) =
                self.try_build_if(pos, end_pos, goto_handling.clone())?
            {
                self.visited.extend(consumed);
                statements.push(stmt);
                pos = next_pos;
                continue;
            }

            self.visited.insert(block_id);
            statements.push(self.basic_statement(block_id, goto_handling.clone()));
            pos += 1;
        }
        Ok(statements)
    }

    fn basic_statement(&self, block_id: usize, goto_handling: GotoHandling) -> StructuredStmt {
        let mut stmts = self.semantics[block_id].stmts.clone();
        match &self.semantics[block_id].terminator {
            Terminator::Return(value) => stmts.push(Stmt::Return(value.clone())),
            Terminator::Throw(value) => stmts.push(Stmt::Throw(value.clone())),
            Terminator::Goto(target) => {
                if goto_handling.suppressed.contains(target) {
                } else if goto_handling.break_target == Some(*target) {
                    stmts.push(Stmt::Break);
                } else if goto_handling.continue_target == Some(*target) {
                    stmts.push(Stmt::Continue);
                } else {
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
        let raw_try_end_pos = self.position_for_offset(end_pc)?;
        let handler_pos = self.position_for_offset(handler_pc)?;
        let try_end_pos = raw_try_end_pos.min(handler_pos);
        if try_end_pos <= next_pos {
            return Ok(None);
        }

        let catch_all_end = self.catch_all_handler_end_pos(handler_pos, end_pos);
        let merge_pos = self.find_try_catch_merge_pos(
            next_pos,
            try_end_pos,
            &[],
            Some((handler_pos, catch_all_end)),
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
            merge_offset
                .map(|offset| goto_handling.with_suppressed(offset))
                .unwrap_or_else(|| goto_handling.clone()),
        )?);
        let mut try_body = strip_try_comments(try_body);
        let handler_body = wrap_sequence(self.build_range(
            handler_pos,
            catch_all_end,
            merge_offset
                .map(|offset| goto_handling.with_suppressed(offset))
                .unwrap_or_else(|| goto_handling.clone()),
        )?);
        let handler_body = strip_try_comments(handler_body);
        let (canonical_finally, _slot) = extract_finally_from_handler(handler_body)?;
        if !is_monitor_only_finally(&canonical_finally) {
            self.suppressed_try_starts
                .remove(&self.cfg.blocks[self.cfg.order[handler_pos]].start_offset);
            self.suppressed_try_starts.remove(&region_start_offset);
            return Ok(None);
        }

        if try_end_pos < handler_pos {
            let normal_tail = wrap_sequence(self.build_range(
                    try_end_pos,
                    handler_pos,
                    merge_offset
                        .map(|offset| goto_handling.with_suppressed(offset))
                        .unwrap_or_else(|| goto_handling.clone()),
                )?);
            let normal_tail = strip_try_comments(normal_tail);
            if let Some(stripped) =
                remove_duplicate_finally(self.method, normal_tail, &canonical_finally)
            {
                if !matches!(stripped, StructuredStmt::Empty) {
                    let mut items = top_level_items(try_body);
                    items.extend(top_level_items(stripped));
                    try_body = wrap_sequence(items);
                }
            }
        }

        let Some(sync_body) = strip_monitor_exit_suffix(try_body, &canonical_finally) else {
            self.suppressed_try_starts
                .remove(&self.cfg.blocks[self.cfg.order[handler_pos]].start_offset);
            self.suppressed_try_starts.remove(&region_start_offset);
            return Ok(None);
        };
        self.suppressed_try_starts
            .remove(&self.cfg.blocks[self.cfg.order[handler_pos]].start_offset);
        self.suppressed_try_starts.remove(&region_start_offset);

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

        let raw_try_end_pos = self.position_for_offset(end_pc)?;
        if raw_try_end_pos <= pos || raw_try_end_pos > end_pos {
            return Ok(None);
        }
        if (pos..raw_try_end_pos).any(|region_pos| self.visited.contains(&self.cfg.order[region_pos])) {
            return Ok(None);
        }

        let mut typed_handlers = Vec::new();
        let mut catch_all_handler = None;
        for entry in entries {
            let handler_pos = self.position_for_offset(entry.handler_pc)?;
            if handler_pos >= end_pos {
                continue;
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
        if typed_handlers.is_empty() && catch_all_handler.is_none() {
            return Ok(None);
        }
        let try_end_pos = typed_handlers
            .iter()
            .map(|(handler_pos, _)| *handler_pos)
            .chain(catch_all_handler.iter().map(|(handler_pos, _)| *handler_pos))
            .fold(raw_try_end_pos, usize::min);
        if try_end_pos <= pos {
            return Ok(None);
        }

        let catch_all_end = catch_all_handler
            .map(|(handler_pos, _)| self.catch_all_handler_end_pos(handler_pos, end_pos));
        let merge_pos = self.find_try_catch_merge_pos(
            pos,
            try_end_pos,
            &typed_handlers,
            catch_all_handler.map(|(handler_pos, _)| (handler_pos, catch_all_end.unwrap_or(handler_pos + 1))),
            end_pos,
        );
        let merge_offset = if merge_pos < self.cfg.order.len() {
            Some(self.cfg.blocks[self.cfg.order[merge_pos]].start_offset)
        } else {
            None
        };
        let catch_all_end = catch_all_end.unwrap_or(merge_pos);

        self.suppressed_try_starts.insert(start_offset);
        let try_body = wrap_sequence(self.build_range(
            pos,
            try_end_pos,
            merge_offset
                .map(|offset| goto_handling.with_suppressed(offset))
                .unwrap_or_else(|| goto_handling.clone()),
        )?);
        let mut try_body = strip_try_comments(try_body);

        let mut catches = Vec::new();
        let consumed = (pos..merge_pos.min(self.cfg.order.len()))
            .map(|region_pos| self.cfg.order[region_pos])
            .collect::<Vec<_>>();

        let first_handler_pos = typed_handlers
            .first()
            .map(|(handler_pos, _)| *handler_pos)
            .or_else(|| catch_all_handler.map(|(handler_pos, _)| handler_pos))
            .unwrap_or(merge_pos);

        if catch_all_handler.is_none() && try_end_pos < first_handler_pos {
            let normal_tail = wrap_sequence(self.build_range(
                try_end_pos,
                first_handler_pos,
                merge_offset
                    .map(|offset| goto_handling.with_suppressed(offset))
                    .unwrap_or_else(|| goto_handling.clone()),
            )?);
            let normal_tail = strip_try_comments(normal_tail);
            if !matches!(normal_tail, StructuredStmt::Empty)
                && has_terminal_exit(&normal_tail)
            {
                let mut items = top_level_items(try_body);
                items.extend(top_level_items(normal_tail));
                try_body = wrap_sequence(items);
            }
        }

        let mut finally_body = None;
        if let Some((catch_all_pos, _handler_pc)) = catch_all_handler {
            let catch_all_start_offset = self.cfg.blocks[self.cfg.order[catch_all_pos]].start_offset;
            self.suppressed_try_starts.insert(catch_all_start_offset);
            let canonical_handler_body = wrap_sequence(self.build_range(
                catch_all_pos,
                catch_all_end,
                merge_offset
                    .map(|offset| goto_handling.with_suppressed(offset))
                    .unwrap_or_else(|| goto_handling.clone()),
            )?);
            let canonical_handler_body = strip_try_comments(canonical_handler_body);
            let (canonical_finally, catch_var_slot) =
                extract_finally_from_handler(canonical_handler_body)?;

            let mut rendered_finally = canonical_finally.clone();
            if try_end_pos < first_handler_pos {
                let normal_tail = wrap_sequence(self.build_range(
                    try_end_pos,
                    first_handler_pos,
                    merge_offset
                        .map(|offset| goto_handling.with_suppressed(offset))
                        .unwrap_or_else(|| goto_handling.clone()),
                )?);
                let normal_tail = strip_try_comments(normal_tail);
                let stripped_normal_tail =
                    remove_duplicate_finally(self.method, normal_tail.clone(), &canonical_finally);
                if let Some(stripped) = stripped_normal_tail {
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
                    self.suppressed_try_starts.remove(&catch_all_start_offset);
                    self.suppressed_try_starts.remove(&start_offset);
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
                    merge_offset
                        .map(|offset| goto_handling.with_suppressed(offset))
                        .unwrap_or_else(|| goto_handling.clone()),
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
                merge_offset
                    .map(|offset| goto_handling.with_suppressed(offset))
                    .unwrap_or_else(|| goto_handling.clone()),
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
                merge_offset
                    .map(GotoHandling::break_to)
                    .unwrap_or_else(|| goto_handling.clone()),
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
        if let Terminator::Goto(condition_target) = terminator {
            let condition_pos = self.position_for_offset(*condition_target)?;
            let body_start_pos = pos + 1;
            if body_start_pos >= condition_pos || condition_pos >= end_pos {
                return Ok(None);
            }

            let condition_block_id = self.cfg.order[condition_pos];
            let Terminator::If {
                condition,
                jump_target,
                fallthrough_target,
            } = &self.semantics[condition_block_id].terminator
            else {
                return Ok(None);
            };

            let body_start_offset = self.cfg.blocks[self.cfg.order[body_start_pos]].start_offset;
            let (loop_condition, exit_pos) = if *jump_target == body_start_offset {
                (condition.clone(), self.position_for_offset(*fallthrough_target)?)
            } else if *fallthrough_target == body_start_offset {
                (
                    negate_condition(condition.clone()),
                    self.position_for_offset(*jump_target)?,
                )
            } else {
                return Ok(None);
            };

            if exit_pos <= condition_pos || exit_pos > end_pos {
                return Ok(None);
            }

            let Some(exit_offset) = self.start_offset_at(exit_pos) else {
                return Ok(None);
            };
            let body_stmts = self.build_range(
                body_start_pos,
                condition_pos,
                GotoHandling::loop_targets(*condition_target, exit_offset),
            )?;
            let while_stmt = StructuredStmt::While {
                condition: loop_condition,
                body: Box::new(wrap_sequence(body_stmts)),
            };
            let mut items = Vec::new();
            if !self.semantics[block_id].stmts.is_empty() {
                items.push(StructuredStmt::Basic(self.semantics[block_id].stmts.clone()));
            }
            items.push(while_stmt);
            let consumed = (pos..=condition_pos)
                .map(|region_pos| self.cfg.order[region_pos])
                .collect::<Vec<_>>();
            return Ok(Some((wrap_sequence(items), exit_pos, consumed)));
        }

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
        let has_backedge = (body_start_pos..exit_pos).any(|candidate_pos| {
            let candidate_id = self.cfg.order[candidate_pos];
            matches!(
                self.semantics[candidate_id].terminator,
                Terminator::Goto(target) if target == loop_header_offset
            )
        });
        if !has_backedge {
            return Ok(None);
        }
        let Some(exit_offset) = self.start_offset_at(exit_pos) else {
            return Ok(None);
        };
        let body_stmts = self.build_range(
            body_start_pos,
            exit_pos,
            GotoHandling::loop_targets(loop_header_offset, exit_offset),
        )?;
        let mut consumed = vec![block_id];
        for region_pos in body_start_pos..exit_pos {
            consumed.push(self.cfg.order[region_pos]);
        }
        let while_stmt = StructuredStmt::While {
            condition: loop_condition,
            body: Box::new(wrap_sequence(body_stmts)),
        };
        let stmt = if self.semantics[block_id].stmts.is_empty() {
            while_stmt
        } else {
            StructuredStmt::Sequence(vec![
                StructuredStmt::Basic(self.semantics[block_id].stmts.clone()),
                while_stmt,
            ])
        };
        Ok(Some((stmt, exit_pos, consumed)))
    }

    fn try_build_do_while(
        &mut self,
        pos: usize,
        end_pos: usize,
        _goto_handling: GotoHandling,
    ) -> Result<Option<(StructuredStmt, usize, Vec<usize>)>> {
        let block_id = self.cfg.order[pos];
        let start_offset = self.cfg.blocks[block_id].start_offset;

        for condition_pos in (pos + 1)..end_pos {
            let condition_block_id = self.cfg.order[condition_pos];
            let Terminator::If {
                condition,
                jump_target,
                fallthrough_target,
            } = &self.semantics[condition_block_id].terminator
            else {
                continue;
            };
            let condition_offset = self.cfg.blocks[condition_block_id].start_offset;
            let (loop_condition, exit_pos) = if *jump_target == start_offset {
                (condition.clone(), self.position_for_offset(*fallthrough_target)?)
            } else if *fallthrough_target == start_offset {
                (
                    negate_condition(condition.clone()),
                    self.position_for_offset(*jump_target)?,
                )
            } else {
                continue;
            };
            if exit_pos <= condition_pos || exit_pos > end_pos {
                continue;
            }

            let Some(exit_offset) = self.start_offset_at(exit_pos) else {
                continue;
            };
            let body_stmts = self.build_range(
                pos,
                condition_pos,
                GotoHandling::loop_targets(condition_offset, exit_offset),
            )?;
            let stmt = StructuredStmt::DoWhile {
                condition: loop_condition,
                body: Box::new(wrap_sequence(body_stmts)),
            };
            let consumed = (pos..=condition_pos)
                .map(|region_pos| self.cfg.order[region_pos])
                .collect::<Vec<_>>();
            return Ok(Some((stmt, exit_pos, consumed)));
        }

        let Terminator::If {
            condition,
            jump_target,
            fallthrough_target,
        } = &self.semantics[block_id].terminator
        else {
            return Ok(None);
        };
        if self.semantics[block_id].stmts.is_empty() {
            return Ok(None);
        }

        if *jump_target == start_offset || *fallthrough_target == start_offset {
            let (loop_condition, exit_pos) = if *jump_target == start_offset {
                (condition.clone(), self.position_for_offset(*fallthrough_target)?)
            } else {
                (
                    negate_condition(condition.clone()),
                    self.position_for_offset(*jump_target)?,
                )
            };
            if exit_pos <= pos || exit_pos > end_pos {
                return Ok(None);
            }
            let mut body_items = Vec::new();
            if !self.semantics[block_id].stmts.is_empty() {
                body_items.push(StructuredStmt::Basic(self.semantics[block_id].stmts.clone()));
            }
            let stmt = StructuredStmt::DoWhile {
                condition: loop_condition,
                body: Box::new(wrap_sequence(body_items)),
            };
            return Ok(Some((stmt, exit_pos, vec![block_id])));
        }

        let next_pos = pos + 1;
        if next_pos >= end_pos {
            return Ok(None);
        }
        let next_block_id = self.cfg.order[next_pos];
        let next_offset = self.cfg.blocks[next_block_id].start_offset;
        let Terminator::Goto(target) = self.semantics[next_block_id].terminator else {
            return Ok(None);
        };
        if target != start_offset {
            return Ok(None);
        }

        let (loop_condition, exit_pos) = if *jump_target == next_offset {
            (condition.clone(), self.position_for_offset(*fallthrough_target)?)
        } else if *fallthrough_target == next_offset {
            (
                negate_condition(condition.clone()),
                self.position_for_offset(*jump_target)?,
            )
        } else {
            return Ok(None);
        };
        if exit_pos <= next_pos || exit_pos > end_pos {
            return Ok(None);
        }

        let mut body_items = Vec::new();
        if !self.semantics[block_id].stmts.is_empty() {
            body_items.push(StructuredStmt::Basic(self.semantics[block_id].stmts.clone()));
        }
        let stmt = StructuredStmt::DoWhile {
            condition: loop_condition,
            body: Box::new(wrap_sequence(body_items)),
        };
        Ok(Some((stmt, exit_pos, vec![block_id, next_block_id])))
    }

    fn try_build_chained_while(
        &mut self,
        pos: usize,
        end_pos: usize,
        _goto_handling: GotoHandling,
    ) -> Result<Option<(StructuredStmt, usize, Vec<usize>)>> {
        let block_id = self.cfg.order[pos];
        let start_offset = self.cfg.blocks[block_id].start_offset;
        if !self.semantics[block_id].stmts.is_empty() {
            return Ok(None);
        }

        let mut backedge_pos = None;
        for candidate_pos in (pos + 1)..end_pos {
            let candidate_id = self.cfg.order[candidate_pos];
            if matches!(
                self.semantics[candidate_id].terminator,
                Terminator::Goto(target) if target == start_offset
            ) {
                backedge_pos = Some(candidate_pos);
            }
        }
        let Some(backedge_pos) = backedge_pos else {
            return Ok(None);
        };
        let exit_pos = backedge_pos + 1;
        if exit_pos >= end_pos {
            return Ok(None);
        }
        let Some(body_start_pos) = ((pos + 1)..=backedge_pos).find(|candidate_pos| {
            let candidate_id = self.cfg.order[*candidate_pos];
            !self.semantics[candidate_id].stmts.is_empty()
        }) else {
            return Ok(None);
        };

        let body_start_offset = self.cfg.blocks[self.cfg.order[body_start_pos]].start_offset;
        let Some(exit_offset) = self.start_offset_at(exit_pos) else {
            return Ok(None);
        };
        let mut visiting = HashSet::new();
        let Some(condition) = self.build_branch_expression(
            block_id,
            BranchResolution::Offset(body_start_offset),
            BranchResolution::Offset(exit_offset),
            &mut visiting,
        ) else {
            return Ok(None);
        };

        let body_stmts = self.build_range(
            body_start_pos,
            exit_pos,
            GotoHandling::loop_targets(start_offset, exit_offset),
        )?;
        let stmt = StructuredStmt::While {
            condition,
            body: Box::new(wrap_sequence(body_stmts)),
        };
        let consumed = (pos..exit_pos)
            .map(|region_pos| self.cfg.order[region_pos])
            .collect::<Vec<_>>();
        Ok(Some((stmt, exit_pos, consumed)))
    }

    fn try_build_chained_if(
        &mut self,
        pos: usize,
        end_pos: usize,
        goto_handling: GotoHandling,
    ) -> Result<Option<(StructuredStmt, usize, Vec<usize>)>> {
        let block_id = self.cfg.order[pos];
        if !self.semantics[block_id].stmts.is_empty() {
            return Ok(None);
        }
        if !matches!(self.semantics[block_id].terminator, Terminator::If { .. }) {
            return Ok(None);
        }
        let start_offset = self.cfg.blocks[block_id].start_offset;
        let has_backedge = ((pos + 1)..end_pos).any(|candidate_pos| {
            let candidate_id = self.cfg.order[candidate_pos];
            matches!(
                self.semantics[candidate_id].terminator,
                Terminator::Goto(target) if target == start_offset
            )
        });
        if has_backedge {
            return Ok(None);
        }

        let Some(body_start_pos) = ((pos + 1)..end_pos).find(|candidate_pos| {
            let candidate_id = self.cfg.order[*candidate_pos];
            !self.semantics[candidate_id].stmts.is_empty()
        }) else {
            return Ok(None);
        };
        let body_start_id = self.cfg.order[body_start_pos];
        let exit_pos = match self.semantics[body_start_id].terminator {
            Terminator::Fallthrough(Some(exit_offset)) => self.position_for_offset(exit_offset)?,
            Terminator::Throw(_) | Terminator::Return(_) => body_start_pos + 1,
            _ => return Ok(None),
        };
        if exit_pos <= body_start_pos || exit_pos > end_pos {
            return Ok(None);
        }

        let mut visiting = HashSet::new();
        let Some(condition) = self.build_branch_expression(
            block_id,
            BranchResolution::Offset(self.cfg.blocks[body_start_id].start_offset),
            BranchResolution::RangeEnd(exit_pos),
            &mut visiting,
        ) else {
            return Ok(None);
        };
        let then_body = self.build_range(body_start_pos, exit_pos, goto_handling)?;
        let if_stmt = StructuredStmt::If {
            condition,
            then_branch: Box::new(wrap_sequence(then_body)),
            else_branch: None,
        };
        let consumed = (pos..exit_pos)
            .map(|region_pos| self.cfg.order[region_pos])
            .collect::<Vec<_>>();
        Ok(Some((if_stmt, exit_pos, consumed)))
    }

    fn build_branch_expression(
        &self,
        block_id: usize,
        true_target: BranchResolution,
        false_target: BranchResolution,
        visiting: &mut HashSet<usize>,
    ) -> Option<StructuredExpr> {
        if !visiting.insert(block_id) {
            return None;
        }
        let semantics = &self.semantics[block_id];
        let expr = if !semantics.stmts.is_empty() {
            None
        } else {
            match &semantics.terminator {
                Terminator::If {
                    condition,
                    jump_target,
                    fallthrough_target,
                } => {
                    let on_jump = self.resolve_branch_target(
                        *jump_target,
                        true_target,
                        false_target,
                        visiting,
                    )?;
                    let on_fall = self.resolve_branch_target(
                        *fallthrough_target,
                        true_target,
                        false_target,
                        visiting,
                    )?;
                    Some(combine_conditional_expression(
                        condition.clone(),
                        on_jump,
                        on_fall,
                        &Type::Boolean,
                    ))
                }
                Terminator::Goto(target) => {
                    self.resolve_branch_target(*target, true_target, false_target, visiting)
                }
                _ => None,
            }
        };
        visiting.remove(&block_id);
        expr
    }

    fn resolve_branch_target(
        &self,
        target: u16,
        true_target: BranchResolution,
        false_target: BranchResolution,
        visiting: &mut HashSet<usize>,
    ) -> Option<StructuredExpr> {
        if self.branch_matches(target, true_target) {
            return Some(StructuredExpr::Literal(crate::expr::Literal::Boolean(
                true,
            )));
        }
        if self.branch_matches(target, false_target) {
            return Some(StructuredExpr::Literal(crate::expr::Literal::Boolean(
                false,
            )));
        }
        let target_block = self.cfg.block_by_offset(target)?;
        self.build_branch_expression(target_block.id, true_target, false_target, visiting)
    }

    fn branch_matches(&self, target: u16, resolution: BranchResolution) -> bool {
        match resolution {
            BranchResolution::Offset(offset) => target == offset,
            BranchResolution::RangeEnd(end_pos) => self
                .cfg
                .block_by_offset(target)
                .map(|block| position_for_block(self.cfg, block.id) >= end_pos)
                .unwrap_or(false),
        }
    }

    fn start_offset_at(&self, pos: usize) -> Option<u16> {
        self.cfg
            .order
            .get(pos)
            .map(|block_id| self.cfg.blocks[*block_id].start_offset)
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

        if split_pos > end_pos {
            let then_body = self.build_range(then_start_pos, end_pos, goto_handling)?;
            let mut consumed = vec![block_id];
            for region_pos in then_start_pos..end_pos {
                consumed.push(self.cfg.order[region_pos]);
            }
            let if_stmt = StructuredStmt::If {
                condition: source_condition,
                then_branch: Box::new(wrap_sequence(then_body)),
                else_branch: None,
            };
            let stmt = if self.semantics[block_id].stmts.is_empty() {
                if_stmt
            } else {
                StructuredStmt::Sequence(vec![
                    StructuredStmt::Basic(self.semantics[block_id].stmts.clone()),
                    if_stmt,
                ])
            };
            return Ok(Some((stmt, end_pos, consumed)));
        }

        if split_pos <= then_start_pos {
            return Ok(None);
        }

        let before_split = split_pos.saturating_sub(1);
        let before_split_id = self.cfg.order[before_split];
        let else_goto = match &self.semantics[before_split_id].terminator {
            Terminator::Goto(target) => Some(*target),
            _ => None,
        };

        let (then_branch, else_branch, next_pos_after, consumed) =
            if let Some(merge_target) = else_goto {
                let merge_pos = self.position_for_offset(merge_target)?;
                if merge_pos <= split_pos {
                    if goto_handling.break_target == Some(merge_target)
                        || goto_handling.continue_target == Some(merge_target)
                    {
                        let then_body =
                            self.build_range(then_start_pos, split_pos, goto_handling.clone())?;
                        let else_body =
                            self.build_range(split_pos, end_pos, goto_handling.clone())?;
                        let mut consumed = vec![block_id];
                        for region_pos in then_start_pos..end_pos {
                            consumed.push(self.cfg.order[region_pos]);
                        }
                        let then_branch = if else_is_jump_target {
                            wrap_sequence(then_body.clone())
                        } else {
                            wrap_sequence(else_body.clone())
                        };
                        let else_branch = if else_is_jump_target {
                            Some(wrap_sequence(else_body))
                        } else {
                            Some(wrap_sequence(then_body))
                        };
                        let if_stmt = StructuredStmt::If {
                            condition: source_condition,
                            then_branch: Box::new(then_branch),
                            else_branch: else_branch.map(Box::new),
                        };
                        let stmt = if self.semantics[block_id].stmts.is_empty() {
                            if_stmt
                        } else {
                            StructuredStmt::Sequence(vec![
                                StructuredStmt::Basic(self.semantics[block_id].stmts.clone()),
                                if_stmt,
                            ])
                        };
                        return Ok(Some((stmt, end_pos, consumed)));
                    }
                    return Ok(None);
                }
                let then_goto_handling =
                    if goto_handling.break_target == Some(merge_target)
                        || goto_handling.continue_target == Some(merge_target)
                    {
                        goto_handling.clone()
                    } else {
                        goto_handling.with_suppressed(merge_target)
                    };
                let then_body = self.build_range(
                    then_start_pos,
                    split_pos,
                    then_goto_handling,
                )?;
                let else_body = self.build_range(split_pos, merge_pos, goto_handling.clone())?;
                let mut consumed = vec![block_id];
                for region_pos in then_start_pos..merge_pos {
                    consumed.push(self.cfg.order[region_pos]);
                }
                let then_branch = if else_is_jump_target {
                    wrap_sequence(then_body.clone())
                } else {
                    wrap_sequence(else_body.clone())
                };
                let else_branch = if else_is_jump_target {
                    Some(wrap_sequence(else_body))
                } else {
                    Some(wrap_sequence(then_body))
                };
                (then_branch, else_branch, merge_pos, consumed)
            } else {
                let then_body = self.build_range(then_start_pos, split_pos, goto_handling.clone())?;
                let mut consumed = vec![block_id];
                for region_pos in then_start_pos..split_pos {
                    consumed.push(self.cfg.order[region_pos]);
                }
                let if_stmt = StructuredStmt::If {
                    condition: source_condition,
                    then_branch: Box::new(wrap_sequence(then_body)),
                    else_branch: None,
                };
                let stmt = if self.semantics[block_id].stmts.is_empty() {
                    if_stmt
                } else {
                    StructuredStmt::Sequence(vec![
                        StructuredStmt::Basic(self.semantics[block_id].stmts.clone()),
                        if_stmt,
                    ])
                };
                return Ok(Some((stmt, split_pos, consumed)));
            };

        let if_stmt = StructuredStmt::If {
            condition: source_condition,
            then_branch: Box::new(then_branch),
            else_branch: else_branch.map(Box::new),
        };
        let stmt = if self.semantics[block_id].stmts.is_empty() {
            if_stmt
        } else {
            StructuredStmt::Sequence(vec![
                StructuredStmt::Basic(self.semantics[block_id].stmts.clone()),
                if_stmt,
            ])
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
        catch_all_handler: Option<(usize, usize)>,
        end_pos: usize,
    ) -> usize {
        let last_handler_pos = handlers
            .iter()
            .map(|(handler_pos, _)| *handler_pos)
            .max()
            .max(catch_all_handler.map(|(_, handler_end_pos)| handler_end_pos.saturating_sub(1)))
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
        let mut max_pos = handler_pos;
        let mut queue = VecDeque::from([handler_pos]);
        let mut visited = HashSet::new();

        while let Some(pos) = queue.pop_front() {
            if pos >= end_pos || !visited.insert(pos) {
                continue;
            }
            max_pos = max_pos.max(pos);
            let block_id = self.cfg.order[pos];
            for successor in successor_positions(self.cfg, &self.semantics[block_id]) {
                if successor >= handler_pos && successor < end_pos {
                    queue.push_back(successor);
                }
            }
        }

        max_pos + 1
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
        StructuredStmt::TryWithResources {
            resources,
            body,
            catches,
        } => StructuredStmt::TryWithResources {
            resources,
            body: Box::new(rewrite_synchronized_stmt(*body)),
            catches: catches
                .into_iter()
                .map(|catch| CatchArm {
                    catch_type: catch.catch_type,
                    catch_var: catch.catch_var,
                    body: Box::new(rewrite_synchronized_stmt(*catch.body)),
                })
                .collect(),
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
        StructuredStmt::ForEach {
            var_type,
            var_name,
            iterable,
            body,
        } => StructuredStmt::ForEach {
            var_type,
            var_name,
            iterable,
            body: Box::new(rewrite_synchronized_stmt(*body)),
        },
        other => other,
    }
}

fn rewrite_synchronized_sequence(items: Vec<StructuredStmt>) -> StructuredStmt {
    let rewritten = items
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

fn rewrite_control_flow_stmt(stmt: StructuredStmt) -> StructuredStmt {
    match stmt {
        StructuredStmt::Sequence(items) => rewrite_control_flow_sequence(items),
        StructuredStmt::Try {
            try_body,
            catches,
            finally_body,
        } => StructuredStmt::Try {
            try_body: Box::new(rewrite_control_flow_stmt(*try_body)),
            catches: catches
                .into_iter()
                .map(|catch| CatchArm {
                    catch_type: catch.catch_type,
                    catch_var: catch.catch_var,
                    body: Box::new(rewrite_control_flow_stmt(*catch.body)),
                })
                .collect(),
            finally_body: finally_body.map(|body| Box::new(rewrite_control_flow_stmt(*body))),
        },
        StructuredStmt::TryWithResources {
            resources,
            body,
            catches,
        } => StructuredStmt::TryWithResources {
            resources,
            body: Box::new(rewrite_control_flow_stmt(*body)),
            catches: catches
                .into_iter()
                .map(|catch| CatchArm {
                    catch_type: catch.catch_type,
                    catch_var: catch.catch_var,
                    body: Box::new(rewrite_control_flow_stmt(*catch.body)),
                })
                .collect(),
        },
        StructuredStmt::Switch { expr, arms } => StructuredStmt::Switch {
            expr,
            arms: arms
                .into_iter()
                .map(|arm| SwitchArm {
                    labels: arm.labels,
                    has_default: arm.has_default,
                    body: Box::new(rewrite_control_flow_stmt(*arm.body)),
                })
                .collect(),
        },
        StructuredStmt::If {
            condition,
            then_branch,
            else_branch,
        } => StructuredStmt::If {
            condition,
            then_branch: Box::new(rewrite_control_flow_stmt(*then_branch)),
            else_branch: else_branch.map(|branch| Box::new(rewrite_control_flow_stmt(*branch))),
        },
        StructuredStmt::While { condition, body } => StructuredStmt::While {
            condition,
            body: Box::new(strip_terminal_continue(rewrite_control_flow_stmt(*body))),
        },
        StructuredStmt::DoWhile { condition, body } => StructuredStmt::DoWhile {
            condition,
            body: Box::new(strip_terminal_continue(rewrite_control_flow_stmt(*body))),
        },
        StructuredStmt::For {
            init,
            condition,
            update,
            body,
        } => StructuredStmt::For {
            init,
            condition,
            update,
            body: Box::new(strip_terminal_continue(rewrite_control_flow_stmt(*body))),
        },
        StructuredStmt::ForEach {
            var_type,
            var_name,
            iterable,
            body,
        } => StructuredStmt::ForEach {
            var_type,
            var_name,
            iterable,
            body: Box::new(strip_terminal_continue(rewrite_control_flow_stmt(*body))),
        },
        other => other,
    }
}

fn rewrite_control_flow_sequence(items: Vec<StructuredStmt>) -> StructuredStmt {
    let rewritten = items
        .into_iter()
        .map(rewrite_control_flow_stmt)
        .flat_map(top_level_items)
        .collect::<Vec<_>>();
    let mut output = Vec::new();
    let mut index = 0;
    while index < rewritten.len() {
        if let Some((stmt, consumed)) = try_rewrite_for_loop(&rewritten[index..]) {
            output.push(stmt);
            index += consumed;
            continue;
        }
        output.push(rewritten[index].clone());
        index += 1;
    }
    wrap_sequence(output)
}

fn try_rewrite_for_loop(items: &[StructuredStmt]) -> Option<(StructuredStmt, usize)> {
    if items.len() < 2 {
        return None;
    }
    let StructuredStmt::Basic(init) = &items[0] else {
        return None;
    };
    if init.len() != 1 {
        return None;
    }
    let StructuredStmt::While { condition, body } = &items[1] else {
        return None;
    };
    let init_slot = stmt_target_slot(&init[0])?;
    let (body_without_update, update) = extract_for_update(*body.clone(), init_slot)?;
    let body = rewrite_for_continue_body(body_without_update);
    Some((
        StructuredStmt::For {
            init: init.clone(),
            condition: condition.clone(),
            update,
            body: Box::new(body),
        },
        2,
    ))
}

fn extract_for_update(body: StructuredStmt, slot: u16) -> Option<(StructuredStmt, Vec<Stmt>)> {
    match body {
        StructuredStmt::Basic(mut stmts) => {
            let last = stmts.last()?;
            if stmt_target_slot(last) != Some(slot) {
                return None;
            }
            let update = vec![stmts.pop()?];
            let body = if stmts.is_empty() {
                StructuredStmt::Empty
            } else {
                StructuredStmt::Basic(stmts)
            };
            Some((body, update))
        }
        StructuredStmt::Sequence(mut items) => {
            let last = items.pop()?;
            let (rewritten_last, update) = extract_for_update(last, slot)?;
            if !matches!(rewritten_last, StructuredStmt::Empty) {
                items.push(rewritten_last);
            }
            Some((wrap_sequence(items), update))
        }
        _ => None,
    }
}

fn rewrite_for_continue_body(body: StructuredStmt) -> StructuredStmt {
    match body {
        StructuredStmt::If {
            condition,
            then_branch,
            else_branch: Some(else_branch),
        } if is_structurally_empty(&then_branch) => wrap_sequence(vec![
            StructuredStmt::If {
                condition,
                then_branch: Box::new(StructuredStmt::Basic(vec![Stmt::Continue])),
                else_branch: None,
            },
            rewrite_for_continue_body(*else_branch),
        ]),
        StructuredStmt::Sequence(mut items) => {
            if let Some(last) = items.pop() {
                let rewritten_last = rewrite_for_continue_body(last);
                if !matches!(rewritten_last, StructuredStmt::Empty) {
                    items.push(rewritten_last);
                }
            }
            wrap_sequence(items)
        }
        other => other,
    }
}

fn is_structurally_empty(stmt: &StructuredStmt) -> bool {
    match stmt {
        StructuredStmt::Empty => true,
        StructuredStmt::Basic(stmts) => stmts.is_empty(),
        StructuredStmt::Sequence(items) => items.iter().all(is_structurally_empty),
        _ => false,
    }
}

fn strip_terminal_continue(stmt: StructuredStmt) -> StructuredStmt {
    match stmt {
        StructuredStmt::Basic(mut stmts) => {
            while matches!(stmts.last(), Some(Stmt::Continue)) {
                stmts.pop();
            }
            if stmts.is_empty() {
                StructuredStmt::Empty
            } else {
                StructuredStmt::Basic(stmts)
            }
        }
        StructuredStmt::Sequence(mut items) => {
            while matches!(items.last(), Some(StructuredStmt::Empty)) {
                items.pop();
            }
            if let Some(last) = items.pop() {
                let stripped = strip_terminal_continue(last);
                if !matches!(stripped, StructuredStmt::Empty) {
                    items.push(stripped);
                }
            }
            wrap_sequence(items)
        }
        other => other,
    }
}

fn stmt_target_slot(stmt: &Stmt) -> Option<u16> {
    match stmt {
        Stmt::Assign {
            target: StructuredExpr::Var(slot),
            ..
        } => Some(*slot),
        _ => None,
    }
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
    let monitor_exit_expr = single_monitor_exit_expr(finally_body)?;
    if !exprs_equivalent(&monitor_expr, &monitor_exit_expr) {
        return None;
    }
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
    let monitor_exit_expr = single_monitor_exit_expr(finally_body)?;
    Some(strip_monitor_exit_expr(body, &monitor_exit_expr))
}

fn single_monitor_exit_expr(stmt: &StructuredStmt) -> Option<StructuredExpr> {
    let items = top_level_items(stmt.clone());
    if items.len() != 1 {
        return None;
    }
    let StructuredStmt::Basic(stmts) = &items[0] else {
        return None;
    };
    if stmts.len() != 1 {
        return None;
    }
    let Stmt::MonitorExit(expr) = &stmts[0] else {
        return None;
    };
    Some(expr.clone())
}

fn exprs_equivalent(left: &StructuredExpr, right: &StructuredExpr) -> bool {
    match (left, right) {
        (StructuredExpr::This, StructuredExpr::This) => true,
        (StructuredExpr::Var(left), StructuredExpr::Var(right)) => left == right,
        (StructuredExpr::Temp(left), StructuredExpr::Temp(right)) => left == right,
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
                    (Some(left), Some(right)) => exprs_equivalent(left, right),
                    (None, None) => true,
                    _ => false,
                }
        }
        _ => left == right,
    }
}

fn strip_monitor_exit_expr(stmt: StructuredStmt, monitor_exit_expr: &StructuredExpr) -> StructuredStmt {
    match stmt {
        StructuredStmt::Sequence(items) => wrap_sequence(
            items
                .into_iter()
                .map(|item| strip_monitor_exit_expr(item, monitor_exit_expr))
                .collect(),
        ),
        StructuredStmt::Basic(stmts) => {
            let filtered = stmts
                .into_iter()
                .filter(|stmt| {
                    !matches!(
                        stmt,
                        Stmt::MonitorExit(expr) if exprs_equivalent(expr, monitor_exit_expr)
                    )
                })
                .collect::<Vec<_>>();
            if filtered.is_empty() {
                StructuredStmt::Empty
            } else {
                StructuredStmt::Basic(filtered)
            }
        }
        StructuredStmt::If {
            condition,
            then_branch,
            else_branch,
        } => StructuredStmt::If {
            condition,
            then_branch: Box::new(strip_monitor_exit_expr(*then_branch, monitor_exit_expr)),
            else_branch: else_branch
                .map(|branch| Box::new(strip_monitor_exit_expr(*branch, monitor_exit_expr))),
        },
        StructuredStmt::While { condition, body } => StructuredStmt::While {
            condition,
            body: Box::new(strip_monitor_exit_expr(*body, monitor_exit_expr)),
        },
        StructuredStmt::ForEach {
            var_type,
            var_name,
            iterable,
            body,
        } => StructuredStmt::ForEach {
            var_type,
            var_name,
            iterable,
            body: Box::new(strip_monitor_exit_expr(*body, monitor_exit_expr)),
        },
        StructuredStmt::Switch { expr, arms } => StructuredStmt::Switch {
            expr,
            arms: arms
                .into_iter()
                .map(|arm| SwitchArm {
                    labels: arm.labels,
                    has_default: arm.has_default,
                    body: Box::new(strip_monitor_exit_expr(*arm.body, monitor_exit_expr)),
                })
                .collect(),
        },
        StructuredStmt::Try {
            try_body,
            catches,
            finally_body,
        } => StructuredStmt::Try {
            try_body: Box::new(strip_monitor_exit_expr(*try_body, monitor_exit_expr)),
            catches: catches
                .into_iter()
                .map(|catch| CatchArm {
                    catch_type: catch.catch_type,
                    catch_var: catch.catch_var,
                    body: Box::new(strip_monitor_exit_expr(*catch.body, monitor_exit_expr)),
                })
                .collect(),
            finally_body: finally_body
                .map(|body| Box::new(strip_monitor_exit_expr(*body, monitor_exit_expr))),
        },
        StructuredStmt::TryWithResources {
            resources,
            body,
            catches,
        } => StructuredStmt::TryWithResources {
            resources,
            body: Box::new(strip_monitor_exit_expr(*body, monitor_exit_expr)),
            catches: catches
                .into_iter()
                .map(|catch| CatchArm {
                    catch_type: catch.catch_type,
                    catch_var: catch.catch_var,
                    body: Box::new(strip_monitor_exit_expr(*catch.body, monitor_exit_expr)),
                })
                .collect(),
        },
        StructuredStmt::Synchronized { expr, body } => StructuredStmt::Synchronized {
            expr,
            body: Box::new(strip_monitor_exit_expr(*body, monitor_exit_expr)),
        },
        other => other,
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
    if matches!(stmt, StructuredStmt::Empty) {
        return Ok((StructuredStmt::Empty, None));
    }
    let (slot, without_binding) = extract_catch_binding_slot(stmt);
    if matches!(without_binding, StructuredStmt::Empty) {
        return Ok((StructuredStmt::Empty, slot));
    }
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
        (
            StructuredStmt::ForEach {
                var_type: left_ty,
                var_name: left_name,
                iterable: left_iterable,
                body: left_body,
            },
            StructuredStmt::ForEach {
                var_type: right_ty,
                var_name: right_name,
                iterable: right_iterable,
                body: right_body,
            },
        ) => {
            left_ty == right_ty
                && left_name == right_name
                && expr_equivalent(
                    method,
                    left_iterable,
                    right_iterable,
                    slot_map,
                    reverse_slot_map,
                    temp_map,
                    reverse_temp_map,
                )
                && stmt_equivalent(
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
            StructuredExpr::StringConcat { parts: left_parts },
            StructuredExpr::StringConcat { parts: right_parts },
        ) => {
            left_parts.len() == right_parts.len()
                && left_parts.iter().zip(right_parts.iter()).all(|(left, right)| match (left, right) {
                    (
                        crate::expr::StringConcatPart::Literal(left),
                        crate::expr::StringConcatPart::Literal(right),
                    ) => left == right,
                    (
                        crate::expr::StringConcatPart::Expr(left),
                        crate::expr::StringConcatPart::Expr(right),
                    ) => expr_equivalent(
                        method,
                        left,
                        right,
                        slot_map,
                        reverse_slot_map,
                        temp_map,
                        reverse_temp_map,
                    ),
                    _ => false,
                })
        }
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

    let monitor_exit_expr = single_monitor_exit_expr(finally_body)?;
    if !exprs_equivalent(&monitor_expr, &monitor_exit_expr) {
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
        StructuredStmt::ForEach {
            var_type,
            var_name,
            iterable,
            body,
        } => StructuredStmt::ForEach {
            var_type,
            var_name,
            iterable,
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
        StructuredStmt::TryWithResources {
            resources,
            body,
            catches,
        } => StructuredStmt::TryWithResources {
            resources,
            body: Box::new(strip_try_comments(*body)),
            catches: catches
                .into_iter()
                .map(|catch| CatchArm {
                    catch_type: catch.catch_type,
                    catch_var: catch.catch_var,
                    body: Box::new(strip_try_comments(*catch.body)),
                })
                .collect(),
        },
        StructuredStmt::Synchronized { expr, body } => StructuredStmt::Synchronized {
            expr,
            body: Box::new(strip_try_comments(*body)),
        },
        other => other,
    }
}

fn has_terminal_exit(stmt: &StructuredStmt) -> bool {
    match stmt {
        StructuredStmt::Basic(stmts) => matches!(
            stmts.last(),
            Some(Stmt::Return(_) | Stmt::Throw(_))
        ),
        StructuredStmt::Sequence(items) => items.last().is_some_and(has_terminal_exit),
        _ => false,
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
