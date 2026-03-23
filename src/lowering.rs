use crate::bytecode::{ResolvedConstant, resolve_field_ref, resolve_ldc, resolve_method_ref};
use crate::expr::{BinaryOp, Literal, Stmt, StructuredExpr};
use crate::loader::{LoadedClass, LoadedMethod, load_class};
use crate::structure::{StructuredStmt, SwitchArm, SwitchLabel};
use rust_asm::types::Type;
use rust_asm::class_reader::ClassReader;
use rust_asm::constant_pool::CpInfo;
use rust_asm::insn::{Insn, LdcValue};
use rust_asm::opcodes;
use std::collections::HashMap;
use std::path::{Path, PathBuf};

#[derive(Debug, Clone)]
pub struct ClassPathResolver {
    root: PathBuf,
}

impl ClassPathResolver {
    pub fn for_class_file(path: &Path, internal_name: &str) -> Option<Self> {
        let mut root = path.parent()?.to_path_buf();
        let package_depth = internal_name.matches('/').count();
        for _ in 0..package_depth {
            root = root.parent()?.to_path_buf();
        }
        Some(Self { root })
    }

    pub fn load_class(&self, internal_name: &str) -> Option<LoadedClass> {
        let path = self
            .root
            .join(format!("{}.class", internal_name.replace('/', "\\")));
        let bytes = std::fs::read(path).ok()?;
        let class_node = ClassReader::new(&bytes).to_class_node().ok()?;
        load_class(class_node).ok()
    }
}

pub fn lower_switches(
    class: &LoadedClass,
    method: &LoadedMethod,
    stmt: StructuredStmt,
    resolver: Option<&ClassPathResolver>,
) -> StructuredStmt {
    let lowered = lower_stmt(class, method, stmt, resolver);
    match lowered {
        StructuredStmt::Sequence(items) => {
            StructuredStmt::Sequence(lower_sequence(class, method, items, resolver))
        }
        other => other,
    }
}

fn lower_stmt(
    class: &LoadedClass,
    method: &LoadedMethod,
    stmt: StructuredStmt,
    resolver: Option<&ClassPathResolver>,
) -> StructuredStmt {
    match stmt {
        StructuredStmt::Basic(stmts) => StructuredStmt::Basic(stmts),
        StructuredStmt::Sequence(items) => {
            StructuredStmt::Sequence(lower_sequence(class, method, items, resolver))
        }
        StructuredStmt::If {
            condition,
            then_branch,
            else_branch,
        } => StructuredStmt::If {
            condition,
            then_branch: Box::new(lower_stmt(class, method, *then_branch, resolver)),
            else_branch: else_branch
                .map(|branch| Box::new(lower_stmt(class, method, *branch, resolver))),
        },
        StructuredStmt::While { condition, body } => StructuredStmt::While {
            condition,
            body: Box::new(lower_stmt(class, method, *body, resolver)),
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
            body: Box::new(lower_stmt(class, method, *body, resolver)),
        },
        StructuredStmt::Try {
            try_body,
            catches,
            finally_body,
        } => StructuredStmt::Try {
            try_body: Box::new(lower_stmt(class, method, *try_body, resolver)),
            catches: catches
                .into_iter()
                .map(|catch| crate::structure::CatchArm {
                    catch_type: catch.catch_type,
                    catch_var: catch.catch_var,
                    body: Box::new(lower_stmt(class, method, *catch.body, resolver)),
                })
                .collect(),
            finally_body: finally_body
                .map(|body| Box::new(lower_stmt(class, method, *body, resolver))),
        },
        StructuredStmt::Synchronized { expr, body } => StructuredStmt::Synchronized {
            expr,
            body: Box::new(lower_stmt(class, method, *body, resolver)),
        },
        StructuredStmt::Switch { expr, arms } => {
            let lowered_arms = arms
                .into_iter()
                .map(|arm| SwitchArm {
                    labels: arm.labels,
                    has_default: arm.has_default,
                    body: Box::new(lower_stmt(class, method, *arm.body, resolver)),
                })
                .collect::<Vec<_>>();
            lower_enum_switch(class, method, expr.clone(), lowered_arms.clone(), resolver)
                .unwrap_or(StructuredStmt::Switch {
                    expr,
                    arms: lowered_arms,
                })
        }
        other => other,
    }
}

fn lower_sequence(
    class: &LoadedClass,
    method: &LoadedMethod,
    items: Vec<StructuredStmt>,
    resolver: Option<&ClassPathResolver>,
) -> Vec<StructuredStmt> {
    let lowered_items = items
        .into_iter()
        .map(|stmt| lower_stmt(class, method, stmt, resolver))
        .flat_map(flatten_sequence_stmt)
        .collect::<Vec<_>>();

    let mut output = Vec::new();
    let mut index = 0;
    while index < lowered_items.len() {
        if let Some((stmt, consumed)) = lower_string_switch(class, method, &lowered_items[index..])
        {
            output.push(stmt);
            index += consumed;
            continue;
        }
        if let Some((stmt, consumed)) = lower_array_foreach(method, &lowered_items[index..]) {
            output.push(stmt);
            index += consumed;
            continue;
        }
        if let Some((stmt, consumed)) = lower_iterator_foreach(method, &lowered_items[index..]) {
            output.push(stmt);
            index += consumed;
            continue;
        }
        output.push(lowered_items[index].clone());
        index += 1;
    }
    output
}

fn flatten_sequence_stmt(stmt: StructuredStmt) -> Vec<StructuredStmt> {
    match stmt {
        StructuredStmt::Sequence(items) => items
            .into_iter()
            .flat_map(flatten_sequence_stmt)
            .collect::<Vec<_>>(),
        other => vec![other],
    }
}

fn lower_string_switch(
    class: &LoadedClass,
    method: &LoadedMethod,
    items: &[StructuredStmt],
) -> Option<(StructuredStmt, usize)> {
    if items.len() < 3 {
        return None;
    }
    let prefix = match &items[0] {
        StructuredStmt::Basic(stmts) => stmts,
        _ => return None,
    };
    let first_switch = match &items[1] {
        StructuredStmt::Switch { expr, arms } => (expr, arms),
        _ => return None,
    };
    let (mid_scaffolding, second_switch, consumed) = match items.get(2) {
        Some(StructuredStmt::Switch { expr, arms }) => (Vec::new(), (expr, arms), 3),
        Some(StructuredStmt::Basic(stmts)) => match items.get(3) {
            Some(StructuredStmt::Switch { expr, arms })
                if stmts
                    .iter()
                    .all(|stmt| is_string_switch_scaffolding(stmt, 0, 0) || matches!(stmt, Stmt::Assign { .. })) =>
            {
                (stmts.clone(), (expr, arms), 4)
            }
            _ => return None,
        },
        _ => return None,
    };

    let discriminator_slot = match second_switch.0 {
        StructuredExpr::Var(slot) => *slot,
        _ => return None,
    };

    let (selector_slot, selector_expr) = match extract_string_selector(prefix, first_switch.0)? {
        Some(value) => value,
        None => return None,
    };

    let mapping = detect_string_switch_map(class, method, selector_slot, discriminator_slot);
    if mapping.is_empty() {
        return None;
    }

    let lowered_arms = second_switch
        .1
        .iter()
        .map(|arm| {
            let mut labels = Vec::new();
            for label in &arm.labels {
                match label {
                    SwitchLabel::Int(value) => {
                        if let Some(string) = mapping.get(value) {
                            labels.push(SwitchLabel::String(string.clone()));
                        } else {
                            labels.push(SwitchLabel::Int(*value));
                        }
                    }
                    other => labels.push(other.clone()),
                }
            }
            SwitchArm {
                labels,
                has_default: arm.has_default,
                body: arm.body.clone(),
            }
        })
        .collect::<Vec<_>>();

    let mut residual_prefix = prefix
        .iter()
        .filter(|stmt| !is_string_switch_scaffolding(stmt, selector_slot, discriminator_slot))
        .cloned()
        .collect::<Vec<_>>();
    residual_prefix.extend(
        mid_scaffolding
            .into_iter()
            .filter(|stmt| !is_string_switch_scaffolding(stmt, selector_slot, discriminator_slot)),
    );

    let lowered_switch = StructuredStmt::Switch {
        expr: selector_expr,
        arms: lowered_arms,
    };
    let result = if residual_prefix.is_empty() {
        lowered_switch
    } else {
        StructuredStmt::Sequence(vec![StructuredStmt::Basic(residual_prefix), lowered_switch])
    };
    Some((result, consumed))
}

fn lower_array_foreach(method: &LoadedMethod, items: &[StructuredStmt]) -> Option<(StructuredStmt, usize)> {
    if items.len() < 2 {
        return None;
    }
    let StructuredStmt::Basic(prefix) = &items[0] else {
        return None;
    };
    let StructuredStmt::While { condition, body } = &items[1] else {
        return None;
    };

    let (iter_slot, len_slot, index_slot, iterable_expr, prefix_consumed) =
        match_array_foreach_prefix(method, prefix)?;
    let StructuredExpr::Binary {
        op: BinaryOp::Lt,
        left,
        right,
    } = condition
    else {
        return None;
    };
    if !matches!(&**left, StructuredExpr::Var(slot) if *slot == index_slot)
        || !matches!(&**right, StructuredExpr::Var(slot) if *slot == len_slot)
    {
        return None;
    }

    let body_items = flatten_sequence_stmt((**body).clone());
    let (var_slot, foreach_body) = peel_array_foreach_body(method, &body_items, iter_slot, index_slot)?;
    let var_type = infer_expr_type_from_prefix(method, prefix, &iterable_expr)
        .and_then(|ty| match ty {
            Type::Array(element) => Some(*element),
            _ => None,
        })
        .unwrap_or(Type::Object("java/lang/Object".to_string()));

    let retained_prefix = prefix[..prefix.len().saturating_sub(prefix_consumed)].to_vec();
    let foreach_stmt = StructuredStmt::ForEach {
        var_type,
        var_name: method.slot_name(var_slot),
        iterable: iterable_expr,
        body: Box::new(foreach_body),
    };
    let result = if retained_prefix.is_empty() {
        foreach_stmt
    } else {
        StructuredStmt::Sequence(vec![StructuredStmt::Basic(retained_prefix), foreach_stmt])
    };
    Some((result, 2))
}

fn match_array_foreach_prefix(
    method: &LoadedMethod,
    prefix: &[Stmt],
) -> Option<(u16, u16, u16, StructuredExpr, usize)> {
    if prefix.len() < 3 {
        return None;
    }
    let idx_init = prefix.last()?;
    let len_assign = prefix.get(prefix.len().checked_sub(2)?)?;
    let iter_assign = prefix.get(prefix.len().checked_sub(3)?)?;

    let Stmt::Assign {
        target: StructuredExpr::Var(index_slot),
        value: StructuredExpr::Literal(Literal::Int(0)),
    } = idx_init
    else {
        return None;
    };
    let Stmt::Assign {
        target: StructuredExpr::Var(len_slot),
        value: StructuredExpr::ArrayLength(iter_expr),
    } = len_assign
    else {
        return None;
    };

    let (iter_slot, iterable_expr) = match iter_assign {
        Stmt::Assign {
            target: StructuredExpr::Var(slot),
            value,
        } => (*slot, value.clone()),
        _ => return None,
    };
    if !matches!(&**iter_expr, StructuredExpr::Var(slot) if *slot == iter_slot) {
        return None;
    }
    let _ = method;
    Some((iter_slot, *len_slot, *index_slot, iterable_expr, 3))
}

fn peel_array_foreach_body(
    method: &LoadedMethod,
    body_items: &[StructuredStmt],
    iter_slot: u16,
    index_slot: u16,
) -> Option<(u16, StructuredStmt)> {
    let first = body_items.first()?;
    let StructuredStmt::Basic(first_stmts) = first else {
        return None;
    };
    let first_stmt = first_stmts.first()?;
    let (var_slot, head_consumed) = match first_stmt {
        Stmt::Assign {
            target: StructuredExpr::Var(var_slot),
            value:
                StructuredExpr::ArrayAccess {
                    array,
                    index,
                },
        } if matches!(&**array, StructuredExpr::Var(slot) if *slot == iter_slot)
            && matches!(&**index, StructuredExpr::Var(slot) if *slot == index_slot) =>
        {
            (*var_slot, 1usize)
        }
        _ => return None,
    };

    let last = body_items.last()?;
    let StructuredStmt::Basic(last_stmts) = last else {
        return None;
    };
    let tail_consumed = match last_stmts.last()? {
        Stmt::Assign {
            target: StructuredExpr::Var(slot),
            value:
                StructuredExpr::Binary {
                    op: BinaryOp::Add,
                    left,
                    right,
                },
        } if *slot == index_slot
            && matches!(&**left, StructuredExpr::Var(left_slot) if *left_slot == index_slot)
            && matches!(&**right, StructuredExpr::Literal(Literal::Int(1))) =>
        {
            1usize
        }
        _ => return None,
    };

    let mut rebuilt = Vec::new();
    for (index, item) in body_items.iter().enumerate() {
        match item {
            StructuredStmt::Basic(stmts) if index == 0 && index + 1 == body_items.len() => {
                let trimmed =
                    stmts[head_consumed..stmts.len().saturating_sub(tail_consumed)].to_vec();
                if !trimmed.is_empty() {
                    rebuilt.push(StructuredStmt::Basic(trimmed));
                }
            }
            StructuredStmt::Basic(stmts) if index == 0 => {
                let trimmed = stmts[head_consumed..].to_vec();
                if !trimmed.is_empty() {
                    rebuilt.push(StructuredStmt::Basic(trimmed));
                }
            }
            StructuredStmt::Basic(stmts) if index + 1 == body_items.len() => {
                let trimmed = stmts[..stmts.len().saturating_sub(tail_consumed)].to_vec();
                if !trimmed.is_empty() {
                    rebuilt.push(StructuredStmt::Basic(trimmed));
                }
            }
            other => rebuilt.push(other.clone()),
        }
    }
    let _ = method;
    Some((var_slot, wrap_sequence(rebuilt)))
}

fn lower_iterator_foreach(method: &LoadedMethod, items: &[StructuredStmt]) -> Option<(StructuredStmt, usize)> {
    if items.len() < 2 {
        return None;
    }
    let StructuredStmt::Basic(prefix) = &items[0] else {
        return None;
    };
    let StructuredStmt::While { condition, body } = &items[1] else {
        return None;
    };

    let (iterator_slot, iterable_expr, prefix_consumed) = match_iterator_foreach_prefix(prefix)?;
    if !matches!(
        condition,
        StructuredExpr::Call {
            receiver: Some(receiver),
            owner,
            name,
            descriptor,
            args,
            ..
        } if matches!(&**receiver, StructuredExpr::Var(slot) if *slot == iterator_slot)
            && owner == "java/util/Iterator"
            && name == "hasNext"
            && descriptor == "()Z"
            && args.is_empty()
    ) {
        return None;
    }

    let body_items = flatten_sequence_stmt((**body).clone());
    let (var_slot, var_type, foreach_body) = peel_iterator_foreach_body(method, &body_items, iterator_slot)?;

    let retained_prefix = prefix[..prefix.len().saturating_sub(prefix_consumed)].to_vec();
    let foreach_stmt = StructuredStmt::ForEach {
        var_type,
        var_name: method.slot_name(var_slot),
        iterable: iterable_expr,
        body: Box::new(foreach_body),
    };
    let result = if retained_prefix.is_empty() {
        foreach_stmt
    } else {
        StructuredStmt::Sequence(vec![StructuredStmt::Basic(retained_prefix), foreach_stmt])
    };
    Some((result, 2))
}

fn match_iterator_foreach_prefix(prefix: &[Stmt]) -> Option<(u16, StructuredExpr, usize)> {
    let assign = prefix.last()?;
    let Stmt::Assign {
        target: StructuredExpr::Var(iterator_slot),
        value:
            StructuredExpr::Call {
                receiver: Some(iterable_expr),
                owner,
                name,
                descriptor,
                args,
                is_static: false,
            },
    } = assign
    else {
        return None;
    };
    if owner == "java/util/Iterator" || name != "iterator" || descriptor != "()Ljava/util/Iterator;" || !args.is_empty() {
        return None;
    }
    Some((*iterator_slot, *iterable_expr.clone(), 1))
}

fn peel_iterator_foreach_body(
    method: &LoadedMethod,
    body_items: &[StructuredStmt],
    iterator_slot: u16,
) -> Option<(u16, Type, StructuredStmt)> {
    let first = body_items.first()?;
    let StructuredStmt::Basic(first_stmts) = first else {
        return None;
    };
    let first_stmt = first_stmts.first()?;

    let (var_slot, var_type, head_consumed) = match first_stmt {
        Stmt::Assign {
            target: StructuredExpr::Var(slot),
            value:
                StructuredExpr::Call {
                    receiver: Some(receiver),
                    owner,
                    name,
                    descriptor,
                    args,
                    ..
                },
        } if matches!(&**receiver, StructuredExpr::Var(iter_slot) if *iter_slot == iterator_slot)
            && owner == "java/util/Iterator"
            && name == "next"
            && descriptor == "()Ljava/lang/Object;"
            && args.is_empty() =>
        {
            (*slot, Type::Object("java/lang/Object".to_string()), 1usize)
        }
        Stmt::Assign {
            target: StructuredExpr::Var(slot),
            value:
                StructuredExpr::Cast {
                    ty,
                    expr,
                },
        } if matches!(
            &**expr,
            StructuredExpr::Call {
                receiver: Some(receiver),
                owner,
                name,
                descriptor,
                args,
                ..
            } if matches!(&**receiver, StructuredExpr::Var(iter_slot) if *iter_slot == iterator_slot)
                && owner == "java/util/Iterator"
                && name == "next"
                && descriptor == "()Ljava/lang/Object;"
                && args.is_empty()
        ) =>
        {
            (*slot, ty.clone(), 1usize)
        }
        _ => return None,
    };

    let mut rebuilt = Vec::new();
    for (index, item) in body_items.iter().enumerate() {
        match item {
            StructuredStmt::Basic(stmts) if index == 0 => {
                let trimmed = stmts[head_consumed..].to_vec();
                if !trimmed.is_empty() {
                    rebuilt.push(StructuredStmt::Basic(trimmed));
                }
            }
            other => rebuilt.push(other.clone()),
        }
    }
    let _ = method;
    Some((var_slot, var_type, wrap_sequence(rebuilt)))
}

fn infer_expr_type_from_prefix(
    method: &LoadedMethod,
    prefix: &[Stmt],
    expr: &StructuredExpr,
) -> Option<Type> {
    match expr {
        StructuredExpr::Temp(id) => prefix
            .iter()
            .rev()
            .find_map(|stmt| match stmt {
                Stmt::TempAssign { id: temp_id, ty, value } if temp_id == id => {
                    ty.clone().or_else(|| infer_expr_type_from_prefix(method, prefix, value))
                }
                _ => None,
            }),
        StructuredExpr::Var(slot) => prefix
            .iter()
            .rev()
            .find_map(|stmt| match stmt {
                Stmt::Assign {
                    target: StructuredExpr::Var(target_slot),
                    value,
                } if target_slot == slot => infer_expr_type_from_prefix(method, prefix, value),
                _ => None,
            })
            .or_else(|| method.slot_type(*slot)),
        StructuredExpr::NewArray { element_type, .. } => {
            Some(Type::Array(Box::new(element_type.clone())))
        }
        StructuredExpr::ArrayAccess { array, .. } => infer_expr_type_from_prefix(method, prefix, array)
            .and_then(|ty| match ty {
                Type::Array(element) => Some(*element),
                _ => None,
            }),
        StructuredExpr::Field { descriptor, .. } => Some(descriptor.clone()),
        StructuredExpr::Call { descriptor, .. } => crate::types::parse_method_descriptor(descriptor)
            .ok()
            .map(|parsed| parsed.return_type),
        StructuredExpr::This => Some(Type::Object(method.name.clone())),
        StructuredExpr::Literal(Literal::String(_)) => Some(Type::Object("java/lang/String".to_string())),
        StructuredExpr::Literal(Literal::Int(_)) => Some(Type::Int),
        StructuredExpr::Literal(Literal::Long(_)) => Some(Type::Long),
        StructuredExpr::Literal(Literal::Float(_)) => Some(Type::Float),
        StructuredExpr::Literal(Literal::Double(_)) => Some(Type::Double),
        StructuredExpr::Literal(Literal::Boolean(_)) => Some(Type::Boolean),
        StructuredExpr::Literal(Literal::Char(_)) => Some(Type::Char),
        StructuredExpr::Literal(Literal::Null) => None,
        StructuredExpr::Literal(Literal::Class(_)) => Some(Type::Object("java/lang/Class".to_string())),
        StructuredExpr::StringConcat { .. } => Some(Type::Object("java/lang/String".to_string())),
        StructuredExpr::Cast { ty, .. } => Some(ty.clone()),
        StructuredExpr::New { class_name, .. } => Some(Type::Object(class_name.clone())),
        StructuredExpr::ArrayLength(_)
        | StructuredExpr::Binary { .. }
        | StructuredExpr::Unary { .. }
        | StructuredExpr::InstanceOf { .. }
        | StructuredExpr::CaughtException(_) => None,
    }
}

fn wrap_sequence(statements: Vec<StructuredStmt>) -> StructuredStmt {
    match statements.len() {
        0 => StructuredStmt::Empty,
        1 => statements.into_iter().next().unwrap_or(StructuredStmt::Empty),
        _ => StructuredStmt::Sequence(statements),
    }
}

fn lower_enum_switch(
    _class: &LoadedClass,
    _method: &LoadedMethod,
    expr: StructuredExpr,
    arms: Vec<SwitchArm>,
    resolver: Option<&ClassPathResolver>,
) -> Option<StructuredStmt> {
    let StructuredExpr::ArrayAccess { array, index } = expr else {
        return None;
    };
    let StructuredExpr::Field {
        target: None,
        owner: helper_owner,
        name: switchmap_field,
        is_static: true,
        ..
    } = *array
    else {
        return None;
    };
    let StructuredExpr::Call {
        receiver: Some(selector_expr),
        owner: enum_owner,
        name,
        descriptor,
        args,
        ..
    } = *index
    else {
        return None;
    };
    if name != "ordinal" || descriptor != "()I" || !args.is_empty() {
        return None;
    }

    let mapping = detect_enum_switch_map(resolver?, &helper_owner, &switchmap_field, &enum_owner)?;
    let lowered_arms = arms
        .into_iter()
        .map(|arm| {
            let mut labels = Vec::new();
            for label in arm.labels {
                match label {
                    SwitchLabel::Int(value) => {
                        if let Some(enum_label) = mapping.get(&value) {
                            labels.push(SwitchLabel::Enum(enum_label.clone()));
                        } else {
                            labels.push(SwitchLabel::Int(value));
                        }
                    }
                    other => labels.push(other),
                }
            }
            SwitchArm {
                labels,
                has_default: arm.has_default,
                body: arm.body,
            }
        })
        .collect::<Vec<_>>();

    Some(StructuredStmt::Switch {
        expr: *selector_expr,
        arms: lowered_arms,
    })
}

fn extract_string_selector(
    prefix: &[Stmt],
    first_switch_expr: &StructuredExpr,
) -> Option<Option<(u16, StructuredExpr)>> {
    let StructuredExpr::Call {
        receiver: Some(receiver),
        owner,
        name,
        descriptor,
        args,
        ..
    } = first_switch_expr
    else {
        return Some(None);
    };
    if owner != "java/lang/String" || name != "hashCode" || descriptor != "()I" || !args.is_empty()
    {
        return Some(None);
    }
    let StructuredExpr::Var(selector_slot) = &**receiver else {
        return Some(None);
    };

    for stmt in prefix {
        if let Stmt::Assign {
            target: StructuredExpr::Var(slot),
            value,
        } = stmt
            && *slot == *selector_slot
        {
            return Some(Some((*selector_slot, value.clone())));
        }
    }
    Some(Some((*selector_slot, StructuredExpr::Var(*selector_slot))))
}

fn is_string_switch_scaffolding(stmt: &Stmt, selector_slot: u16, discriminator_slot: u16) -> bool {
    match stmt {
        Stmt::Assign {
            target: StructuredExpr::Var(slot),
            ..
        } if *slot == selector_slot || *slot == discriminator_slot => true,
        _ => false,
    }
}

fn detect_string_switch_map(
    class: &LoadedClass,
    method: &LoadedMethod,
    selector_slot: u16,
    discriminator_slot: u16,
) -> HashMap<i32, String> {
    let mut mapping = HashMap::new();
    let insns = &method.instructions;
    for index in 0..insns.len().saturating_sub(5) {
        if !is_aload_of_slot(&insns[index], selector_slot) {
            continue;
        }
        let string = match extract_ldc_string(&class.constant_pool, &insns[index + 1]) {
            Some(value) => value,
            None => continue,
        };
        let equals = match resolve_method_ref(&class.constant_pool, &insns[index + 2]) {
            Ok(method_ref) => method_ref,
            Err(_) => continue,
        };
        if equals.owner != "java/lang/String"
            || equals.name != "equals"
            || equals.descriptor != "(Ljava/lang/Object;)Z"
        {
            continue;
        }
        if !matches!(
            &insns[index + 3],
            Insn::Jump(node) if node.insn.opcode == opcodes::IFEQ
        ) {
            continue;
        }
        let discriminator = match extract_int_constant(&class.constant_pool, &insns[index + 4]) {
            Some(value) => value,
            None => continue,
        };
        if !is_istore_of_slot(&insns[index + 5], discriminator_slot) {
            continue;
        }
        mapping.insert(discriminator, string);
    }
    mapping
}

fn detect_enum_switch_map(
    resolver: &ClassPathResolver,
    helper_owner: &str,
    switchmap_field: &str,
    enum_owner: &str,
) -> Option<HashMap<i32, String>> {
    let helper_class = resolver.load_class(helper_owner)?;
    let clinit = helper_class
        .methods
        .iter()
        .find(|method| method.name == "<clinit>")?;
    let mut mapping = HashMap::new();
    let insns = &clinit.instructions;
    for index in 0..insns.len().saturating_sub(4) {
        let first = match &insns[index] {
            Insn::Field(node) if node.insn.opcode == opcodes::GETSTATIC => {
                resolve_field_ref(&helper_class.constant_pool, &node.field_ref).ok()?
            }
            _ => continue,
        };
        if first.owner != helper_owner || first.name != switchmap_field {
            continue;
        }
        let second = match &insns[index + 1] {
            Insn::Field(node) if node.insn.opcode == opcodes::GETSTATIC => {
                resolve_field_ref(&helper_class.constant_pool, &node.field_ref).ok()?
            }
            _ => continue,
        };
        if second.owner != enum_owner {
            continue;
        }
        let ordinal = resolve_method_ref(&helper_class.constant_pool, &insns[index + 2]).ok()?;
        if ordinal.owner != enum_owner || ordinal.name != "ordinal" || ordinal.descriptor != "()I" {
            continue;
        }
        let case_value = extract_int_constant(&helper_class.constant_pool, &insns[index + 3])?;
        if !matches!(&insns[index + 4], Insn::Simple(node) if node.opcode == opcodes::IASTORE) {
            continue;
        }
        mapping.insert(case_value, second.name);
    }
    Some(mapping)
}

fn is_aload_of_slot(insn: &Insn, slot: u16) -> bool {
    match insn {
        Insn::Var(node) => node.insn.opcode == opcodes::ALOAD && node.var_index == slot,
        Insn::Simple(node) => match node.opcode {
            opcodes::ALOAD_0 => slot == 0,
            opcodes::ALOAD_1 => slot == 1,
            opcodes::ALOAD_2 => slot == 2,
            opcodes::ALOAD_3 => slot == 3,
            _ => false,
        },
        _ => false,
    }
}

fn is_istore_of_slot(insn: &Insn, slot: u16) -> bool {
    match insn {
        Insn::Var(node) => node.insn.opcode == opcodes::ISTORE && node.var_index == slot,
        Insn::Simple(node) => match node.opcode {
            opcodes::ISTORE_0 => slot == 0,
            opcodes::ISTORE_1 => slot == 1,
            opcodes::ISTORE_2 => slot == 2,
            opcodes::ISTORE_3 => slot == 3,
            _ => false,
        },
        _ => false,
    }
}

fn extract_ldc_string(cp: &[CpInfo], insn: &Insn) -> Option<String> {
    match insn {
        Insn::Ldc(node) => match &node.value {
            LdcValue::String(value) => Some(value.clone()),
            LdcValue::Index(_) => match resolve_ldc(cp, &node.value).ok()? {
                ResolvedConstant::String(value) => Some(value),
                _ => None,
            },
            _ => None,
        },
        _ => None,
    }
}

fn extract_int_constant(cp: &[CpInfo], insn: &Insn) -> Option<i32> {
    match insn {
        Insn::Int(node) => Some(node.operand),
        Insn::Ldc(node) => match resolve_ldc(cp, &node.value).ok()? {
            ResolvedConstant::Int(value) => Some(value),
            _ => None,
        },
        Insn::Simple(node) => match node.opcode {
            opcodes::ICONST_M1 => Some(-1),
            opcodes::ICONST_0 => Some(0),
            opcodes::ICONST_1 => Some(1),
            opcodes::ICONST_2 => Some(2),
            opcodes::ICONST_3 => Some(3),
            opcodes::ICONST_4 => Some(4),
            opcodes::ICONST_5 => Some(5),
            _ => None,
        },
        _ => None,
    }
}
