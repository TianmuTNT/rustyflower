use crate::bytecode::{ResolvedConstant, resolve_field_ref, resolve_ldc, resolve_method_ref};
use crate::expr::{Literal, Stmt, StructuredExpr};
use crate::loader::{LoadedClass, LoadedMethod, load_class};
use crate::structure::{StructuredStmt, SwitchArm, SwitchLabel};
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
        StructuredStmt::TryCatch { try_body, catches } => StructuredStmt::TryCatch {
            try_body: Box::new(lower_stmt(class, method, *try_body, resolver)),
            catches: catches
                .into_iter()
                .map(|catch| crate::structure::CatchArm {
                    catch_type: catch.catch_type,
                    catch_var: catch.catch_var,
                    body: Box::new(lower_stmt(class, method, *catch.body, resolver)),
                })
                .collect(),
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
    let second_switch = match &items[2] {
        StructuredStmt::Switch { expr, arms } => (expr, arms),
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

    let residual_prefix = prefix
        .iter()
        .filter(|stmt| !is_string_switch_scaffolding(stmt, selector_slot, discriminator_slot))
        .cloned()
        .collect::<Vec<_>>();

    let lowered_switch = StructuredStmt::Switch {
        expr: selector_expr,
        arms: lowered_arms,
    };
    let result = if residual_prefix.is_empty() {
        lowered_switch
    } else {
        StructuredStmt::Sequence(vec![StructuredStmt::Basic(residual_prefix), lowered_switch])
    };
    Some((result, 3))
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
        } if *slot == selector_slot => true,
        Stmt::Assign {
            target: StructuredExpr::Var(slot),
            value: StructuredExpr::Literal(Literal::Int(-1)),
        } if *slot == discriminator_slot => true,
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
