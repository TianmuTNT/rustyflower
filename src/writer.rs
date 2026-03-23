use crate::expr::{BinaryOp, Literal, Stmt, StructuredExpr, UnaryOp};
use crate::loader::{LoadedClass, LoadedConstant, LoadedField, LoadedMethod};
use crate::lowering::{ClassPathResolver, lower_switches};
use crate::structure::{StructuredStmt, SwitchLabel, decompile_method};
use crate::types::{default_value, format_internal_name, format_type, parse_method_descriptor};
use rust_asm::constants;
use rust_asm::insn::Insn;
use rust_asm::opcodes;
use rust_asm::types::Type;
use std::collections::{HashMap, HashSet};
use std::fmt::Write;

pub fn write_class(class: &LoadedClass, resolver: Option<&ClassPathResolver>) -> String {
    let mut out = String::new();
    if let Some(package_name) = &class.package_name {
        let _ = writeln!(out, "package {};", package_name);
        let _ = writeln!(out);
    }

    let _ = write!(
        out,
        "{}{}",
        class_modifiers(class.access_flags),
        class_keyword(class)
    );
    let _ = write!(out, " {}", class.simple_name);
    if let Some(super_name) = &class.super_name
        && super_name != "java/lang/Object"
        && class.access_flags & constants::ACC_INTERFACE == 0
    {
        let _ = write!(out, " extends {}", format_internal_name(super_name));
    }
    if !class.interfaces.is_empty() {
        let joiner = if class.access_flags & constants::ACC_INTERFACE != 0 {
            " extends "
        } else {
            " implements "
        };
        let rendered = class
            .interfaces
            .iter()
            .map(|name| format_internal_name(name))
            .collect::<Vec<_>>()
            .join(", ");
        let _ = write!(out, "{joiner}{rendered}");
    }
    let _ = writeln!(out, " {{");

    for field in &class.fields {
        let _ = writeln!(out, "    {}", write_field(field));
    }
    if !class.fields.is_empty() && !class.methods.is_empty() {
        let _ = writeln!(out);
    }

    for (index, method) in class.methods.iter().enumerate() {
        write_method(&mut out, class, method, resolver);
        if index + 1 != class.methods.len() {
            let _ = writeln!(out);
        }
    }

    let _ = writeln!(out, "}}");
    out
}

fn class_keyword(class: &LoadedClass) -> &'static str {
    if class.access_flags & constants::ACC_ANNOTATION != 0 {
        "@interface"
    } else if class.access_flags & constants::ACC_ENUM != 0 {
        "enum"
    } else if class.access_flags & constants::ACC_INTERFACE != 0 {
        "interface"
    } else {
        "class"
    }
}

fn class_modifiers(access_flags: u16) -> String {
    let mut parts = Vec::new();
    if access_flags & constants::ACC_PUBLIC != 0 {
        parts.push("public");
    }
    if access_flags & constants::ACC_ABSTRACT != 0
        && access_flags & constants::ACC_INTERFACE == 0
        && access_flags & constants::ACC_ENUM == 0
    {
        parts.push("abstract");
    }
    if access_flags & constants::ACC_FINAL != 0 && access_flags & constants::ACC_ENUM == 0 {
        parts.push("final");
    }
    if parts.is_empty() {
        String::new()
    } else {
        format!("{} ", parts.join(" "))
    }
}

fn member_modifiers(access_flags: u16) -> String {
    let mut parts = Vec::new();
    if access_flags & constants::ACC_PUBLIC != 0 {
        parts.push("public");
    } else if access_flags & constants::ACC_PROTECTED != 0 {
        parts.push("protected");
    } else if access_flags & constants::ACC_PRIVATE != 0 {
        parts.push("private");
    }
    if access_flags & constants::ACC_STATIC != 0 {
        parts.push("static");
    }
    if access_flags & constants::ACC_FINAL != 0 {
        parts.push("final");
    }
    if access_flags & constants::ACC_ABSTRACT != 0 {
        parts.push("abstract");
    }
    if access_flags & constants::ACC_NATIVE != 0 {
        parts.push("native");
    }
    if access_flags & constants::ACC_SYNCHRONIZED != 0 {
        parts.push("synchronized");
    }
    if access_flags & constants::ACC_STRICT != 0 {
        parts.push("strictfp");
    }
    if parts.is_empty() {
        String::new()
    } else {
        format!("{} ", parts.join(" "))
    }
}

fn write_field(field: &LoadedField) -> String {
    let mut out = String::new();
    let _ = write!(
        out,
        "{}{} {}",
        member_modifiers(field.access_flags),
        format_type(&field.descriptor),
        field.name
    );
    if let Some(value) = &field.constant_value {
        let _ = write!(out, " = {}", write_constant(value));
    }
    let _ = write!(out, ";");
    out
}

fn write_constant(value: &LoadedConstant) -> String {
    match value {
        LoadedConstant::Boolean(value) => value.to_string(),
        LoadedConstant::Char(value) => format!("{value:?}"),
        LoadedConstant::Int(value) => value.to_string(),
        LoadedConstant::Long(value) => format!("{value}L"),
        LoadedConstant::Float(value) => format!("{value}F"),
        LoadedConstant::Double(value) => value.to_string(),
        LoadedConstant::String(value) => format!("{value:?}"),
    }
}

fn write_method(
    out: &mut String,
    class: &LoadedClass,
    method: &LoadedMethod,
    resolver: Option<&ClassPathResolver>,
) {
    if method.name == "<clinit>" {
        let _ = writeln!(out, "    static {{");
        write_unsupported_body(out, &method.parsed_descriptor.return_type, None);
        let _ = writeln!(out, "    }}");
        return;
    }

    let mut header = String::new();
    let _ = write!(header, "    {}", member_modifiers(method.access_flags));
    if method.name == "<init>" {
        let _ = write!(header, "{}", class.simple_name);
    } else {
        let _ = write!(
            header,
            "{} {}",
            format_type(&method.parsed_descriptor.return_type),
            method.name
        );
    }
    let params = method
        .parameters
        .iter()
        .map(|parameter| format!("{} {}", format_type(&parameter.descriptor), parameter.name))
        .collect::<Vec<_>>()
        .join(", ");
    let _ = write!(header, "({params})");
    if !method.exceptions.is_empty() {
        let rendered = method
            .exceptions
            .iter()
            .map(|name| format_internal_name(name))
            .collect::<Vec<_>>()
            .join(", ");
        let _ = write!(header, " throws {rendered}");
    }
    if !method.has_code
        || method.access_flags & (constants::ACC_ABSTRACT | constants::ACC_NATIVE) != 0
    {
        let _ = writeln!(out, "{header};");
        return;
    }

    let _ = writeln!(out, "{header} {{");
    match decompile_method(class, method) {
        Ok(body) => {
            let body = lower_switches(class, method, body, resolver);
            if contains_legacy_subroutine(method) && contains_unresolved_artifacts(&body) {
                write_unsupported_body(out, &method.parsed_descriptor.return_type, None);
                let _ = writeln!(out, "    }}");
                return;
            }
            let mut ctx = MethodWriteContext::new(method);
            write_structured_stmt(out, &body, 2, &mut ctx);
        }
        Err(_error) => {
            write_unsupported_body(out, &method.parsed_descriptor.return_type, None);
        }
    }
    let _ = writeln!(out, "    }}");
}

fn contains_legacy_subroutine(method: &LoadedMethod) -> bool {
    method.instructions.iter().any(|insn| {
        matches!(
            insn,
            Insn::Jump(node) if matches!(node.insn.opcode, opcodes::JSR | opcodes::JSR_W)
        ) || matches!(insn, Insn::Var(node) if node.insn.opcode == opcodes::RET)
    })
}

fn contains_unresolved_artifacts(stmt: &StructuredStmt) -> bool {
    match stmt {
        StructuredStmt::Sequence(items) => items.iter().any(contains_unresolved_artifacts),
        StructuredStmt::Basic(stmts) => stmts.iter().any(stmt_has_unresolved_artifacts),
        StructuredStmt::Try {
            try_body,
            catches,
            finally_body,
        } => {
            contains_unresolved_artifacts(try_body)
                || catches
                    .iter()
                    .any(|catch| contains_unresolved_artifacts(&catch.body))
                || finally_body
                    .as_ref()
                    .is_some_and(|body| contains_unresolved_artifacts(body))
        }
        StructuredStmt::Synchronized { expr, body } => {
            expr_has_unresolved_artifacts(expr) || contains_unresolved_artifacts(body)
        }
        StructuredStmt::Switch { expr, arms } => {
            expr_has_unresolved_artifacts(expr)
                || arms
                    .iter()
                    .any(|arm| contains_unresolved_artifacts(&arm.body))
        }
        StructuredStmt::If {
            condition,
            then_branch,
            else_branch,
        } => {
            expr_has_unresolved_artifacts(condition)
                || contains_unresolved_artifacts(then_branch)
                || else_branch
                    .as_ref()
                    .is_some_and(|branch| contains_unresolved_artifacts(branch))
        }
        StructuredStmt::While { condition, body } => {
            expr_has_unresolved_artifacts(condition) || contains_unresolved_artifacts(body)
        }
        StructuredStmt::Comment(_) => true,
        StructuredStmt::Empty => false,
    }
}

fn stmt_has_unresolved_artifacts(stmt: &Stmt) -> bool {
    match stmt {
        Stmt::Assign { target, value } => {
            expr_has_unresolved_artifacts(target) || expr_has_unresolved_artifacts(value)
        }
        Stmt::TempAssign { value, .. } => expr_has_unresolved_artifacts(value),
        Stmt::Expr(expr) | Stmt::Throw(expr) | Stmt::MonitorEnter(expr) | Stmt::MonitorExit(expr) => {
            matches!(stmt, Stmt::MonitorEnter(_) | Stmt::MonitorExit(_))
                || expr_has_unresolved_artifacts(expr)
        }
        Stmt::Return(Some(expr)) => expr_has_unresolved_artifacts(expr),
        Stmt::Return(None) | Stmt::Break => false,
        Stmt::ConstructorCall { args, .. } => args.iter().any(expr_has_unresolved_artifacts),
        Stmt::Comment(_) => true,
    }
}

fn expr_has_unresolved_artifacts(expr: &StructuredExpr) -> bool {
    match expr {
        StructuredExpr::CaughtException(_) => true,
        StructuredExpr::Field { target, .. } => target
            .as_ref()
            .is_some_and(|target| expr_has_unresolved_artifacts(target)),
        StructuredExpr::ArrayAccess { array, index } => {
            expr_has_unresolved_artifacts(array) || expr_has_unresolved_artifacts(index)
        }
        StructuredExpr::ArrayLength(expr)
        | StructuredExpr::Unary { expr, .. }
        | StructuredExpr::Cast { expr, .. }
        | StructuredExpr::InstanceOf { expr, .. } => expr_has_unresolved_artifacts(expr),
        StructuredExpr::Binary { left, right, .. } => {
            expr_has_unresolved_artifacts(left) || expr_has_unresolved_artifacts(right)
        }
        StructuredExpr::Call { receiver, args, .. } => {
            receiver
                .as_ref()
                .is_some_and(|receiver| expr_has_unresolved_artifacts(receiver))
                || args.iter().any(expr_has_unresolved_artifacts)
        }
        StructuredExpr::New { args, .. } => args.iter().any(expr_has_unresolved_artifacts),
        StructuredExpr::NewArray { size, .. } => expr_has_unresolved_artifacts(size),
        StructuredExpr::This
        | StructuredExpr::Var(_)
        | StructuredExpr::Temp(_)
        | StructuredExpr::Literal(_) => false,
    }
}

fn write_unsupported_body(out: &mut String, return_type: &Type, reason: Option<&str>) {
    let _ = writeln!(
        out,
        "        /* rustyflower: method body decompilation is being implemented incrementally.{} */",
        reason
            .map(|reason| format!(" reason: {reason}"))
            .unwrap_or_default()
    );
    if !matches!(return_type, Type::Void) {
        let _ = writeln!(out, "        return {};", default_value(return_type));
    }
}

struct MethodWriteContext<'a> {
    method: &'a LoadedMethod,
    declared_slots: HashSet<u16>,
    declared_temps: HashSet<u32>,
    temp_types: HashMap<u32, Type>,
}

impl<'a> MethodWriteContext<'a> {
    fn new(method: &'a LoadedMethod) -> Self {
        let declared_slots = method
            .parameters
            .iter()
            .map(|parameter| parameter.slot)
            .collect::<HashSet<_>>();
        Self {
            method,
            declared_slots,
            declared_temps: HashSet::new(),
            temp_types: HashMap::new(),
        }
    }
}

fn write_structured_stmt(
    out: &mut String,
    stmt: &StructuredStmt,
    indent: usize,
    ctx: &mut MethodWriteContext<'_>,
) {
    match stmt {
        StructuredStmt::Sequence(statements) => {
            for statement in statements {
                write_structured_stmt(out, statement, indent, ctx);
            }
        }
        StructuredStmt::Basic(statements) => {
            for statement in statements {
                write_stmt(out, statement, indent, ctx);
            }
        }
        StructuredStmt::Try {
            try_body,
            catches,
            finally_body,
        } => {
            let pad = "    ".repeat(indent);
            let _ = writeln!(out, "{}try {{", pad);
            write_structured_stmt(out, try_body, indent + 1, ctx);
            let _ = writeln!(out, "{}}}", pad);
            for catch in catches {
                let _ = writeln!(
                    out,
                    "{}catch ({} {}) {{",
                    pad,
                    format_internal_name(&catch.catch_type),
                    catch.catch_var
                );
                write_structured_stmt(out, &catch.body, indent + 1, ctx);
                let _ = writeln!(out, "{}}}", pad);
            }
            if let Some(finally_body) = finally_body {
                let _ = writeln!(out, "{}finally {{", pad);
                write_structured_stmt(out, finally_body, indent + 1, ctx);
                let _ = writeln!(out, "{}}}", pad);
            }
        }
        StructuredStmt::Synchronized { expr, body } => {
            let pad = "    ".repeat(indent);
            let _ = writeln!(out, "{}synchronized ({}) {{", pad, render_expr(expr, ctx));
            write_structured_stmt(out, body, indent + 1, ctx);
            let _ = writeln!(out, "{}}}", pad);
        }
        StructuredStmt::Switch { expr, arms } => {
            let pad = "    ".repeat(indent);
            let _ = writeln!(out, "{}switch ({}) {{", pad, render_expr(expr, ctx));
            for arm in arms {
                for label in &arm.labels {
                    let _ = writeln!(
                        out,
                        "{}case {}:",
                        "    ".repeat(indent + 1),
                        render_switch_label(label)
                    );
                }
                if arm.has_default {
                    let _ = writeln!(out, "{}default:", "    ".repeat(indent + 1));
                }
                write_structured_stmt(out, &arm.body, indent + 2, ctx);
            }
            let _ = writeln!(out, "{}}}", pad);
        }
        StructuredStmt::If {
            condition,
            then_branch,
            else_branch,
        } => {
            let pad = "    ".repeat(indent);
            let _ = writeln!(out, "{}if ({}) {{", pad, render_expr(condition, ctx));
            write_structured_stmt(out, then_branch, indent + 1, ctx);
            if let Some(else_branch) = else_branch {
                let _ = writeln!(out, "{}}} else {{", pad);
                write_structured_stmt(out, else_branch, indent + 1, ctx);
            }
            let _ = writeln!(out, "{}}}", pad);
        }
        StructuredStmt::While { condition, body } => {
            let pad = "    ".repeat(indent);
            let _ = writeln!(out, "{}while ({}) {{", pad, render_expr(condition, ctx));
            write_structured_stmt(out, body, indent + 1, ctx);
            let _ = writeln!(out, "{}}}", pad);
        }
        StructuredStmt::Comment(message) => {
            let _ = writeln!(out, "{}/* {message} */", "    ".repeat(indent));
        }
        StructuredStmt::Empty => {}
    }
}

fn render_switch_label(label: &SwitchLabel) -> String {
    match label {
        SwitchLabel::Int(value) => value.to_string(),
        SwitchLabel::String(value) => format!("{value:?}"),
        SwitchLabel::Enum(value) => value.clone(),
    }
}

fn write_stmt(out: &mut String, stmt: &Stmt, indent: usize, ctx: &mut MethodWriteContext<'_>) {
    let pad = "    ".repeat(indent);
    match stmt {
        Stmt::Assign { target, value } => {
            if let StructuredExpr::Var(slot) = target {
                if !ctx.declared_slots.contains(slot) {
                    ctx.declared_slots.insert(*slot);
                    let ty = ctx
                        .method
                        .slot_type(*slot)
                        .or_else(|| infer_expr_type(value, ctx))
                        .unwrap_or(Type::Object("java/lang/Object".to_string()));
                    let _ = writeln!(
                        out,
                        "{}{} {} = {};",
                        pad,
                        format_type(&ty),
                        ctx.method.slot_name(*slot),
                        render_expr(value, ctx)
                    );
                    return;
                }
            }
            let _ = writeln!(
                out,
                "{}{} = {};",
                pad,
                render_expr(target, ctx),
                render_expr(value, ctx)
            );
        }
        Stmt::TempAssign { id, ty, value } => {
            let actual_type = ty
                .clone()
                .or_else(|| infer_expr_type(value, ctx))
                .unwrap_or(Type::Object("java/lang/Object".to_string()));
            ctx.temp_types.insert(*id, actual_type.clone());
            let _ = writeln!(
                out,
                "{}{} tmp{} = {};",
                pad,
                format_type(&actual_type),
                id,
                render_expr(value, ctx)
            );
            ctx.declared_temps.insert(*id);
        }
        Stmt::Expr(expr) => {
            let _ = writeln!(out, "{}{};", pad, render_expr(expr, ctx));
        }
        Stmt::MonitorEnter(expr) => {
            let _ = writeln!(
                out,
                "{}/* rustyflower: monitorenter {} */",
                pad,
                render_expr(expr, ctx)
            );
        }
        Stmt::MonitorExit(expr) => {
            let _ = writeln!(
                out,
                "{}/* rustyflower: monitorexit {} */",
                pad,
                render_expr(expr, ctx)
            );
        }
        Stmt::Break => {
            let _ = writeln!(out, "{}break;", pad);
        }
        Stmt::Return(value) => {
            if let Some(value) = value {
                let _ = writeln!(out, "{}return {};", pad, render_expr(value, ctx));
            } else {
                let _ = writeln!(out, "{}return;", pad);
            }
        }
        Stmt::Throw(value) => {
            let _ = writeln!(out, "{}throw {};", pad, render_expr(value, ctx));
        }
        Stmt::ConstructorCall { is_super, args } => {
            let rendered_args = args
                .iter()
                .map(|arg| render_expr(arg, ctx))
                .collect::<Vec<_>>()
                .join(", ");
            let _ = writeln!(
                out,
                "{}{}({});",
                pad,
                if *is_super { "super" } else { "this" },
                rendered_args
            );
        }
        Stmt::Comment(message) => {
            let _ = writeln!(out, "{}/* {} */", pad, message);
        }
    }
}

fn render_expr(expr: &StructuredExpr, ctx: &MethodWriteContext<'_>) -> String {
    match expr {
        StructuredExpr::This => "this".to_string(),
        StructuredExpr::Var(slot) => ctx.method.slot_name(*slot),
        StructuredExpr::Temp(id) => format!("tmp{id}"),
        StructuredExpr::CaughtException(_) => "<caught-exception>".to_string(),
        StructuredExpr::Literal(literal) => render_literal(literal),
        StructuredExpr::Field {
            target,
            owner,
            name,
            is_static,
            ..
        } => {
            if *is_static {
                format!("{}.{}", format_internal_name(owner), name)
            } else {
                format!(
                    "{}.{}",
                    target
                        .as_ref()
                        .map(|expr| render_expr(expr, ctx))
                        .unwrap_or_else(|| "this".to_string()),
                    name
                )
            }
        }
        StructuredExpr::ArrayAccess { array, index } => {
            format!("{}[{}]", render_expr(array, ctx), render_expr(index, ctx))
        }
        StructuredExpr::ArrayLength(expr) => format!("{}.length", render_expr(expr, ctx)),
        StructuredExpr::Binary { op, left, right } => format!(
            "({} {} {})",
            render_expr(left, ctx),
            render_binary_op(*op),
            render_expr(right, ctx)
        ),
        StructuredExpr::Unary { op, expr } => match op {
            UnaryOp::Neg => format!("-{}", render_expr(expr, ctx)),
            UnaryOp::Not => format!("!{}", render_expr(expr, ctx)),
        },
        StructuredExpr::Call {
            receiver,
            owner,
            name,
            args,
            is_static,
            ..
        } => {
            let rendered_args = args
                .iter()
                .map(|arg| render_expr(arg, ctx))
                .collect::<Vec<_>>()
                .join(", ");
            if *is_static {
                format!("{}.{}({rendered_args})", format_internal_name(owner), name)
            } else {
                format!(
                    "{}.{}({rendered_args})",
                    receiver
                        .as_ref()
                        .map(|expr| render_expr(expr, ctx))
                        .unwrap_or_else(|| "this".to_string()),
                    name
                )
            }
        }
        StructuredExpr::New { class_name, args } => {
            let rendered_args = args
                .iter()
                .map(|arg| render_expr(arg, ctx))
                .collect::<Vec<_>>()
                .join(", ");
            format!("new {}({rendered_args})", format_internal_name(class_name))
        }
        StructuredExpr::NewArray { element_type, size } => format!(
            "new {}[{}]",
            format_type(element_type),
            render_expr(size, ctx)
        ),
        StructuredExpr::Cast { ty, expr } => {
            format!("(({}) {})", format_type(ty), render_expr(expr, ctx))
        }
        StructuredExpr::InstanceOf { expr, ty } => {
            format!(
                "({} instanceof {})",
                render_expr(expr, ctx),
                format_type(ty)
            )
        }
    }
}

fn render_literal(literal: &Literal) -> String {
    match literal {
        Literal::Null => "null".to_string(),
        Literal::Boolean(value) => value.to_string(),
        Literal::Char(value) => format!("{value:?}"),
        Literal::Int(value) => value.to_string(),
        Literal::Long(value) => format!("{value}L"),
        Literal::Float(value) => format!("{value}F"),
        Literal::Double(value) => value.to_string(),
        Literal::String(value) => format!("{value:?}"),
        Literal::Class(ty) => format!("{}.class", format_type(ty)),
    }
}

fn render_binary_op(op: BinaryOp) -> &'static str {
    match op {
        BinaryOp::Add => "+",
        BinaryOp::Sub => "-",
        BinaryOp::Mul => "*",
        BinaryOp::Div => "/",
        BinaryOp::Rem => "%",
        BinaryOp::Shl => "<<",
        BinaryOp::Shr => ">>",
        BinaryOp::Ushr => ">>>",
        BinaryOp::And => "&",
        BinaryOp::Or => "|",
        BinaryOp::Xor => "^",
        BinaryOp::Eq => "==",
        BinaryOp::Ne => "!=",
        BinaryOp::Lt => "<",
        BinaryOp::Le => "<=",
        BinaryOp::Gt => ">",
        BinaryOp::Ge => ">=",
    }
}

fn infer_expr_type(expr: &StructuredExpr, ctx: &MethodWriteContext<'_>) -> Option<Type> {
    match expr {
        StructuredExpr::This => None,
        StructuredExpr::Var(slot) => ctx.method.slot_type(*slot),
        StructuredExpr::Temp(id) => ctx.temp_types.get(id).cloned(),
        StructuredExpr::CaughtException(ty) => ty.clone(),
        StructuredExpr::Literal(literal) => Some(match literal {
            Literal::Null => return None,
            Literal::Boolean(_) => Type::Boolean,
            Literal::Char(_) => Type::Char,
            Literal::Int(_) => Type::Int,
            Literal::Long(_) => Type::Long,
            Literal::Float(_) => Type::Float,
            Literal::Double(_) => Type::Double,
            Literal::String(_) => Type::Object("java/lang/String".to_string()),
            Literal::Class(_) => Type::Object("java/lang/Class".to_string()),
        }),
        StructuredExpr::Field { descriptor, .. } => Some(descriptor.clone()),
        StructuredExpr::ArrayAccess { .. } => None,
        StructuredExpr::ArrayLength(_) => Some(Type::Int),
        StructuredExpr::Binary { op, left, right } => Some(match op {
            BinaryOp::Eq
            | BinaryOp::Ne
            | BinaryOp::Lt
            | BinaryOp::Le
            | BinaryOp::Gt
            | BinaryOp::Ge => Type::Boolean,
            _ => infer_expr_type(left, ctx)
                .or_else(|| infer_expr_type(right, ctx))
                .unwrap_or(Type::Int),
        }),
        StructuredExpr::Unary { op, expr } => Some(match op {
            UnaryOp::Not => Type::Boolean,
            UnaryOp::Neg => infer_expr_type(expr, ctx).unwrap_or(Type::Int),
        }),
        StructuredExpr::Call { descriptor, .. } => parse_method_descriptor(descriptor)
            .ok()
            .map(|descriptor| descriptor.return_type),
        StructuredExpr::New { class_name, .. } => Some(Type::Object(class_name.clone())),
        StructuredExpr::NewArray { element_type, .. } => {
            Some(Type::Array(Box::new(element_type.clone())))
        }
        StructuredExpr::Cast { ty, .. } => Some(ty.clone()),
        StructuredExpr::InstanceOf { .. } => Some(Type::Boolean),
    }
}
