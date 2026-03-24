use crate::expr::{BinaryOp, Literal, Stmt, StringConcatPart, StructuredExpr, UnaryOp};
use crate::loader::{LoadedClass, LoadedConstant, LoadedField, LoadedMethod};
use crate::lowering::{ClassPathResolver, lower_switches};
use crate::structure::{
    StructuredStmt, SwitchLabel, TryResource, decompile_expression_fallback,
    decompile_method, decompile_simple_exception_fallback, rewrite_control_flow,
};
use crate::types::{
    default_value, format_internal_name, format_signature_type, format_type,
    parse_method_descriptor,
};
use rust_asm::constants;
use rust_asm::signature::{SignatureType, TypeParameter};
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
    write_class_declaration(&mut out, class, resolver, 0);
    out
}

fn write_class_declaration(
    out: &mut String,
    class: &LoadedClass,
    resolver: Option<&ClassPathResolver>,
    indent: usize,
) {
    let pad = "    ".repeat(indent);
    let _ = write!(
        out,
        "{}{}{}",
        pad,
        class_modifiers(class.access_flags),
        class_keyword(class)
    );
    let _ = write!(out, " {}", class_source_name(class));
    if let Some(signature) = &class.parsed_signature {
        let rendered_params = render_type_parameters(&signature.type_parameters);
        if !rendered_params.is_empty() {
            let _ = write!(out, "{rendered_params}");
        }
        if signature.super_class.internal_name() != "java/lang/Object"
            && class.access_flags & constants::ACC_INTERFACE == 0
        {
            let _ = write!(
                out,
                " extends {}",
                format_signature_type(&SignatureType::Class(signature.super_class.clone()))
            );
        }
        if !signature.interfaces.is_empty() {
            let joiner = if class.access_flags & constants::ACC_INTERFACE != 0 {
                " extends "
            } else {
                " implements "
            };
            let rendered = signature
                .interfaces
                .iter()
                .cloned()
                .map(SignatureType::Class)
                .map(|ty| format_signature_type(&ty))
                .collect::<Vec<_>>()
                .join(", ");
            let _ = write!(out, "{joiner}{rendered}");
        }
    } else {
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
    }
    let _ = writeln!(out, " {{");

    let visible_fields = class
        .fields
        .iter()
        .filter(|field| !is_hidden_field(field))
        .collect::<Vec<_>>();
    for field in &visible_fields {
        let _ = writeln!(out, "{}    {}", pad, write_field(field));
    }
    let visible_methods = class
        .methods
        .iter()
        .filter(|method| !is_hidden_method(class, method))
        .collect::<Vec<_>>();
    let nested_classes = member_nested_classes(class, resolver);
    if !visible_fields.is_empty() && (!visible_methods.is_empty() || !nested_classes.is_empty()) {
        let _ = writeln!(out);
    }

    let mut methods_out = String::new();
    for (index, method) in visible_methods.iter().enumerate() {
        write_method(&mut methods_out, class, method, resolver, indent + 1);
        if index + 1 != visible_methods.len() {
            let _ = writeln!(methods_out);
        }
    }
    let required_helper_methods = class
        .methods
        .iter()
        .filter(|method| method.name.starts_with("lambda$"))
        .filter(|method| {
            methods_out.contains(&format!("{}(", render_synthetic_lambda_method_name(&method.name)))
        })
        .collect::<Vec<_>>();
    if !methods_out.is_empty() {
        let _ = write!(out, "{methods_out}");
    }
    if !required_helper_methods.is_empty() {
        if !methods_out.is_empty() {
            let _ = writeln!(out);
        }
        for (index, method) in required_helper_methods.iter().enumerate() {
            write_method(out, class, method, resolver, indent + 1);
            if index + 1 != required_helper_methods.len() || !nested_classes.is_empty() {
                let _ = writeln!(out);
            }
        }
    } else if !methods_out.is_empty() && !nested_classes.is_empty() {
        let _ = writeln!(out);
    }

    for (index, nested) in nested_classes.iter().enumerate() {
        write_class_declaration(out, nested, resolver, indent + 1);
        if index + 1 != nested_classes.len() {
            let _ = writeln!(out);
        }
    }

    let _ = writeln!(out, "{}}}", pad);
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
    } else if access_flags & constants::ACC_PROTECTED != 0 {
        parts.push("protected");
    } else if access_flags & constants::ACC_PRIVATE != 0 {
        parts.push("private");
    }
    if access_flags & constants::ACC_STATIC != 0 {
        parts.push("static");
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
        field.parsed_signature
            .as_ref()
            .map(format_signature_type)
            .unwrap_or_else(|| format_type(&field.descriptor)),
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
    indent: usize,
) {
    let pad = "    ".repeat(indent);
    let header = if method.name == "<clinit>" {
        format!("{pad}static")
    } else {
        let mut header = String::new();
        let _ = write!(header, "{pad}{}", member_modifiers(method.access_flags));
        if let Some(signature) = &method.parsed_signature {
            let rendered = render_type_parameters(&signature.type_parameters);
            if !rendered.is_empty() {
                let _ = write!(header, "{rendered} ");
            }
        }
        if method.name == "<init>" {
            let _ = write!(header, "{}", class_source_name(class));
        } else {
            let return_type = method
                .parsed_signature
                .as_ref()
                .map(|signature| format_signature_type(&signature.return_type))
                .unwrap_or_else(|| {
                    render_type_for_site(
                        &method.parsed_descriptor.return_type,
                        class,
                        resolver,
                        Some(method),
                    )
                });
            let _ = write!(header, "{} {}", return_type, method_source_name(method));
        }
        let params = render_method_parameters(class, method, resolver);
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
        header
    };
    if method.name != "<clinit>"
        && (!method.has_code
            || method.access_flags & (constants::ACC_ABSTRACT | constants::ACC_NATIVE) != 0)
    {
        let _ = writeln!(out, "{header};");
        return;
    }

    let _ = writeln!(out, "{header} {{");
    match decompile_method(class, method) {
        Ok(body) => {
            let body = rewrite_control_flow(lower_switches(class, method, body, resolver));
            if contains_legacy_subroutine(method) && contains_unresolved_artifacts(&body) {
                write_unsupported_body(out, &method.parsed_descriptor.return_type, indent + 1, None);
                let _ = writeln!(out, "{pad}}}");
                return;
            }
            let mut ctx = MethodWriteContext::new(class, method, resolver);
            let local_classes = local_nested_classes(class, method, resolver);
            if !local_classes.is_empty() {
                for (index, local_class) in local_classes.iter().enumerate() {
                    write_class_declaration(out, local_class, resolver, indent + 1);
                    if index + 1 != local_classes.len() || !matches!(body, StructuredStmt::Empty) {
                        let _ = writeln!(out);
                    }
                }
            }
            write_structured_stmt(out, &body, indent + 1, &mut ctx);
        }
        Err(_error) => {
            if let Ok(Some(body)) = decompile_expression_fallback(class, method) {
                let body = rewrite_control_flow(body);
                let mut ctx = MethodWriteContext::new(class, method, resolver);
                write_structured_stmt(out, &body, indent + 1, &mut ctx);
            } else if let Ok(Some(body)) = decompile_simple_exception_fallback(class, method) {
                let body = rewrite_control_flow(lower_switches(class, method, body, resolver));
                let mut ctx = MethodWriteContext::new(class, method, resolver);
                write_structured_stmt(out, &body, indent + 1, &mut ctx);
            } else {
                write_unsupported_body(out, &method.parsed_descriptor.return_type, indent + 1, None);
            }
        }
    }
    let _ = writeln!(out, "{pad}}}");
}

fn render_method_parameters(
    class: &LoadedClass,
    method: &LoadedMethod,
    resolver: Option<&ClassPathResolver>,
) -> String {
    let parameter_types = method
        .parsed_signature
        .as_ref()
        .map(|signature| signature.parameter_types.as_slice());
    let skip_count = synthetic_constructor_parameter_count(class, method);
    method
        .parameters
        .iter()
        .enumerate()
        .skip(skip_count)
        .map(|(index, parameter)| {
            let ty = parameter_types
                .and_then(|types| types.get(index))
                .map(format_signature_type)
                .unwrap_or_else(|| render_type_for_site(&parameter.descriptor, class, resolver, Some(method)));
            format!("{ty} {}", parameter.name)
        })
        .collect::<Vec<_>>()
        .join(", ")
}

fn render_type_parameters(parameters: &[TypeParameter]) -> String {
    if parameters.is_empty() {
        return String::new();
    }
    format!(
        "<{}>",
        parameters
            .iter()
            .map(render_type_parameter)
            .collect::<Vec<_>>()
            .join(", ")
    )
}

fn render_type_parameter(parameter: &TypeParameter) -> String {
    let mut bounds = Vec::new();
    if let Some(bound) = &parameter.class_bound
        && !matches!(bound, SignatureType::Class(class) if class.internal_name() == "java/lang/Object")
    {
        bounds.push(format_signature_type(bound));
    }
    bounds.extend(
        parameter
            .interface_bounds
            .iter()
            .map(format_signature_type),
    );
    if bounds.is_empty() {
        parameter.name.clone()
    } else {
        format!("{} extends {}", parameter.name, bounds.join(" & "))
    }
}

fn synthetic_constructor_parameter_count(class: &LoadedClass, method: &LoadedMethod) -> usize {
    if method.name == "<init>"
        && class.outer_class.is_some()
        && class.access_flags & constants::ACC_STATIC == 0
    {
        return 1;
    }
    0
}

fn is_hidden_field(field: &LoadedField) -> bool {
    field.name.starts_with("this$")
        || field.name.starts_with("val$")
}

fn is_hidden_method(class: &LoadedClass, method: &LoadedMethod) -> bool {
    let _ = class;
    method.name.starts_with("lambda$")
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
        StructuredStmt::TryWithResources {
            resources,
            body,
            catches,
        } => {
            resources
                .iter()
                .any(|resource| expr_has_unresolved_artifacts(&resource.initializer))
                || contains_unresolved_artifacts(body)
                || catches
                    .iter()
                    .any(|catch| contains_unresolved_artifacts(&catch.body))
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
        StructuredStmt::DoWhile { condition, body } => {
            expr_has_unresolved_artifacts(condition) || contains_unresolved_artifacts(body)
        }
        StructuredStmt::For {
            init,
            condition,
            update,
            body,
        } => {
            init.iter().any(stmt_has_unresolved_artifacts)
                || expr_has_unresolved_artifacts(condition)
                || update.iter().any(stmt_has_unresolved_artifacts)
                || contains_unresolved_artifacts(body)
        }
        StructuredStmt::ForEach {
            iterable, body, ..
        } => expr_has_unresolved_artifacts(iterable) || contains_unresolved_artifacts(body),
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
        Stmt::Return(None) | Stmt::Break | Stmt::Continue => false,
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
        StructuredExpr::StringConcat { parts } => parts.iter().any(|part| match part {
            StringConcatPart::Literal(_) => false,
            StringConcatPart::Expr(expr) => expr_has_unresolved_artifacts(expr),
        }),
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
        StructuredExpr::Ternary {
            condition,
            then_expr,
            else_expr,
        } => {
            expr_has_unresolved_artifacts(condition)
                || expr_has_unresolved_artifacts(then_expr)
                || expr_has_unresolved_artifacts(else_expr)
        }
        StructuredExpr::Call { receiver, args, .. } => {
            receiver
                .as_ref()
                .is_some_and(|receiver| expr_has_unresolved_artifacts(receiver))
                || args.iter().any(expr_has_unresolved_artifacts)
        }
        StructuredExpr::Lambda { captured_args, .. } => {
            captured_args.iter().any(expr_has_unresolved_artifacts)
        }
        StructuredExpr::MethodReference { receiver, .. } => receiver
            .as_ref()
            .is_some_and(|receiver| expr_has_unresolved_artifacts(receiver)),
        StructuredExpr::New { args, .. } => args.iter().any(expr_has_unresolved_artifacts),
        StructuredExpr::NewArray { size, .. } => expr_has_unresolved_artifacts(size),
        StructuredExpr::This
        | StructuredExpr::Var(_)
        | StructuredExpr::Temp(_)
        | StructuredExpr::Literal(_) => false,
    }
}

fn write_unsupported_body(
    out: &mut String,
    return_type: &Type,
    indent: usize,
    reason: Option<&str>,
) {
    let pad = "    ".repeat(indent);
    let _ = writeln!(
        out,
        "{}/* rustyflower: method body decompilation is being implemented incrementally.{} */",
        pad,
        reason
            .map(|reason| format!(" reason: {reason}"))
            .unwrap_or_default()
    );
    if !matches!(return_type, Type::Void) {
        let _ = writeln!(out, "{}return {};", pad, default_value(return_type));
    }
}

struct MethodWriteContext<'a> {
    class: &'a LoadedClass,
    method: &'a LoadedMethod,
    resolver: Option<&'a ClassPathResolver>,
    declared_slots: HashSet<u16>,
    declared_temps: HashSet<u32>,
    temp_types: HashMap<u32, Type>,
    slot_types: HashMap<u16, Type>,
    slot_overrides: HashMap<u16, String>,
    this_override: Option<String>,
}

impl<'a> MethodWriteContext<'a> {
    fn new(
        class: &'a LoadedClass,
        method: &'a LoadedMethod,
        resolver: Option<&'a ClassPathResolver>,
    ) -> Self {
        let declared_slots = method
            .parameters
            .iter()
            .map(|parameter| parameter.slot)
            .collect::<HashSet<_>>();
        let slot_types = method
            .parameters
            .iter()
            .map(|parameter| (parameter.slot, parameter.descriptor.clone()))
            .collect::<HashMap<_, _>>();
        Self::with_overrides(
            class,
            method,
            resolver,
            declared_slots,
            slot_types,
            HashMap::new(),
            None,
        )
    }

    fn with_overrides(
        class: &'a LoadedClass,
        method: &'a LoadedMethod,
        resolver: Option<&'a ClassPathResolver>,
        mut declared_slots: HashSet<u16>,
        slot_types: HashMap<u16, Type>,
        slot_overrides: HashMap<u16, String>,
        this_override: Option<String>,
    ) -> Self {
        declared_slots.extend(slot_overrides.keys().copied());
        Self {
            class,
            method,
            resolver,
            declared_slots,
            declared_temps: HashSet::new(),
            temp_types: HashMap::new(),
            slot_types,
            slot_overrides,
            this_override,
        }
    }
}

fn class_source_name(class: &LoadedClass) -> String {
    class
        .inner_classes
        .iter()
        .find(|entry| entry.name == class.internal_name)
        .and_then(|entry| entry.inner_name.clone())
        .unwrap_or_else(|| class.simple_name.clone())
}

fn method_source_name(method: &LoadedMethod) -> String {
    if method.name.starts_with("lambda$") {
        render_synthetic_lambda_method_name(&method.name)
    } else {
        method.name.clone()
    }
}

fn render_synthetic_lambda_method_name(name: &str) -> String {
    name.replace("lambda$", "lambdaImpl_").replace('$', "_")
}

fn member_nested_classes(
    class: &LoadedClass,
    resolver: Option<&ClassPathResolver>,
) -> Vec<LoadedClass> {
    let Some(resolver) = resolver else {
        return Vec::new();
    };
    let mut nested = class
        .inner_classes
        .iter()
        .filter(|entry| entry.outer_name.as_deref() == Some(class.internal_name.as_str()))
        .filter(|entry| entry.access_flags & constants::ACC_SYNTHETIC == 0)
        .filter(|entry| {
            entry.inner_name.as_ref().is_some_and(|name| {
                name.chars()
                    .next()
                    .is_some_and(|ch| !ch.is_ascii_digit())
            })
        })
        .filter_map(|entry| resolver.load_class(&entry.name))
        .filter(|nested| nested.enclosing_method.is_none())
        .collect::<Vec<_>>();
    nested.sort_by(|left, right| left.internal_name.cmp(&right.internal_name));
    nested
}

fn local_nested_classes(
    class: &LoadedClass,
    method: &LoadedMethod,
    resolver: Option<&ClassPathResolver>,
) -> Vec<LoadedClass> {
    let Some(resolver) = resolver else {
        return Vec::new();
    };
    let mut nested = class
        .inner_classes
        .iter()
        .filter(|entry| entry.access_flags & constants::ACC_SYNTHETIC == 0)
        .filter(|entry| entry.name != class.internal_name)
        .filter_map(|entry| resolver.load_class(&entry.name))
        .filter(|nested| {
            nested.enclosing_method.as_ref().is_some_and(|enclosing| {
                enclosing.owner == class.internal_name
                    && enclosing.name.as_deref() == Some(method.name.as_str())
                    && enclosing.descriptor.as_deref() == Some(method.descriptor.as_str())
            })
        })
        .filter(|nested| {
            nested
                .inner_classes
                .iter()
                .find(|entry| entry.name == nested.internal_name)
                .and_then(|entry| entry.inner_name.as_ref())
                .is_some_and(|name| {
                    name.chars()
                        .next()
                        .is_some_and(|ch| !ch.is_ascii_digit())
                })
        })
        .collect::<Vec<_>>();
    nested.sort_by(|left, right| left.internal_name.cmp(&right.internal_name));
    nested
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
        StructuredStmt::TryWithResources {
            resources,
            body,
            catches,
        } => {
            let pad = "    ".repeat(indent);
            let rendered_resources = resources
                .iter()
                .map(|resource| render_try_resource(resource, ctx))
                .collect::<Vec<_>>()
                .join("; ");
            let _ = writeln!(out, "{}try ({}) {{", pad, rendered_resources);
            write_structured_stmt(out, body, indent + 1, ctx);
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
        StructuredStmt::DoWhile { condition, body } => {
            let pad = "    ".repeat(indent);
            let _ = writeln!(out, "{}do {{", pad);
            write_structured_stmt(out, body, indent + 1, ctx);
            let _ = writeln!(out, "{}}} while ({});", pad, render_expr(condition, ctx));
        }
        StructuredStmt::For {
            init,
            condition,
            update,
            body,
        } => {
            let pad = "    ".repeat(indent);
            let init = render_for_init(init, ctx);
            let update = update
                .iter()
                .map(|stmt| render_for_update(stmt, ctx))
                .collect::<Vec<_>>()
                .join(", ");
            let _ = writeln!(
                out,
                "{}for ({}; {}; {}) {{",
                pad,
                init,
                render_expr(condition, ctx),
                update
            );
            write_structured_stmt(out, body, indent + 1, ctx);
            let _ = writeln!(out, "{}}}", pad);
        }
        StructuredStmt::ForEach {
            var_type,
            var_name,
            iterable,
            body,
        } => {
            let pad = "    ".repeat(indent);
            let _ = writeln!(
                out,
                "{}for ({} {} : {}) {{",
                pad,
                render_type_in_context(var_type, ctx),
                var_name,
                render_expr(iterable, ctx)
            );
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

fn hidden_outer_slot(ctx: &MethodWriteContext<'_>) -> Option<u16> {
    if ctx.class.outer_class.is_some()
        && ctx.class.access_flags & constants::ACC_STATIC == 0
        && ctx.method.name == "<init>"
    {
        Some(1)
    } else {
        None
    }
}

fn is_hidden_outer_null_check(stmt: &Stmt, ctx: &MethodWriteContext<'_>) -> bool {
    let Some(hidden_slot) = hidden_outer_slot(ctx) else {
        return false;
    };
    match stmt {
        Stmt::Expr(StructuredExpr::Call {
            receiver: None,
            owner,
            name,
            descriptor,
            args,
            is_static,
        }) => {
            *is_static
                && owner == "java/util/Objects"
                && name == "requireNonNull"
                && descriptor == "(Ljava/lang/Object;)Ljava/lang/Object;"
                && matches!(args.as_slice(), [StructuredExpr::Var(slot)] if *slot == hidden_slot)
        }
        _ => false,
    }
}

fn write_stmt(out: &mut String, stmt: &Stmt, indent: usize, ctx: &mut MethodWriteContext<'_>) {
    let pad = "    ".repeat(indent);
    if is_hidden_outer_null_check(stmt, ctx) {
        return;
    }
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
                    ctx.slot_types.insert(*slot, ty.clone());
                    let _ = writeln!(
                        out,
                        "{}{} {} = {};",
                        pad,
                        render_type_in_context(&ty, ctx),
                        ctx.method.slot_name(*slot),
                        render_expr_as_type(value, &ty, ctx)
                    );
                    return;
                }
            }
            let _ = writeln!(
                out,
                "{}{};",
                pad,
                render_assignment_expr(target, value, ctx)
            );
            if let StructuredExpr::Var(slot) = target
                && let Some(ty) = infer_expr_type(value, ctx)
            {
                ctx.slot_types.insert(*slot, ty);
            }
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
                render_type_in_context(&actual_type, ctx),
                id,
                render_expr_as_type(value, &actual_type, ctx)
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
        Stmt::Continue => {
            let _ = writeln!(out, "{}continue;", pad);
        }
        Stmt::Return(value) => {
            if let Some(value) = value {
                let _ = writeln!(
                    out,
                    "{}return {};",
                    pad,
                    render_expr_as_type(value, &ctx.method.parsed_descriptor.return_type, ctx)
                );
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

fn render_for_init(init: &[Stmt], ctx: &mut MethodWriteContext<'_>) -> String {
    if init.is_empty() {
        return String::new();
    }
    if init.len() == 1 {
        match &init[0] {
            Stmt::Assign {
                target: StructuredExpr::Var(slot),
                value,
            } if !ctx.declared_slots.contains(slot) => {
                ctx.declared_slots.insert(*slot);
                let ty = ctx
                    .method
                    .slot_type(*slot)
                    .or_else(|| infer_expr_type(value, ctx))
                    .unwrap_or(Type::Object("java/lang/Object".to_string()));
                return format!(
                    "{} {} = {}",
                    render_type_in_context(&ty, ctx),
                    ctx.method.slot_name(*slot),
                    render_expr(value, ctx)
                );
            }
            stmt => return render_for_update(stmt, ctx),
        }
    }
    init.iter()
        .map(|stmt| render_for_update(stmt, ctx))
        .collect::<Vec<_>>()
        .join(", ")
}

fn render_for_update(stmt: &Stmt, ctx: &MethodWriteContext<'_>) -> String {
    match stmt {
        Stmt::Assign { target, value } => render_assignment_expr(target, value, ctx),
        Stmt::Expr(expr) => render_expr(expr, ctx),
        Stmt::TempAssign { id, value, .. } => {
            format!("tmp{} = {}", id, render_expr(value, ctx))
        }
        Stmt::Comment(message) => format!("/* {} */", message),
        Stmt::Break => "break".to_string(),
        Stmt::Continue => "continue".to_string(),
        Stmt::Return(Some(expr)) => format!("return {}", render_expr(expr, ctx)),
        Stmt::Return(None) => "return".to_string(),
        Stmt::Throw(expr) => format!("throw {}", render_expr(expr, ctx)),
        Stmt::ConstructorCall { is_super, args } => format!(
            "{}({})",
            if *is_super { "super" } else { "this" },
            args.iter()
                .map(|arg| render_expr(arg, ctx))
                .collect::<Vec<_>>()
                .join(", ")
        ),
        Stmt::MonitorEnter(expr) => format!("/* monitorenter {} */", render_expr(expr, ctx)),
        Stmt::MonitorExit(expr) => format!("/* monitorexit {} */", render_expr(expr, ctx)),
    }
}

fn render_assignment_expr(
    target: &StructuredExpr,
    value: &StructuredExpr,
    ctx: &MethodWriteContext<'_>,
) -> String {
    if let Some((op, rhs)) = compound_assignment_parts(target, value) {
        return format!(
            "{} {}= {}",
            render_expr(target, ctx),
            render_compound_operator(op),
            render_expr(rhs, ctx)
        );
    }
    format!(
        "{} = {}",
        render_expr(target, ctx),
        render_value_for_target(target, value, ctx)
    )
}

fn render_try_resource(resource: &TryResource, ctx: &MethodWriteContext<'_>) -> String {
    format!(
        "{} {} = {}",
        render_type_in_context(&resource.var_type, ctx),
        resource.var_name,
        render_expr(&resource.initializer, ctx)
    )
}

fn render_value_for_target(
    target: &StructuredExpr,
    value: &StructuredExpr,
    ctx: &MethodWriteContext<'_>,
) -> String {
    if let Some(signature) = signature_for_target_expr(target, ctx) {
        return render_expr_as_signature(value, &signature, ctx);
    }
    if let Some(ty) = infer_target_type(target, ctx) {
        return render_expr_as_type(value, &ty, ctx);
    }
    render_expr(value, ctx)
}

fn render_expr_as_signature(
    expr: &StructuredExpr,
    signature: &SignatureType,
    ctx: &MethodWriteContext<'_>,
) -> String {
    let rendered = render_expr(expr, ctx);
    if signature_needs_explicit_cast(signature) && !matches!(expr, StructuredExpr::Cast { .. }) {
        return format!("(({}) {})", format_signature_type(signature), rendered);
    }
    rendered
}

fn signature_needs_explicit_cast(signature: &SignatureType) -> bool {
    match signature {
        SignatureType::Base(_) => false,
        SignatureType::TypeVariable(_) => true,
        SignatureType::Array(element) => signature_needs_explicit_cast(element),
        SignatureType::Class(class) => {
            !class.simple_class.type_arguments.is_empty()
                || class
                    .suffixes
                    .iter()
                    .any(|suffix| !suffix.type_arguments.is_empty())
        }
    }
}

fn signature_for_target_expr(
    target: &StructuredExpr,
    ctx: &MethodWriteContext<'_>,
) -> Option<SignatureType> {
    match target {
        StructuredExpr::Field { owner, name, .. } => lookup_field(owner, name, ctx)
            .and_then(|field| field.parsed_signature.clone()),
        _ => None,
    }
}

fn lookup_field(
    owner: &str,
    name: &str,
    ctx: &MethodWriteContext<'_>,
) -> Option<LoadedField> {
    if owner == ctx.class.internal_name {
        return ctx.class.fields.iter().find(|field| field.name == name).cloned();
    }
    ctx.resolver
        .and_then(|resolver| resolver.load_class(owner))
        .and_then(|class| class.fields.into_iter().find(|field| field.name == name))
}

fn infer_target_type(target: &StructuredExpr, ctx: &MethodWriteContext<'_>) -> Option<Type> {
    match target {
        StructuredExpr::Var(slot) => ctx
            .slot_types
            .get(slot)
            .cloned()
            .or_else(|| ctx.method.slot_type(*slot)),
        StructuredExpr::Field { descriptor, .. } => Some(descriptor.clone()),
        StructuredExpr::ArrayAccess { array, .. } => infer_expr_type(array, ctx).and_then(|ty| match ty {
            Type::Array(element) => Some(*element),
            _ => None,
        }),
        _ => None,
    }
}

fn compound_assignment_parts<'a>(
    target: &StructuredExpr,
    value: &'a StructuredExpr,
) -> Option<(BinaryOp, &'a StructuredExpr)> {
    let StructuredExpr::Binary { op, left, right } = value else {
        return None;
    };
    if !is_compound_assignment_op(*op) {
        return None;
    }
    if expr_matches_target(target, left) {
        return Some((*op, right));
    }
    if is_commutative_assignment_op(*op) && expr_matches_target(target, right) {
        return Some((*op, left));
    }
    None
}

fn expr_matches_target(target: &StructuredExpr, candidate: &StructuredExpr) -> bool {
    target == candidate
}

fn is_commutative_assignment_op(op: BinaryOp) -> bool {
    matches!(
        op,
        BinaryOp::Add | BinaryOp::Mul | BinaryOp::And | BinaryOp::Or | BinaryOp::Xor
    )
}

fn is_compound_assignment_op(op: BinaryOp) -> bool {
    matches!(
        op,
        BinaryOp::Add
            | BinaryOp::Sub
            | BinaryOp::Mul
            | BinaryOp::Div
            | BinaryOp::Rem
            | BinaryOp::Shl
            | BinaryOp::Shr
            | BinaryOp::Ushr
            | BinaryOp::And
            | BinaryOp::Or
            | BinaryOp::Xor
    )
}

fn render_compound_operator(op: BinaryOp) -> &'static str {
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
        _ => return "=",
    }
}

fn render_expr(expr: &StructuredExpr, ctx: &MethodWriteContext<'_>) -> String {
    match expr {
        StructuredExpr::This => ctx.this_override.clone().unwrap_or_else(|| "this".to_string()),
        StructuredExpr::Var(slot) => ctx
            .slot_overrides
            .get(slot)
            .cloned()
            .or_else(|| {
                hidden_outer_slot(ctx)
                    .filter(|hidden_slot| hidden_slot == slot)
                    .and_then(|_| ctx.class.outer_class.as_ref())
                    .map(|outer| format!("{}.this", format_internal_name(outer)))
            })
            .unwrap_or_else(|| ctx.method.slot_name(*slot)),
        StructuredExpr::Temp(id) => format!("tmp{id}"),
        StructuredExpr::CaughtException(_) => "<caught-exception>".to_string(),
        StructuredExpr::Literal(literal) => render_literal(literal),
        StructuredExpr::StringConcat { parts } => {
            let mut rendered = parts
                .iter()
                .map(|part| render_string_concat_part(part, ctx))
                .collect::<Vec<_>>();
            let has_literal = parts
                .iter()
                .any(|part| matches!(part, StringConcatPart::Literal(_)));
            if !has_literal
                && parts
                    .first()
                    .is_some_and(|part| !matches!(
                        part,
                        StringConcatPart::Expr(expr)
                            if matches!(infer_expr_type(expr, ctx), Some(Type::Object(name)) if name == "java/lang/String")
                    ))
            {
                rendered.insert(0, "\"\"".to_string());
            }
            rendered.join(" + ")
        }
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
        StructuredExpr::Ternary {
            condition,
            then_expr,
            else_expr,
        } => format!(
            "({} ? {} : {})",
            render_expr(condition, ctx),
            render_expr(then_expr, ctx),
            render_expr(else_expr, ctx)
        ),
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
                let rendered_receiver = receiver
                    .as_ref()
                    .map(|expr| render_expr(expr, ctx))
                    .unwrap_or_else(|| "this".to_string());
                let rendered_receiver = match receiver.as_deref() {
                    Some(StructuredExpr::Lambda { .. })
                    | Some(StructuredExpr::MethodReference { .. }) => {
                        let receiver_type = receiver
                            .as_ref()
                            .and_then(|expr| infer_expr_type(expr, ctx))
                            .map(|ty| render_type_in_context(&ty, ctx))
                            .unwrap_or_else(|| "java.lang.Object".to_string());
                        format!("(({}) {})", receiver_type, rendered_receiver)
                    }
                    _ => rendered_receiver,
                };
                format!(
                    "{}.{}({rendered_args})",
                    rendered_receiver,
                    name
                )
            }
        }
        StructuredExpr::Lambda {
            implementation_owner,
            implementation_name,
            implementation_descriptor,
            reference_kind,
            captured_args,
            parameter_types,
            interface_type: _,
        } => render_lambda(
            implementation_owner,
            implementation_name,
            implementation_descriptor,
            *reference_kind,
            captured_args,
            parameter_types,
            ctx,
        ),
        StructuredExpr::MethodReference {
            receiver,
            owner,
            name,
            is_constructor,
            ..
        } => {
            let qualifier = receiver
                .as_ref()
                .map(|expr| render_expr(expr, ctx))
                .unwrap_or_else(|| render_internal_name_in_context(owner, ctx));
            format!("{}::{}", qualifier, if *is_constructor { "new" } else { name })
        }
        StructuredExpr::New { class_name, args } => {
            let target_class = ctx
                .resolver
                .and_then(|resolver| resolver.load_class(class_name));
            let skip_count = target_class
                .as_ref()
                .map(|class| synthetic_new_argument_count(class, args, ctx))
                .unwrap_or(0);
            let rendered_args = args
                .iter()
                .skip(skip_count)
                .map(|arg| render_expr(arg, ctx))
                .collect::<Vec<_>>()
                .join(", ");
            format!(
                "new {}({rendered_args})",
                render_constructed_type_name(class_name, target_class.as_ref(), ctx)
            )
        }
        StructuredExpr::NewArray { element_type, size } => format!(
            "new {}[{}]",
            render_type_in_context(element_type, ctx),
            render_expr(size, ctx)
        ),
        StructuredExpr::Cast { ty, expr } => {
            format!("(({}) {})", render_type_in_context(ty, ctx), render_expr(expr, ctx))
        }
        StructuredExpr::InstanceOf { expr, ty } => {
            format!(
                "({} instanceof {})",
                render_expr(expr, ctx),
                render_type_in_context(ty, ctx)
            )
        }
    }
}

fn render_expr_as_type(expr: &StructuredExpr, ty: &Type, ctx: &MethodWriteContext<'_>) -> String {
    if matches!(ty, Type::Boolean) {
        match expr {
            StructuredExpr::Literal(Literal::Int(0)) => return "false".to_string(),
            StructuredExpr::Literal(Literal::Int(1)) => return "true".to_string(),
            _ => {}
        }
    }
    render_expr(expr, ctx)
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

fn render_lambda(
    implementation_owner: &str,
    implementation_name: &str,
    implementation_descriptor: &str,
    _reference_kind: u8,
    captured_args: &[StructuredExpr],
    parameter_types: &[Type],
    ctx: &MethodWriteContext<'_>,
) -> String {
    if implementation_owner == ctx.class.internal_name {
        return render_lambda_with_owner(
            ctx.class,
            implementation_name,
            implementation_descriptor,
            captured_args,
            parameter_types,
            ctx,
        );
    }
    if let Some(resolver) = ctx.resolver
        && let Some(owner_class) = resolver.load_class(implementation_owner)
    {
        return render_lambda_with_owner(
            &owner_class,
            implementation_name,
            implementation_descriptor,
            captured_args,
            parameter_types,
            ctx,
        );
    }
    render_lambda_fallback(
        implementation_owner,
        implementation_name,
        captured_args,
        parameter_types,
        ctx,
    )
}

fn render_lambda_with_owner(
    owner_class: &LoadedClass,
    implementation_name: &str,
    implementation_descriptor: &str,
    captured_args: &[StructuredExpr],
    parameter_types: &[Type],
    ctx: &MethodWriteContext<'_>,
) -> String {
    let Some(method) = owner_class
        .methods
        .iter()
        .find(|method| {
            method.name == implementation_name && method.descriptor == implementation_descriptor
        })
    else {
        return render_lambda_fallback(
            &owner_class.internal_name,
            implementation_name,
            captured_args,
            parameter_types,
            ctx,
        );
    };

    let param_names = (0..parameter_types.len())
        .map(|index| format!("arg{index}"))
        .collect::<Vec<_>>();
    let (slot_overrides, this_override) =
        build_lambda_slot_overrides(method, captured_args, &param_names, parameter_types, ctx);

    let body = match decompile_method(owner_class, method) {
        Ok(body) => lower_switches(owner_class, method, body, ctx.resolver),
        Err(_) => {
            return render_lambda_fallback(
                &owner_class.internal_name,
                implementation_name,
                captured_args,
                parameter_types,
                ctx,
            );
        }
    };
    if structured_stmt_contains_lambda(&body) {
        return render_lambda_fallback(
            &owner_class.internal_name,
            implementation_name,
            captured_args,
            parameter_types,
            ctx,
        );
    }

    let mut lambda_ctx = MethodWriteContext::with_overrides(
        owner_class,
        method,
        ctx.resolver,
        HashSet::new(),
        HashMap::new(),
        slot_overrides,
        this_override,
    );

    let params = param_names.join(", ");
    if let Some(expr) = single_lambda_expression(&body) {
        return format!("({params}) -> {}", render_expr(expr, &lambda_ctx));
    }

    let mut body_out = String::new();
    write_structured_stmt(&mut body_out, &body, 1, &mut lambda_ctx);
    format!("({params}) -> {{\n{body_out}}}")
}

fn build_lambda_slot_overrides(
    method: &LoadedMethod,
    captured_args: &[StructuredExpr],
    parameter_names: &[String],
    parameter_types: &[Type],
    ctx: &MethodWriteContext<'_>,
) -> (HashMap<u16, String>, Option<String>) {
    let mut slot_overrides = HashMap::new();
    let rendered_captured = captured_args
        .iter()
        .map(|arg| render_expr(arg, ctx))
        .collect::<Vec<_>>();

    let mut descriptor_index = 0usize;
    let mut capture_index = 0usize;
    let mut next_slot = if method.is_static() { 0 } else { 1 };
    let this_override = if method.is_static() {
        None
    } else {
        capture_index = 1;
        rendered_captured.first().cloned().or_else(|| Some("this".to_string()))
    };

    let captured_parameter_count = method
        .parsed_descriptor
        .params
        .len()
        .saturating_sub(parameter_names.len());
    for value in rendered_captured
        .iter()
        .skip(capture_index)
        .take(captured_parameter_count)
    {
        let ty = &method.parsed_descriptor.params[descriptor_index];
        slot_overrides.insert(next_slot, value.clone());
        next_slot += ty.get_size() as u16;
        descriptor_index += 1;
    }

    for (parameter_index, parameter_name) in parameter_names.iter().enumerate() {
        if let Some(ty) = method.parsed_descriptor.params.get(descriptor_index) {
            let binding = parameter_types
                .get(parameter_index)
                .map(|ty| format!("(({}) {})", render_type_in_context(ty, ctx), parameter_name))
                .unwrap_or_else(|| parameter_name.clone());
            slot_overrides.insert(next_slot, binding);
            next_slot += ty.get_size() as u16;
            descriptor_index += 1;
        }
    }

    (slot_overrides, this_override)
}

fn structured_stmt_contains_lambda(stmt: &StructuredStmt) -> bool {
    match stmt {
        StructuredStmt::Sequence(items) => items.iter().any(structured_stmt_contains_lambda),
        StructuredStmt::Basic(stmts) => stmts.iter().any(stmt_contains_lambda),
        StructuredStmt::Try {
            try_body,
            catches,
            finally_body,
        } => {
            structured_stmt_contains_lambda(try_body)
                || catches
                    .iter()
                    .any(|catch| structured_stmt_contains_lambda(&catch.body))
                || finally_body
                    .as_ref()
                    .is_some_and(|body| structured_stmt_contains_lambda(body))
        }
        StructuredStmt::TryWithResources {
            resources,
            body,
            catches,
        } => {
            resources
                .iter()
                .any(|resource| expr_contains_lambda(&resource.initializer))
                || structured_stmt_contains_lambda(body)
                || catches
                    .iter()
                    .any(|catch| structured_stmt_contains_lambda(&catch.body))
        }
        StructuredStmt::Synchronized { expr, body } => {
            expr_contains_lambda(expr) || structured_stmt_contains_lambda(body)
        }
        StructuredStmt::Switch { expr, arms } => {
            expr_contains_lambda(expr)
                || arms
                    .iter()
                    .any(|arm| structured_stmt_contains_lambda(&arm.body))
        }
        StructuredStmt::If {
            condition,
            then_branch,
            else_branch,
        } => {
            expr_contains_lambda(condition)
                || structured_stmt_contains_lambda(then_branch)
                || else_branch
                    .as_ref()
                    .is_some_and(|branch| structured_stmt_contains_lambda(branch))
        }
        StructuredStmt::While { condition, body } => {
            expr_contains_lambda(condition) || structured_stmt_contains_lambda(body)
        }
        StructuredStmt::DoWhile { condition, body } => {
            expr_contains_lambda(condition) || structured_stmt_contains_lambda(body)
        }
        StructuredStmt::For {
            init,
            condition,
            update,
            body,
        } => {
            init.iter().any(stmt_contains_lambda)
                || expr_contains_lambda(condition)
                || update.iter().any(stmt_contains_lambda)
                || structured_stmt_contains_lambda(body)
        }
        StructuredStmt::ForEach { iterable, body, .. } => {
            expr_contains_lambda(iterable) || structured_stmt_contains_lambda(body)
        }
        StructuredStmt::Comment(_) | StructuredStmt::Empty => false,
    }
}

fn stmt_contains_lambda(stmt: &Stmt) -> bool {
    match stmt {
        Stmt::Assign { target, value } => expr_contains_lambda(target) || expr_contains_lambda(value),
        Stmt::TempAssign { value, .. }
        | Stmt::Expr(value)
        | Stmt::MonitorEnter(value)
        | Stmt::MonitorExit(value)
        | Stmt::Throw(value) => expr_contains_lambda(value),
        Stmt::Return(Some(value)) => expr_contains_lambda(value),
        Stmt::ConstructorCall { args, .. } => args.iter().any(expr_contains_lambda),
        Stmt::Return(None) | Stmt::Break | Stmt::Continue | Stmt::Comment(_) => false,
    }
}

fn expr_contains_lambda(expr: &StructuredExpr) -> bool {
    match expr {
        StructuredExpr::Lambda { .. } | StructuredExpr::MethodReference { .. } => true,
        StructuredExpr::Field { target, .. } => target
            .as_ref()
            .is_some_and(|target| expr_contains_lambda(target)),
        StructuredExpr::ArrayAccess { array, index } => {
            expr_contains_lambda(array) || expr_contains_lambda(index)
        }
        StructuredExpr::ArrayLength(expr)
        | StructuredExpr::Unary { expr, .. }
        | StructuredExpr::Cast { expr, .. }
        | StructuredExpr::InstanceOf { expr, .. } => expr_contains_lambda(expr),
        StructuredExpr::Binary { left, right, .. } => {
            expr_contains_lambda(left) || expr_contains_lambda(right)
        }
        StructuredExpr::Ternary {
            condition,
            then_expr,
            else_expr,
        } => {
            expr_contains_lambda(condition)
                || expr_contains_lambda(then_expr)
                || expr_contains_lambda(else_expr)
        }
        StructuredExpr::StringConcat { parts } => parts.iter().any(|part| match part {
            StringConcatPart::Literal(_) => false,
            StringConcatPart::Expr(expr) => expr_contains_lambda(expr),
        }),
        StructuredExpr::Call { receiver, args, .. } => {
            receiver
                .as_ref()
                .is_some_and(|receiver| expr_contains_lambda(receiver))
                || args.iter().any(expr_contains_lambda)
        }
        StructuredExpr::New { args, .. } => args.iter().any(expr_contains_lambda),
        StructuredExpr::NewArray { size, .. } => expr_contains_lambda(size),
        StructuredExpr::This
        | StructuredExpr::Var(_)
        | StructuredExpr::Temp(_)
        | StructuredExpr::CaughtException(_)
        | StructuredExpr::Literal(_) => false,
    }
}

fn single_lambda_expression<'a>(stmt: &'a StructuredStmt) -> Option<&'a StructuredExpr> {
    match stmt {
        StructuredStmt::Sequence(items) if items.len() == 1 => single_lambda_expression(&items[0]),
        StructuredStmt::Basic(stmts) if stmts.len() == 1 => match &stmts[0] {
            Stmt::Return(Some(expr)) | Stmt::Expr(expr) => Some(expr),
            _ => None,
        },
        _ => None,
    }
}

fn render_lambda_fallback(
    owner: &str,
    name: &str,
    captured_args: &[StructuredExpr],
    parameter_types: &[Type],
    ctx: &MethodWriteContext<'_>,
) -> String {
    let params = (0..parameter_types.len())
        .map(|index| format!("arg{index}"))
        .collect::<Vec<_>>();
    let mut args = captured_args
        .iter()
        .map(|arg| render_expr(arg, ctx))
        .collect::<Vec<_>>();
    args.extend(
        params
            .iter()
            .enumerate()
            .map(|(index, name)| {
                parameter_types
                    .get(index)
                    .map(|ty| format!("(({}) {})", render_type_in_context(ty, ctx), name))
                    .unwrap_or_else(|| name.clone())
            }),
    );
    format!(
        "({}) -> {}.{}({})",
        params.join(", "),
        render_internal_name_in_context(owner, ctx),
        render_synthetic_lambda_method_name(name),
        args.join(", ")
    )
}

fn render_type_in_context(ty: &Type, ctx: &MethodWriteContext<'_>) -> String {
    render_type_for_site(ty, ctx.class, ctx.resolver, Some(ctx.method))
}

fn render_type_for_site(
    ty: &Type,
    class: &LoadedClass,
    resolver: Option<&ClassPathResolver>,
    method: Option<&LoadedMethod>,
) -> String {
    match ty {
        Type::Void => "void".to_string(),
        Type::Boolean => "boolean".to_string(),
        Type::Char => "char".to_string(),
        Type::Byte => "byte".to_string(),
        Type::Short => "short".to_string(),
        Type::Int => "int".to_string(),
        Type::Float => "float".to_string(),
        Type::Long => "long".to_string(),
        Type::Double => "double".to_string(),
        Type::Array(element) => format!("{}[]", render_type_for_site(element, class, resolver, method)),
        Type::Object(name) => render_internal_name_for_site(name, class, resolver, method),
        Type::Method { .. } => format_type(ty),
    }
}

fn render_internal_name_in_context(name: &str, ctx: &MethodWriteContext<'_>) -> String {
    render_internal_name_for_site(name, ctx.class, ctx.resolver, Some(ctx.method))
}

fn render_internal_name_for_site(
    name: &str,
    class: &LoadedClass,
    resolver: Option<&ClassPathResolver>,
    method: Option<&LoadedMethod>,
) -> String {
    if let Some(resolver) = resolver
        && let Some(target_class) = resolver.load_class(name)
    {
        let is_member_of_current =
            target_class.outer_class.as_deref() == Some(class.internal_name.as_str());
        let is_local_of_current = method.is_some_and(|method| {
            target_class.enclosing_method.as_ref().is_some_and(|enclosing| {
                enclosing.owner == class.internal_name
                    && enclosing.name.as_deref() == Some(method.name.as_str())
                    && enclosing.descriptor.as_deref() == Some(method.descriptor.as_str())
            })
        });
        if is_member_of_current || is_local_of_current {
            return class_source_name(&target_class);
        }
    }
    format_internal_name(name)
}

fn infer_expr_type(expr: &StructuredExpr, ctx: &MethodWriteContext<'_>) -> Option<Type> {
    match expr {
        StructuredExpr::This => None,
        StructuredExpr::Var(slot) => ctx
            .slot_types
            .get(slot)
            .cloned()
            .or_else(|| ctx.method.slot_type(*slot)),
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
        StructuredExpr::StringConcat { .. } => Some(Type::Object("java/lang/String".to_string())),
        StructuredExpr::Field { descriptor, .. } => Some(descriptor.clone()),
        StructuredExpr::ArrayAccess { array, .. } => match infer_expr_type(array, ctx) {
            Some(Type::Array(element)) => Some((*element).clone()),
            _ => None,
        },
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
        StructuredExpr::Ternary {
            then_expr,
            else_expr,
            ..
        } => infer_expr_type(then_expr, ctx).or_else(|| infer_expr_type(else_expr, ctx)),
        StructuredExpr::Unary { op, expr } => Some(match op {
            UnaryOp::Not => Type::Boolean,
            UnaryOp::Neg => infer_expr_type(expr, ctx).unwrap_or(Type::Int),
        }),
        StructuredExpr::Call { descriptor, .. } => parse_method_descriptor(descriptor)
            .ok()
            .map(|descriptor| descriptor.return_type),
        StructuredExpr::Lambda { interface_type, .. }
        | StructuredExpr::MethodReference { interface_type, .. } => Some(interface_type.clone()),
        StructuredExpr::New { class_name, .. } => Some(Type::Object(class_name.clone())),
        StructuredExpr::NewArray { element_type, .. } => {
            Some(Type::Array(Box::new(element_type.clone())))
        }
        StructuredExpr::Cast { ty, .. } => Some(ty.clone()),
        StructuredExpr::InstanceOf { .. } => Some(Type::Boolean),
    }
}

fn synthetic_new_argument_count(
    target_class: &LoadedClass,
    args: &[StructuredExpr],
    ctx: &MethodWriteContext<'_>,
) -> usize {
    if target_class.outer_class.is_some()
        && target_class.access_flags & constants::ACC_STATIC == 0
        && args
            .first()
            .is_some_and(|arg| is_matching_outer_instance(arg, target_class, ctx))
    {
        return 1;
    }
    0
}

fn is_matching_outer_instance(
    expr: &StructuredExpr,
    target_class: &LoadedClass,
    ctx: &MethodWriteContext<'_>,
) -> bool {
    target_class.outer_class.as_deref() == Some(ctx.class.internal_name.as_str())
        && matches!(expr, StructuredExpr::This)
}

fn render_constructed_type_name(
    internal_name: &str,
    target_class: Option<&LoadedClass>,
    ctx: &MethodWriteContext<'_>,
) -> String {
    if let Some(target_class) = target_class
        && (target_class.outer_class.as_deref() == Some(ctx.class.internal_name.as_str())
            || target_class.enclosing_method.as_ref().is_some_and(|enclosing| {
                enclosing.owner == ctx.class.internal_name
                    && enclosing.name.as_deref() == Some(ctx.method.name.as_str())
                    && enclosing.descriptor.as_deref() == Some(ctx.method.descriptor.as_str())
            }))
    {
        return class_source_name(target_class);
    }
    render_internal_name_in_context(internal_name, ctx)
}

fn render_string_concat_part(part: &StringConcatPart, ctx: &MethodWriteContext<'_>) -> String {
    match part {
        StringConcatPart::Literal(value) => format!("{value:?}"),
        StringConcatPart::Expr(expr) => render_expr(expr, ctx),
    }
}
