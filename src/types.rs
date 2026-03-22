use crate::error::{DecompileError, Result};
use rust_asm::types::Type;

#[derive(Debug, Clone)]
pub struct ParsedMethodDescriptor {
    pub params: Vec<Type>,
    pub return_type: Type,
}

pub fn parse_method_descriptor(descriptor: &str) -> Result<ParsedMethodDescriptor> {
    match Type::get_method_type(descriptor) {
        Type::Method {
            argument_types,
            return_type,
        } => Ok(ParsedMethodDescriptor {
            params: argument_types,
            return_type: *return_type,
        }),
        _ => Err(DecompileError::InvalidClass(format!(
            "invalid method descriptor: {descriptor}"
        ))),
    }
}

pub fn parse_field_descriptor(descriptor: &str) -> Result<Type> {
    let ty = Type::get_type(descriptor);
    if matches!(ty, Type::Method { .. }) {
        return Err(DecompileError::InvalidClass(format!(
            "invalid field descriptor: {descriptor}"
        )));
    }
    Ok(ty)
}

pub fn format_type(ty: &Type) -> String {
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
        Type::Array(element) => format!("{}[]", format_type(element)),
        Type::Object(name) => format_internal_name(name),
        Type::Method { .. } => "<method>".to_string(),
    }
}

pub fn format_internal_name(name: &str) -> String {
    name.replace('/', ".").replace('$', ".")
}

pub fn simple_name(internal_name: &str) -> String {
    let name = internal_name
        .rsplit('/')
        .next()
        .unwrap_or(internal_name)
        .rsplit('$')
        .next()
        .unwrap_or(internal_name);
    name.to_string()
}

pub fn package_name(internal_name: &str) -> Option<String> {
    internal_name
        .rsplit_once('/')
        .map(|(pkg, _)| pkg.replace('/', "."))
}

pub fn default_value(ty: &Type) -> &'static str {
    match ty {
        Type::Void => "",
        Type::Boolean => "false",
        Type::Char => "'\\0'",
        Type::Byte | Type::Short | Type::Int => "0",
        Type::Float => "0.0F",
        Type::Long => "0L",
        Type::Double => "0.0D",
        Type::Array(_) | Type::Object(_) => "null",
        Type::Method { .. } => "null",
    }
}
