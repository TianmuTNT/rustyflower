use crate::error::{DecompileError, Result};
use crate::types::{
    ParsedMethodDescriptor, package_name, parse_field_descriptor, parse_method_descriptor,
    simple_name,
};
use rust_asm::class_reader::{
    AttributeInfo, ExceptionTableEntry, LineNumber, LocalVariable, MethodParameter,
};
use rust_asm::constant_pool::CpInfo;
use rust_asm::insn::{AbstractInsnNode, Insn, TryCatchBlockNode};
use rust_asm::nodes::ClassNode;
use rust_asm::types::Type;

#[derive(Debug, Clone)]
pub struct LoadedClass {
    pub access_flags: u16,
    pub internal_name: String,
    pub simple_name: String,
    pub package_name: Option<String>,
    pub super_name: Option<String>,
    pub interfaces: Vec<String>,
    pub source_file: Option<String>,
    pub constant_pool: Vec<CpInfo>,
    pub fields: Vec<LoadedField>,
    pub methods: Vec<LoadedMethod>,
}

#[derive(Debug, Clone)]
pub struct LoadedField {
    pub access_flags: u16,
    pub name: String,
    pub descriptor: Type,
    pub constant_value: Option<LoadedConstant>,
}

#[derive(Debug, Clone)]
pub enum LoadedConstant {
    Boolean(bool),
    Char(char),
    Int(i32),
    Long(i64),
    Float(f32),
    Double(f64),
    String(String),
}

#[derive(Debug, Clone)]
pub struct LoadedMethod {
    pub access_flags: u16,
    pub name: String,
    pub descriptor: String,
    pub parsed_descriptor: ParsedMethodDescriptor,
    pub has_code: bool,
    pub max_stack: u16,
    pub max_locals: u16,
    pub instructions: Vec<Insn>,
    pub instruction_offsets: Vec<u16>,
    pub insn_nodes: Vec<AbstractInsnNode>,
    pub exception_table: Vec<ExceptionTableEntry>,
    pub try_catch_blocks: Vec<TryCatchBlockNode>,
    pub line_numbers: Vec<LoadedLineNumber>,
    pub local_variables: Vec<LoadedLocalVariable>,
    pub parameters: Vec<LoadedParameter>,
    pub exceptions: Vec<String>,
    pub signature: Option<String>,
}

#[derive(Debug, Clone)]
pub struct LoadedLineNumber {
    pub start_pc: u16,
    pub line_number: u16,
}

#[derive(Debug, Clone)]
pub struct LoadedLocalVariable {
    pub start_pc: u16,
    pub length: u16,
    pub name: String,
    pub descriptor: String,
    pub index: u16,
}

#[derive(Debug, Clone)]
pub struct LoadedParameter {
    pub slot: u16,
    pub name: String,
    pub descriptor: Type,
}

impl LoadedMethod {
    pub fn is_static(&self) -> bool {
        self.access_flags & rust_asm::constants::ACC_STATIC != 0
    }

    pub fn parameter_slot_count(&self) -> u16 {
        let mut slot = if self.is_static() { 0 } else { 1 };
        for param in &self.parsed_descriptor.params {
            slot += param.get_size() as u16;
        }
        slot
    }

    pub fn slot_name(&self, slot: u16) -> String {
        if !self.is_static() && slot == 0 {
            return "this".to_string();
        }
        if let Some(parameter) = self
            .parameters
            .iter()
            .find(|parameter| parameter.slot == slot)
        {
            return parameter.name.clone();
        }
        if let Some(local) = self
            .local_variables
            .iter()
            .find(|local| local.index == slot && local.start_pc == 0)
        {
            return local.name.clone();
        }
        format!("var{slot}")
    }

    pub fn slot_type(&self, slot: u16) -> Option<Type> {
        if !self.is_static() && slot == 0 {
            return None;
        }
        if let Some(parameter) = self
            .parameters
            .iter()
            .find(|parameter| parameter.slot == slot)
        {
            return Some(parameter.descriptor.clone());
        }
        self.local_variables
            .iter()
            .find(|local| local.index == slot && local.start_pc == 0)
            .and_then(|local| parse_field_descriptor(&local.descriptor).ok())
    }
}

pub fn load_class(node: ClassNode) -> Result<LoadedClass> {
    let class_name = node.name.clone();
    let mut fields = Vec::with_capacity(node.fields.len());
    for field in node.fields {
        let constant_value = field.attributes.iter().find_map(|attr| match attr {
            AttributeInfo::ConstantValue {
                constantvalue_index,
            } => decode_constant(&node.constant_pool, *constantvalue_index, &field.descriptor).ok(),
            _ => None,
        });
        fields.push(LoadedField {
            access_flags: field.access_flags,
            name: field.name,
            descriptor: parse_field_descriptor(&field.descriptor)?,
            constant_value,
        });
    }

    let mut methods = Vec::with_capacity(node.methods.len());
    for method in node.methods {
        methods.push(load_method(&node.constant_pool, method)?);
    }

    Ok(LoadedClass {
        access_flags: node.access_flags,
        internal_name: class_name.clone(),
        simple_name: simple_name(&class_name),
        package_name: package_name(&class_name),
        super_name: node.super_name,
        interfaces: node.interfaces,
        source_file: node.source_file,
        constant_pool: node.constant_pool,
        fields,
        methods,
    })
}

fn load_method(cp: &[CpInfo], method: rust_asm::nodes::MethodNode) -> Result<LoadedMethod> {
    let parsed_descriptor = parse_method_descriptor(&method.descriptor)?;
    let mut parameters = Vec::with_capacity(parsed_descriptor.params.len());
    let mut slot = if method.access_flags & rust_asm::constants::ACC_STATIC != 0 {
        0
    } else {
        1
    };
    for (index, descriptor) in parsed_descriptor.params.iter().cloned().enumerate() {
        let name = method
            .method_parameters
            .get(index)
            .and_then(|parameter| decode_parameter_name(cp, parameter))
            .or_else(|| {
                method
                    .local_variables
                    .iter()
                    .find(|local| local.index == slot && local.start_pc == 0)
                    .and_then(|local| cp_utf8(cp, local.name_index).ok())
                    .map(str::to_string)
            })
            .unwrap_or_else(|| format!("arg{index}"));
        parameters.push(LoadedParameter {
            slot,
            name,
            descriptor: descriptor.clone(),
        });
        slot += descriptor.get_size() as u16;
    }

    let local_variables = method
        .local_variables
        .into_iter()
        .map(|local| decode_local_variable(cp, local))
        .collect::<Result<Vec<_>>>()?;
    let line_numbers = method
        .line_numbers
        .into_iter()
        .map(|line| LoadedLineNumber {
            start_pc: line.start_pc,
            line_number: line.line_number,
        })
        .collect();

    Ok(LoadedMethod {
        access_flags: method.access_flags,
        name: method.name,
        descriptor: method.descriptor,
        parsed_descriptor,
        has_code: method.has_code,
        max_stack: method.max_stack,
        max_locals: method.max_locals,
        instructions: method.instructions.into_insns(),
        instruction_offsets: method.instruction_offsets,
        insn_nodes: method.insn_nodes,
        exception_table: method.exception_table,
        try_catch_blocks: method.try_catch_blocks,
        line_numbers,
        local_variables,
        parameters,
        exceptions: method.exceptions,
        signature: method.signature,
    })
}

fn decode_local_variable(cp: &[CpInfo], local: LocalVariable) -> Result<LoadedLocalVariable> {
    Ok(LoadedLocalVariable {
        start_pc: local.start_pc,
        length: local.length,
        name: cp_utf8(cp, local.name_index)?.to_string(),
        descriptor: cp_utf8(cp, local.descriptor_index)?.to_string(),
        index: local.index,
    })
}

fn decode_parameter_name(cp: &[CpInfo], parameter: &MethodParameter) -> Option<String> {
    if parameter.name_index == 0 {
        None
    } else {
        cp_utf8(cp, parameter.name_index).ok().map(str::to_string)
    }
}

fn decode_constant(cp: &[CpInfo], index: u16, descriptor: &str) -> Result<LoadedConstant> {
    let ty = parse_field_descriptor(descriptor)?;
    let entry = cp.get(index as usize).ok_or_else(|| {
        DecompileError::InvalidClass(format!("invalid constant pool index {index}"))
    })?;
    match (entry, ty) {
        (CpInfo::Integer(value), Type::Boolean) => Ok(LoadedConstant::Boolean(*value != 0)),
        (CpInfo::Integer(value), Type::Char) => Ok(LoadedConstant::Char(
            char::from_u32(*value as u32).unwrap_or('\0'),
        )),
        (CpInfo::Integer(value), _) => Ok(LoadedConstant::Int(*value)),
        (CpInfo::Long(value), _) => Ok(LoadedConstant::Long(*value)),
        (CpInfo::Float(value), _) => Ok(LoadedConstant::Float(*value)),
        (CpInfo::Double(value), _) => Ok(LoadedConstant::Double(*value)),
        (CpInfo::String { string_index }, _) => Ok(LoadedConstant::String(
            cp_utf8(cp, *string_index)?.to_string(),
        )),
        other => Err(DecompileError::InvalidClass(format!(
            "unsupported constant value for descriptor {descriptor}: {other:?}"
        ))),
    }
}

fn cp_utf8(cp: &[CpInfo], index: u16) -> Result<&str> {
    match cp.get(index as usize) {
        Some(CpInfo::Utf8(value)) => Ok(value.as_str()),
        _ => Err(DecompileError::InvalidClass(format!(
            "invalid utf8 constant pool index {index}"
        ))),
    }
}
