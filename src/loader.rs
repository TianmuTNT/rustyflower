use crate::error::{DecompileError, Result};
use crate::types::{
    ParsedMethodDescriptor, package_name, parse_field_descriptor, parse_method_descriptor,
    simple_name,
};
use rust_asm::class_reader::{
    AttributeInfo, BootstrapMethod, ExceptionTableEntry, LocalVariable, MethodParameter,
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
    pub bootstrap_methods: Vec<LoadedBootstrapMethod>,
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

#[derive(Debug, Clone)]
pub struct LoadedBootstrapMethod {
    pub owner: String,
    pub name: String,
    pub descriptor: String,
    pub arguments: Vec<LoadedBootstrapArgument>,
}

#[derive(Debug, Clone, PartialEq)]
pub enum LoadedBootstrapArgument {
    String(String),
    Class(Type),
    Int(i32),
    Float(f32),
    Long(i64),
    Double(f64),
    MethodType(String),
    Unknown(u16),
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
            .filter(|local| local.index == slot)
            .min_by_key(|local| local.start_pc)
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
            .filter(|local| local.index == slot)
            .min_by_key(|local| local.start_pc)
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

    let bootstrap_methods = node
        .attributes
        .iter()
        .find_map(|attr| match attr {
            AttributeInfo::BootstrapMethods { methods } => Some(methods),
            _ => None,
        })
        .map(|methods| {
            methods
                .iter()
                .map(|method| decode_bootstrap_method(&node.constant_pool, method))
                .collect::<Result<Vec<_>>>()
        })
        .transpose()?
        .unwrap_or_default();

    Ok(LoadedClass {
        access_flags: node.access_flags,
        internal_name: class_name.clone(),
        simple_name: simple_name(&class_name),
        package_name: package_name(&class_name),
        super_name: node.super_name,
        interfaces: node.interfaces,
        source_file: node.source_file,
        constant_pool: node.constant_pool,
        bootstrap_methods,
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

fn decode_bootstrap_method(cp: &[CpInfo], method: &BootstrapMethod) -> Result<LoadedBootstrapMethod> {
    let (owner, name, descriptor) = decode_method_handle(cp, method.bootstrap_method_ref)?;
    let arguments = method
        .bootstrap_arguments
        .iter()
        .map(|index| decode_bootstrap_argument(cp, *index))
        .collect::<Result<Vec<_>>>()?;
    Ok(LoadedBootstrapMethod {
        owner,
        name,
        descriptor,
        arguments,
    })
}

fn decode_method_handle(cp: &[CpInfo], index: u16) -> Result<(String, String, String)> {
    let reference_index = match cp.get(index as usize) {
        Some(CpInfo::MethodHandle { reference_index, .. }) => *reference_index,
        _ => {
            return Err(DecompileError::InvalidClass(format!(
                "invalid method handle index {index}"
            )));
        }
    };
    match cp.get(reference_index as usize) {
        Some(CpInfo::Methodref {
            class_index,
            name_and_type_index,
        })
        | Some(CpInfo::InterfaceMethodref {
            class_index,
            name_and_type_index,
        }) => {
            let owner = cp_class_name(cp, *class_index)?.to_string();
            let (name, descriptor) = cp_name_and_type(cp, *name_and_type_index)?;
            Ok((owner, name.to_string(), descriptor.to_string()))
        }
        _ => Err(DecompileError::InvalidClass(format!(
            "invalid method-handle target {reference_index}"
        ))),
    }
}

fn decode_bootstrap_argument(cp: &[CpInfo], index: u16) -> Result<LoadedBootstrapArgument> {
    Ok(match cp.get(index as usize) {
        Some(CpInfo::String { string_index }) => {
            LoadedBootstrapArgument::String(cp_utf8(cp, *string_index)?.to_string())
        }
        Some(CpInfo::Utf8(value)) => LoadedBootstrapArgument::String(value.clone()),
        Some(CpInfo::Integer(value)) => LoadedBootstrapArgument::Int(*value),
        Some(CpInfo::Float(value)) => LoadedBootstrapArgument::Float(*value),
        Some(CpInfo::Long(value)) => LoadedBootstrapArgument::Long(*value),
        Some(CpInfo::Double(value)) => LoadedBootstrapArgument::Double(*value),
        Some(CpInfo::Class { name_index }) => {
            LoadedBootstrapArgument::Class(Type::get_object_type(cp_utf8(cp, *name_index)?))
        }
        Some(CpInfo::MethodType { descriptor_index }) => {
            LoadedBootstrapArgument::MethodType(cp_utf8(cp, *descriptor_index)?.to_string())
        }
        Some(_) | None => LoadedBootstrapArgument::Unknown(index),
    })
}

fn cp_name_and_type(cp: &[CpInfo], index: u16) -> Result<(&str, &str)> {
    match cp.get(index as usize) {
        Some(CpInfo::NameAndType {
            name_index,
            descriptor_index,
        }) => Ok((cp_utf8(cp, *name_index)?, cp_utf8(cp, *descriptor_index)?)),
        _ => Err(DecompileError::InvalidClass(format!(
            "invalid name_and_type index {index}"
        ))),
    }
}

fn cp_class_name(cp: &[CpInfo], index: u16) -> Result<&str> {
    match cp.get(index as usize) {
        Some(CpInfo::Class { name_index }) => cp_utf8(cp, *name_index),
        _ => Err(DecompileError::InvalidClass(format!(
            "invalid class index {index}"
        ))),
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
