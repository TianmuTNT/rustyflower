use crate::error::{DecompileError, Result};
use crate::types::{ParsedMethodDescriptor, parse_field_descriptor, parse_method_descriptor};
use rust_asm::constant_pool::CpInfo;
use rust_asm::insn::{Insn, LdcValue, MemberRef};
use rust_asm::types::Type;

#[derive(Debug, Clone)]
pub struct ResolvedFieldRef {
    pub owner: String,
    pub name: String,
    pub descriptor: Type,
}

#[derive(Debug, Clone)]
pub struct ResolvedMethodRef {
    pub owner: String,
    pub name: String,
    pub descriptor: String,
    pub parsed_descriptor: ParsedMethodDescriptor,
    pub is_interface: bool,
}

#[derive(Debug, Clone)]
pub enum ResolvedConstant {
    Int(i32),
    Float(f32),
    Long(i64),
    Double(f64),
    String(String),
    Class(Type),
    MethodType(String),
}

pub fn jump_target(current_offset: u16, delta: i32) -> Result<u16> {
    let target = current_offset as i32 + delta;
    if !(0..=u16::MAX as i32).contains(&target) {
        return Err(DecompileError::InvalidClass(format!(
            "jump target out of range: {current_offset} + {delta}"
        )));
    }
    Ok(target as u16)
}

pub fn resolve_field_ref(cp: &[CpInfo], field_ref: &MemberRef) -> Result<ResolvedFieldRef> {
    let (owner, name, descriptor) = match field_ref {
        MemberRef::Symbolic {
            owner,
            name,
            descriptor,
        } => (owner.clone(), name.clone(), descriptor.clone()),
        MemberRef::Index(index) => {
            let (owner, name, descriptor) = cp_field_ref(cp, *index)?;
            (owner.to_string(), name.to_string(), descriptor.to_string())
        }
    };
    Ok(ResolvedFieldRef {
        owner,
        name,
        descriptor: parse_field_descriptor(&descriptor)?,
    })
}

pub fn resolve_method_ref(cp: &[CpInfo], insn: &Insn) -> Result<ResolvedMethodRef> {
    let (owner, name, descriptor, is_interface) = match insn {
        Insn::Method(node) => match &node.method_ref {
            MemberRef::Symbolic {
                owner,
                name,
                descriptor,
            } => (
                owner.clone(),
                name.clone(),
                descriptor.clone(),
                node.insn.opcode == rust_asm::opcodes::INVOKEINTERFACE,
            ),
            MemberRef::Index(index) => {
                let (owner, name, descriptor, is_interface) = cp_method_ref(cp, *index)?;
                (
                    owner.to_string(),
                    name.to_string(),
                    descriptor.to_string(),
                    is_interface,
                )
            }
        },
        Insn::InvokeInterface(node) => {
            let (owner, name, descriptor, is_interface) = cp_method_ref(cp, node.method_index)?;
            (
                owner.to_string(),
                name.to_string(),
                descriptor.to_string(),
                is_interface,
            )
        }
        Insn::InvokeDynamic(node) => {
            let (name, descriptor) = cp_invoke_dynamic(cp, node.method_index)?;
            (
                "java/lang/Object".to_string(),
                name.to_string(),
                descriptor.to_string(),
                false,
            )
        }
        _ => {
            return Err(DecompileError::InvalidClass(
                "instruction is not a method invocation".to_string(),
            ));
        }
    };
    Ok(ResolvedMethodRef {
        owner,
        name,
        parsed_descriptor: parse_method_descriptor(&descriptor)?,
        descriptor,
        is_interface,
    })
}

pub fn resolve_type_from_index(cp: &[CpInfo], index: u16) -> Result<Type> {
    Ok(Type::get_object_type(cp_class_name(cp, index)?))
}

pub fn resolve_ldc(cp: &[CpInfo], value: &LdcValue) -> Result<ResolvedConstant> {
    match value {
        LdcValue::Index(index) => cp_ldc_constant(cp, *index),
        LdcValue::String(value) => Ok(ResolvedConstant::String(value.clone())),
        LdcValue::Type(ty) => Ok(ResolvedConstant::Class(ty.clone())),
        LdcValue::Int(value) => Ok(ResolvedConstant::Int(*value)),
        LdcValue::Float(value) => Ok(ResolvedConstant::Float(*value)),
        LdcValue::Long(value) => Ok(ResolvedConstant::Long(*value)),
        LdcValue::Double(value) => Ok(ResolvedConstant::Double(*value)),
    }
}

pub fn cp_utf8(cp: &[CpInfo], index: u16) -> Result<&str> {
    match cp.get(index as usize) {
        Some(CpInfo::Utf8(value)) => Ok(value.as_str()),
        _ => Err(DecompileError::InvalidClass(format!(
            "invalid utf8 index {index}"
        ))),
    }
}

pub fn cp_class_name(cp: &[CpInfo], index: u16) -> Result<&str> {
    match cp.get(index as usize) {
        Some(CpInfo::Class { name_index }) => cp_utf8(cp, *name_index),
        _ => Err(DecompileError::InvalidClass(format!(
            "invalid class index {index}"
        ))),
    }
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

fn cp_field_ref(cp: &[CpInfo], index: u16) -> Result<(&str, &str, &str)> {
    match cp.get(index as usize) {
        Some(CpInfo::Fieldref {
            class_index,
            name_and_type_index,
        }) => {
            let owner = cp_class_name(cp, *class_index)?;
            let (name, descriptor) = cp_name_and_type(cp, *name_and_type_index)?;
            Ok((owner, name, descriptor))
        }
        _ => Err(DecompileError::InvalidClass(format!(
            "invalid field ref index {index}"
        ))),
    }
}

fn cp_method_ref(cp: &[CpInfo], index: u16) -> Result<(&str, &str, &str, bool)> {
    match cp.get(index as usize) {
        Some(CpInfo::Methodref {
            class_index,
            name_and_type_index,
        }) => {
            let owner = cp_class_name(cp, *class_index)?;
            let (name, descriptor) = cp_name_and_type(cp, *name_and_type_index)?;
            Ok((owner, name, descriptor, false))
        }
        Some(CpInfo::InterfaceMethodref {
            class_index,
            name_and_type_index,
        }) => {
            let owner = cp_class_name(cp, *class_index)?;
            let (name, descriptor) = cp_name_and_type(cp, *name_and_type_index)?;
            Ok((owner, name, descriptor, true))
        }
        _ => Err(DecompileError::InvalidClass(format!(
            "invalid method ref index {index}"
        ))),
    }
}

fn cp_invoke_dynamic(cp: &[CpInfo], index: u16) -> Result<(&str, &str)> {
    match cp.get(index as usize) {
        Some(CpInfo::InvokeDynamic {
            name_and_type_index,
            ..
        }) => cp_name_and_type(cp, *name_and_type_index),
        _ => Err(DecompileError::InvalidClass(format!(
            "invalid invokedynamic index {index}"
        ))),
    }
}

fn cp_ldc_constant(cp: &[CpInfo], index: u16) -> Result<ResolvedConstant> {
    match cp.get(index as usize) {
        Some(CpInfo::Integer(value)) => Ok(ResolvedConstant::Int(*value)),
        Some(CpInfo::Float(value)) => Ok(ResolvedConstant::Float(*value)),
        Some(CpInfo::Long(value)) => Ok(ResolvedConstant::Long(*value)),
        Some(CpInfo::Double(value)) => Ok(ResolvedConstant::Double(*value)),
        Some(CpInfo::String { string_index }) => Ok(ResolvedConstant::String(
            cp_utf8(cp, *string_index)?.to_string(),
        )),
        Some(CpInfo::Class { name_index }) => Ok(ResolvedConstant::Class(Type::get_object_type(
            cp_utf8(cp, *name_index)?,
        ))),
        Some(CpInfo::MethodType { descriptor_index }) => Ok(ResolvedConstant::MethodType(
            cp_utf8(cp, *descriptor_index)?.to_string(),
        )),
        _ => Err(DecompileError::InvalidClass(format!(
            "unsupported ldc constant index {index}"
        ))),
    }
}
