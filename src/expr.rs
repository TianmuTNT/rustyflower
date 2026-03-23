use crate::bytecode::{
    ResolvedConstant, cp_class_name, jump_target, resolve_field_ref, resolve_ldc,
    resolve_method_ref, resolve_type_from_index,
};
use crate::cfg::BasicBlock;
use crate::error::{DecompileError, Result};
use crate::loader::{LoadedBootstrapArgument, LoadedClass, LoadedMethod, LoadedMethodHandle};
use rust_asm::insn::{FieldInsnNode, Insn, LdcValue};
use rust_asm::opcodes;
use rust_asm::types::Type;

#[derive(Debug, Clone, PartialEq)]
pub enum StructuredExpr {
    This,
    Var(u16),
    Temp(u32),
    CaughtException(Option<Type>),
    Literal(Literal),
    StringConcat {
        parts: Vec<StringConcatPart>,
    },
    Field {
        target: Option<Box<StructuredExpr>>,
        owner: String,
        name: String,
        descriptor: Type,
        is_static: bool,
    },
    ArrayAccess {
        array: Box<StructuredExpr>,
        index: Box<StructuredExpr>,
    },
    ArrayLength(Box<StructuredExpr>),
    Binary {
        op: BinaryOp,
        left: Box<StructuredExpr>,
        right: Box<StructuredExpr>,
    },
    Unary {
        op: UnaryOp,
        expr: Box<StructuredExpr>,
    },
    Ternary {
        condition: Box<StructuredExpr>,
        then_expr: Box<StructuredExpr>,
        else_expr: Box<StructuredExpr>,
    },
    Call {
        receiver: Option<Box<StructuredExpr>>,
        owner: String,
        name: String,
        descriptor: String,
        args: Vec<StructuredExpr>,
        is_static: bool,
    },
    Lambda {
        implementation_owner: String,
        implementation_name: String,
        implementation_descriptor: String,
        reference_kind: u8,
        captured_args: Vec<StructuredExpr>,
        parameter_types: Vec<Type>,
        interface_type: Type,
    },
    MethodReference {
        receiver: Option<Box<StructuredExpr>>,
        owner: String,
        name: String,
        descriptor: String,
        is_constructor: bool,
        interface_type: Type,
    },
    New {
        class_name: String,
        args: Vec<StructuredExpr>,
    },
    NewArray {
        element_type: Type,
        size: Box<StructuredExpr>,
    },
    Cast {
        ty: Type,
        expr: Box<StructuredExpr>,
    },
    InstanceOf {
        expr: Box<StructuredExpr>,
        ty: Type,
    },
}

#[derive(Debug, Clone, PartialEq)]
pub enum Literal {
    Null,
    Boolean(bool),
    Char(char),
    Int(i32),
    Long(i64),
    Float(f32),
    Double(f64),
    String(String),
    Class(Type),
}

#[derive(Debug, Clone, PartialEq)]
pub enum StringConcatPart {
    Literal(String),
    Expr(StructuredExpr),
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum BinaryOp {
    Add,
    Sub,
    Mul,
    Div,
    Rem,
    Shl,
    Shr,
    Ushr,
    And,
    Or,
    Xor,
    Eq,
    Ne,
    Lt,
    Le,
    Gt,
    Ge,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum UnaryOp {
    Neg,
    Not,
}

#[derive(Debug, Clone, PartialEq)]
pub enum Stmt {
    Assign {
        target: StructuredExpr,
        value: StructuredExpr,
    },
    TempAssign {
        id: u32,
        ty: Option<Type>,
        value: StructuredExpr,
    },
    Expr(StructuredExpr),
    MonitorEnter(StructuredExpr),
    MonitorExit(StructuredExpr),
    Break,
    Return(Option<StructuredExpr>),
    Throw(StructuredExpr),
    ConstructorCall {
        is_super: bool,
        args: Vec<StructuredExpr>,
    },
    Comment(String),
}

#[derive(Debug, Clone)]
pub enum Terminator {
    Fallthrough(Option<u16>),
    Goto(u16),
    If {
        condition: StructuredExpr,
        jump_target: u16,
        fallthrough_target: u16,
    },
    Return(Option<StructuredExpr>),
    Throw(StructuredExpr),
    Switch {
        expr: StructuredExpr,
        default_target: u16,
        cases: Vec<(i32, u16)>,
    },
}

#[derive(Debug, Clone)]
pub struct BlockSemantics {
    pub stmts: Vec<Stmt>,
    pub terminator: Terminator,
}

#[derive(Debug, Clone)]
enum StackValueKind {
    Expr(StructuredExpr),
    PendingNew { id: u32, class_name: String },
}

#[derive(Debug, Clone)]
struct StackValue {
    kind: StackValueKind,
    ty: Option<Type>,
}

struct BlockTranslator<'a> {
    class: &'a LoadedClass,
    method: &'a LoadedMethod,
    temp_counter: &'a mut u32,
    statements: Vec<Stmt>,
    stack: Vec<StackValue>,
    next_new_id: u32,
}

impl<'a> BlockTranslator<'a> {
    fn new(class: &'a LoadedClass, method: &'a LoadedMethod, temp_counter: &'a mut u32) -> Self {
        Self {
            class,
            method,
            temp_counter,
            statements: Vec::new(),
            stack: Vec::new(),
            next_new_id: 0,
        }
    }

    fn push_expr(&mut self, expr: StructuredExpr, ty: Option<Type>) {
        self.stack.push(StackValue {
            kind: StackValueKind::Expr(expr),
            ty,
        });
    }

    fn pop(&mut self) -> Result<StackValue> {
        self.stack.pop().ok_or_else(|| {
            DecompileError::Unsupported(format!(
                "stack underflow in method {}{}",
                self.method.name, self.method.descriptor
            ))
        })
    }

    fn pop_expr(&mut self) -> Result<(StructuredExpr, Option<Type>)> {
        let value = self.pop()?;
        match value.kind {
            StackValueKind::Expr(expr) => Ok((expr, value.ty)),
            StackValueKind::PendingNew { class_name, .. } => Ok((
                StructuredExpr::New {
                    class_name,
                    args: Vec::new(),
                },
                value.ty,
            )),
        }
    }

    fn ensure_duplicable(&mut self, value: StackValue) -> (StackValue, StackValue) {
        match value.kind {
            StackValueKind::PendingNew { .. } => (value.clone(), value),
            StackValueKind::Expr(expr) if is_safe_to_duplicate(&expr) => {
                let value = StackValue {
                    kind: StackValueKind::Expr(expr),
                    ty: value.ty,
                };
                (value.clone(), value)
            }
            StackValueKind::Expr(expr) => {
                let temp_id = *self.temp_counter;
                *self.temp_counter += 1;
                self.statements.push(Stmt::TempAssign {
                    id: temp_id,
                    ty: value.ty.clone(),
                    value: expr,
                });
                let temp = StackValue {
                    kind: StackValueKind::Expr(StructuredExpr::Temp(temp_id)),
                    ty: value.ty,
                };
                (temp.clone(), temp)
            }
        }
    }

    fn emit_pop_value(&mut self) -> Result<()> {
        let value = self.pop()?;
        if let StackValueKind::Expr(expr) = value.kind
            && has_side_effects(&expr)
        {
            self.statements.push(Stmt::Expr(expr));
        }
        Ok(())
    }
}

pub fn translate_block(
    class: &LoadedClass,
    method: &LoadedMethod,
    block: &BasicBlock,
    fallthrough: Option<u16>,
    temp_counter: &mut u32,
) -> Result<BlockSemantics> {
    let mut translator = BlockTranslator::new(class, method, temp_counter);
    if let Some(catch_type) = handler_entry_type(class, method, block.start_offset) {
        translator.push_expr(
            StructuredExpr::CaughtException(catch_type.clone()),
            catch_type,
        );
    }
    for instruction_index in block.first_index..=block.last_index {
        let insn = &method.instructions[instruction_index];
        let offset = method.instruction_offsets[instruction_index];
        let is_last = instruction_index == block.last_index;
        if is_last
            && let Some(terminator) =
                translate_terminator(&mut translator, insn, offset, fallthrough)?
        {
            return Ok(BlockSemantics {
                stmts: translator.statements,
                terminator,
            });
        }
        translate_instruction(&mut translator, insn)?;
    }
    Ok(BlockSemantics {
        stmts: translator.statements,
        terminator: Terminator::Fallthrough(fallthrough),
    })
}

fn translate_terminator(
    translator: &mut BlockTranslator<'_>,
    insn: &Insn,
    offset: u16,
    fallthrough: Option<u16>,
) -> Result<Option<Terminator>> {
    let terminator = match insn {
        Insn::Jump(node) if is_goto(node.insn.opcode) => {
            Some(Terminator::Goto(jump_target(offset, node.offset)?))
        }
        Insn::Jump(node) if is_conditional_jump(node.insn.opcode) => {
            let fallthrough_target = fallthrough.ok_or_else(|| {
                DecompileError::Unsupported("conditional jump without fallthrough".to_string())
            })?;
            Some(Terminator::If {
                condition: translate_jump_condition(translator, node.insn.opcode)?,
                jump_target: jump_target(offset, node.offset)?,
                fallthrough_target,
            })
        }
        Insn::LookupSwitch(node) => {
            let (expr, _) = translator.pop_expr()?;
            let mut cases = Vec::with_capacity(node.pairs.len());
            for (value, case_offset) in &node.pairs {
                cases.push((*value, jump_target(offset, *case_offset)?));
            }
            Some(Terminator::Switch {
                expr,
                default_target: jump_target(offset, node.default_offset)?,
                cases,
            })
        }
        Insn::TableSwitch(node) => {
            let (expr, _) = translator.pop_expr()?;
            let mut cases = Vec::with_capacity(node.offsets.len());
            for (index, case_offset) in node.offsets.iter().enumerate() {
                cases.push((node.low + index as i32, jump_target(offset, *case_offset)?));
            }
            Some(Terminator::Switch {
                expr,
                default_target: jump_target(offset, node.default_offset)?,
                cases,
            })
        }
        Insn::Simple(node) if is_return(node.opcode) => {
            let value = if node.opcode == opcodes::RETURN {
                None
            } else {
                Some(translator.pop_expr()?.0)
            };
            Some(Terminator::Return(value))
        }
        Insn::Simple(node) if node.opcode == opcodes::ATHROW => {
            Some(Terminator::Throw(translator.pop_expr()?.0))
        }
        _ => None,
    };
    Ok(terminator)
}

fn translate_instruction(translator: &mut BlockTranslator<'_>, insn: &Insn) -> Result<()> {
    match insn {
        Insn::Simple(node) => translate_simple_instruction(translator, node.opcode),
        Insn::Int(node) => translate_int_instruction(translator, node.insn.opcode, node.operand),
        Insn::Var(node) => translate_var_instruction(translator, node.insn.opcode, node.var_index),
        Insn::Type(node) => {
            translate_type_instruction(translator, node.insn.opcode, node.type_index)
        }
        Insn::Field(node) => translate_field_instruction(translator, node),
        Insn::Method(_) | Insn::InvokeInterface(_) | Insn::InvokeDynamic(_) => {
            translate_method_instruction(translator, insn)
        }
        Insn::Ldc(node) => translate_ldc_instruction(translator, &node.value),
        Insn::Iinc(node) => {
            let target = StructuredExpr::Var(node.var_index);
            translator.statements.push(Stmt::Assign {
                target: target.clone(),
                value: StructuredExpr::Binary {
                    op: if node.increment >= 0 {
                        BinaryOp::Add
                    } else {
                        BinaryOp::Sub
                    },
                    left: Box::new(target),
                    right: Box::new(StructuredExpr::Literal(Literal::Int(
                        node.increment.unsigned_abs() as i32,
                    ))),
                },
            });
            Ok(())
        }
        Insn::MultiANewArray(_) => Err(DecompileError::Unsupported(
            "multianewarray is not implemented yet".to_string(),
        )),
        Insn::Jump(_) | Insn::LookupSwitch(_) | Insn::TableSwitch(_) => Ok(()),
    }
}

fn translate_simple_instruction(translator: &mut BlockTranslator<'_>, opcode: u8) -> Result<()> {
    match opcode {
        opcodes::NOP => Ok(()),
        opcodes::ACONST_NULL => {
            translator.push_expr(StructuredExpr::Literal(Literal::Null), None);
            Ok(())
        }
        opcodes::ICONST_M1 => push_int(translator, -1),
        opcodes::ICONST_0 => push_int(translator, 0),
        opcodes::ICONST_1 => push_int(translator, 1),
        opcodes::ICONST_2 => push_int(translator, 2),
        opcodes::ICONST_3 => push_int(translator, 3),
        opcodes::ICONST_4 => push_int(translator, 4),
        opcodes::ICONST_5 => push_int(translator, 5),
        opcodes::LCONST_0 => push_long(translator, 0),
        opcodes::LCONST_1 => push_long(translator, 1),
        opcodes::FCONST_0 => push_float(translator, 0.0),
        opcodes::FCONST_1 => push_float(translator, 1.0),
        opcodes::FCONST_2 => push_float(translator, 2.0),
        opcodes::DCONST_0 => push_double(translator, 0.0),
        opcodes::DCONST_1 => push_double(translator, 1.0),
        opcodes::ILOAD_0..=opcodes::ALOAD_3 => {
            push_var(translator, slot_from_simple_load(opcode), opcode)
        }
        opcodes::IALOAD
        | opcodes::LALOAD
        | opcodes::FALOAD
        | opcodes::DALOAD
        | opcodes::AALOAD
        | opcodes::BALOAD
        | opcodes::CALOAD
        | opcodes::SALOAD => {
            let index = translator.pop_expr()?.0;
            let (array, array_ty) = translator.pop_expr()?;
            translator.push_expr(
                StructuredExpr::ArrayAccess {
                    array: Box::new(array),
                    index: Box::new(index),
                },
                infer_array_element_type(opcode, array_ty.as_ref()),
            );
            Ok(())
        }
        opcodes::ISTORE_0..=opcodes::ASTORE_3 => {
            store_local(translator, slot_from_simple_store(opcode))
        }
        opcodes::IASTORE
        | opcodes::LASTORE
        | opcodes::FASTORE
        | opcodes::DASTORE
        | opcodes::AASTORE
        | opcodes::BASTORE
        | opcodes::CASTORE
        | opcodes::SASTORE => {
            let value = translator.pop_expr()?.0;
            let index = translator.pop_expr()?.0;
            let array = translator.pop_expr()?.0;
            translator.statements.push(Stmt::Assign {
                target: StructuredExpr::ArrayAccess {
                    array: Box::new(array),
                    index: Box::new(index),
                },
                value,
            });
            Ok(())
        }
        opcodes::POP => translator.emit_pop_value(),
        opcodes::POP2 => {
            translator.emit_pop_value()?;
            if !translator.stack.is_empty() {
                translator.emit_pop_value()?;
            }
            Ok(())
        }
        opcodes::DUP => {
            let value = translator.pop()?;
            let (original, duplicate) = translator.ensure_duplicable(value);
            translator.stack.push(original);
            translator.stack.push(duplicate);
            Ok(())
        }
        opcodes::DUP_X1 => {
            let value1 = translator.pop()?;
            let value2 = translator.pop()?;
            let (original, duplicate) = translator.ensure_duplicable(value1);
            translator.stack.push(duplicate);
            translator.stack.push(value2);
            translator.stack.push(original);
            Ok(())
        }
        opcodes::SWAP => {
            let value1 = translator.pop()?;
            let value2 = translator.pop()?;
            translator.stack.push(value1);
            translator.stack.push(value2);
            Ok(())
        }
        opcodes::IADD | opcodes::LADD | opcodes::FADD | opcodes::DADD => {
            binary_op(translator, BinaryOp::Add)
        }
        opcodes::ISUB | opcodes::LSUB | opcodes::FSUB | opcodes::DSUB => {
            binary_op(translator, BinaryOp::Sub)
        }
        opcodes::IMUL | opcodes::LMUL | opcodes::FMUL | opcodes::DMUL => {
            binary_op(translator, BinaryOp::Mul)
        }
        opcodes::IDIV | opcodes::LDIV | opcodes::FDIV | opcodes::DDIV => {
            binary_op(translator, BinaryOp::Div)
        }
        opcodes::IREM | opcodes::LREM | opcodes::FREM | opcodes::DREM => {
            binary_op(translator, BinaryOp::Rem)
        }
        opcodes::ISHL | opcodes::LSHL => binary_op(translator, BinaryOp::Shl),
        opcodes::ISHR | opcodes::LSHR => binary_op(translator, BinaryOp::Shr),
        opcodes::IUSHR | opcodes::LUSHR => binary_op(translator, BinaryOp::Ushr),
        opcodes::IAND | opcodes::LAND => binary_op(translator, BinaryOp::And),
        opcodes::IOR | opcodes::LOR => binary_op(translator, BinaryOp::Or),
        opcodes::IXOR | opcodes::LXOR => binary_op(translator, BinaryOp::Xor),
        opcodes::INEG | opcodes::LNEG | opcodes::FNEG | opcodes::DNEG => {
            let (expr, ty) = translator.pop_expr()?;
            translator.push_expr(
                StructuredExpr::Unary {
                    op: UnaryOp::Neg,
                    expr: Box::new(expr),
                },
                ty,
            );
            Ok(())
        }
        opcodes::I2L => cast_top(translator, Type::Long),
        opcodes::I2F => cast_top(translator, Type::Float),
        opcodes::I2D => cast_top(translator, Type::Double),
        opcodes::L2I => cast_top(translator, Type::Int),
        opcodes::L2F => cast_top(translator, Type::Float),
        opcodes::L2D => cast_top(translator, Type::Double),
        opcodes::F2I => cast_top(translator, Type::Int),
        opcodes::F2L => cast_top(translator, Type::Long),
        opcodes::F2D => cast_top(translator, Type::Double),
        opcodes::D2I => cast_top(translator, Type::Int),
        opcodes::D2L => cast_top(translator, Type::Long),
        opcodes::D2F => cast_top(translator, Type::Float),
        opcodes::I2B => cast_top(translator, Type::Byte),
        opcodes::I2C => cast_top(translator, Type::Char),
        opcodes::I2S => cast_top(translator, Type::Short),
        opcodes::ARRAYLENGTH => {
            let (expr, _) = translator.pop_expr()?;
            translator.push_expr(StructuredExpr::ArrayLength(Box::new(expr)), Some(Type::Int));
            Ok(())
        }
        opcodes::MONITORENTER => {
            let expr = translator.pop_expr()?.0;
            translator.statements.push(Stmt::MonitorEnter(expr));
            Ok(())
        }
        opcodes::MONITOREXIT => {
            let expr = translator.pop_expr()?.0;
            translator.statements.push(Stmt::MonitorExit(expr));
            Ok(())
        }
        opcodes::ATHROW
        | opcodes::IRETURN
        | opcodes::LRETURN
        | opcodes::FRETURN
        | opcodes::DRETURN
        | opcodes::ARETURN
        | opcodes::RETURN => Ok(()),
        other => Err(DecompileError::Unsupported(format!(
            "unsupported opcode 0x{other:02x}"
        ))),
    }
}

fn translate_int_instruction(
    translator: &mut BlockTranslator<'_>,
    opcode: u8,
    operand: i32,
) -> Result<()> {
    match opcode {
        opcodes::BIPUSH | opcodes::SIPUSH => push_int(translator, operand),
        opcodes::NEWARRAY => {
            let size = translator.pop_expr()?.0;
            translator.push_expr(
                StructuredExpr::NewArray {
                    element_type: primitive_array_type(operand as u8)?,
                    size: Box::new(size),
                },
                None,
            );
            Ok(())
        }
        other => Err(DecompileError::Unsupported(format!(
            "unsupported int opcode 0x{other:02x}"
        ))),
    }
}

fn translate_var_instruction(
    translator: &mut BlockTranslator<'_>,
    opcode: u8,
    var_index: u16,
) -> Result<()> {
    match opcode {
        opcodes::ILOAD..=opcodes::ALOAD => push_var(translator, var_index, opcode),
        opcodes::ISTORE..=opcodes::ASTORE => store_local(translator, var_index),
        opcodes::RET => Ok(()),
        other => Err(DecompileError::Unsupported(format!(
            "unsupported var opcode 0x{other:02x}"
        ))),
    }
}

fn translate_type_instruction(
    translator: &mut BlockTranslator<'_>,
    opcode: u8,
    type_index: u16,
) -> Result<()> {
    match opcode {
        opcodes::NEW => {
            let class_name =
                match resolve_type_from_index(&translator.class.constant_pool, type_index)? {
                    Type::Object(name) => name,
                    other => {
                        return Err(DecompileError::Unsupported(format!(
                            "NEW on non-object type {other:?}"
                        )));
                    }
                };
            let new_id = translator.next_new_id;
            translator.next_new_id += 1;
            translator.stack.push(StackValue {
                kind: StackValueKind::PendingNew {
                    id: new_id,
                    class_name: class_name.clone(),
                },
                ty: Some(Type::Object(class_name)),
            });
            Ok(())
        }
        opcodes::ANEWARRAY => {
            let size = translator.pop_expr()?.0;
            let element_type =
                resolve_type_from_index(&translator.class.constant_pool, type_index)?;
            translator.push_expr(
                StructuredExpr::NewArray {
                    element_type,
                    size: Box::new(size),
                },
                None,
            );
            Ok(())
        }
        opcodes::CHECKCAST => {
            let (expr, _) = translator.pop_expr()?;
            let ty = resolve_type_from_index(&translator.class.constant_pool, type_index)?;
            translator.push_expr(
                StructuredExpr::Cast {
                    ty: ty.clone(),
                    expr: Box::new(expr),
                },
                Some(ty),
            );
            Ok(())
        }
        opcodes::INSTANCEOF => {
            let (expr, _) = translator.pop_expr()?;
            let ty = resolve_type_from_index(&translator.class.constant_pool, type_index)?;
            translator.push_expr(
                StructuredExpr::InstanceOf {
                    expr: Box::new(expr),
                    ty,
                },
                Some(Type::Boolean),
            );
            Ok(())
        }
        other => Err(DecompileError::Unsupported(format!(
            "unsupported type opcode 0x{other:02x}"
        ))),
    }
}

fn translate_field_instruction(
    translator: &mut BlockTranslator<'_>,
    insn: &FieldInsnNode,
) -> Result<()> {
    let field = resolve_field_ref(&translator.class.constant_pool, &insn.field_ref)?;
    match insn.insn.opcode {
        opcodes::GETSTATIC => {
            translator.push_expr(
                StructuredExpr::Field {
                    target: None,
                    owner: field.owner,
                    name: field.name,
                    descriptor: field.descriptor.clone(),
                    is_static: true,
                },
                Some(field.descriptor),
            );
            Ok(())
        }
        opcodes::PUTSTATIC => {
            let value = translator.pop_expr()?.0;
            translator.statements.push(Stmt::Assign {
                target: StructuredExpr::Field {
                    target: None,
                    owner: field.owner,
                    name: field.name,
                    descriptor: field.descriptor,
                    is_static: true,
                },
                value,
            });
            Ok(())
        }
        opcodes::GETFIELD => {
            let target = translator.pop_expr()?.0;
            translator.push_expr(
                StructuredExpr::Field {
                    target: Some(Box::new(target)),
                    owner: field.owner,
                    name: field.name,
                    descriptor: field.descriptor.clone(),
                    is_static: false,
                },
                Some(field.descriptor),
            );
            Ok(())
        }
        opcodes::PUTFIELD => {
            let value = translator.pop_expr()?.0;
            let target = translator.pop_expr()?.0;
            translator.statements.push(Stmt::Assign {
                target: StructuredExpr::Field {
                    target: Some(Box::new(target)),
                    owner: field.owner,
                    name: field.name,
                    descriptor: field.descriptor,
                    is_static: false,
                },
                value,
            });
            Ok(())
        }
        other => Err(DecompileError::Unsupported(format!(
            "unsupported field opcode 0x{other:02x}"
        ))),
    }
}

fn translate_method_instruction(translator: &mut BlockTranslator<'_>, insn: &Insn) -> Result<()> {
    if let Insn::InvokeDynamic(node) = insn
        && let Some(expr) = try_translate_string_concat(translator, node)?
    {
        translator.push_expr(
            expr,
            Some(Type::Object("java/lang/String".to_string())),
        );
        return Ok(());
    }
    if let Insn::InvokeDynamic(node) = insn
        && let Some(expr) = try_translate_lambda(translator, node)?
    {
        let resolved = resolve_method_ref(&translator.class.constant_pool, insn)?;
        translator.push_expr(expr, Some(resolved.parsed_descriptor.return_type));
        return Ok(());
    }

    let resolved = resolve_method_ref(&translator.class.constant_pool, insn)?;
    let mut args = Vec::with_capacity(resolved.parsed_descriptor.params.len());
    for _ in 0..resolved.parsed_descriptor.params.len() {
        args.push(translator.pop_expr()?.0);
    }
    args.reverse();

    let is_static = matches!(
        insn,
        Insn::Method(node) if node.insn.opcode == opcodes::INVOKESTATIC
    ) || matches!(insn, Insn::InvokeDynamic(_));

    let receiver = if is_static {
        None
    } else {
        Some(translator.pop()?)
    };

    if resolved.name == "<init>" {
        if let Some(receiver) = receiver {
            return translate_constructor_call(translator, receiver, resolved, args);
        }
        return Err(DecompileError::Unsupported(
            "constructor invocation without receiver".to_string(),
        ));
    }

    let receiver_expr = match receiver {
        Some(StackValue {
            kind: StackValueKind::Expr(expr),
            ..
        }) => Some(Box::new(expr)),
        Some(StackValue {
            kind: StackValueKind::PendingNew { class_name, .. },
            ..
        }) => Some(Box::new(StructuredExpr::New {
            class_name,
            args: Vec::new(),
        })),
        None => None,
    };
    let call = StructuredExpr::Call {
        receiver: receiver_expr,
        owner: resolved.owner,
        name: resolved.name,
        descriptor: resolved.descriptor,
        args,
        is_static,
    };
    if matches!(resolved.parsed_descriptor.return_type, Type::Void) {
        translator.statements.push(Stmt::Expr(call));
    } else {
        translator.push_expr(call, Some(resolved.parsed_descriptor.return_type));
    }
    Ok(())
}

fn translate_constructor_call(
    translator: &mut BlockTranslator<'_>,
    receiver: StackValue,
    resolved: crate::bytecode::ResolvedMethodRef,
    args: Vec<StructuredExpr>,
) -> Result<()> {
    match receiver.kind {
        StackValueKind::PendingNew { id, class_name } => {
            let expr = StructuredExpr::New { class_name, args };
            replace_pending_new(&mut translator.stack, id, expr.clone());
            translator.push_expr(expr, Some(Type::Object(resolved.owner)));
            Ok(())
        }
        StackValueKind::Expr(StructuredExpr::This) => {
            translator.statements.push(Stmt::ConstructorCall {
                is_super: resolved.owner != translator.class.internal_name,
                args,
            });
            Ok(())
        }
        StackValueKind::Expr(expr) => {
            translator.statements.push(Stmt::Expr(StructuredExpr::Call {
                receiver: Some(Box::new(expr)),
                owner: resolved.owner,
                name: "<init>".to_string(),
                descriptor: resolved.descriptor,
                args,
                is_static: false,
            }));
            Ok(())
        }
    }
}

fn try_translate_string_concat(
    translator: &mut BlockTranslator<'_>,
    node: &rust_asm::insn::InvokeDynamicInsnNode,
) -> Result<Option<StructuredExpr>> {
    let bootstrap = match bootstrap_method_for_callsite(translator.class, node.method_index) {
        Some(method) => method,
        None => return Ok(None),
    };
    if bootstrap.owner != "java/lang/invoke/StringConcatFactory"
        || bootstrap.name != "makeConcatWithConstants"
    {
        return Ok(None);
    }

    let resolved = resolve_method_ref(&translator.class.constant_pool, &Insn::InvokeDynamic(node.clone()))?;
    let mut args = Vec::with_capacity(resolved.parsed_descriptor.params.len());
    for _ in 0..resolved.parsed_descriptor.params.len() {
        args.push(translator.pop_expr()?.0);
    }
    args.reverse();

    let recipe = bootstrap
        .arguments
        .first()
        .and_then(|argument| match argument {
            LoadedBootstrapArgument::String(value) => Some(value.as_str()),
            _ => None,
        })
        .ok_or_else(|| {
            DecompileError::Unsupported("string concat recipe is missing".to_string())
        })?;

    let mut parts = Vec::new();
    let mut literal = String::new();
    let mut arg_index = 0usize;
    let mut constant_index = 1usize;
    for ch in recipe.chars() {
        match ch {
            '\u{0001}' => {
                if !literal.is_empty() {
                    parts.push(StringConcatPart::Literal(std::mem::take(&mut literal)));
                }
                let expr = args.get(arg_index).cloned().ok_or_else(|| {
                    DecompileError::Unsupported("string concat argument mismatch".to_string())
                })?;
                parts.push(StringConcatPart::Expr(expr));
                arg_index += 1;
            }
            '\u{0002}' => {
                if !literal.is_empty() {
                    parts.push(StringConcatPart::Literal(std::mem::take(&mut literal)));
                }
                let argument = bootstrap.arguments.get(constant_index).ok_or_else(|| {
                    DecompileError::Unsupported("string concat constant mismatch".to_string())
                })?;
                parts.push(StringConcatPart::Literal(render_bootstrap_literal(argument)));
                constant_index += 1;
            }
            other => literal.push(other),
        }
    }
    if !literal.is_empty() {
        parts.push(StringConcatPart::Literal(literal));
    }

    Ok(Some(StructuredExpr::StringConcat { parts }))
}

fn try_translate_lambda(
    translator: &mut BlockTranslator<'_>,
    node: &rust_asm::insn::InvokeDynamicInsnNode,
) -> Result<Option<StructuredExpr>> {
    let bootstrap = match bootstrap_method_for_callsite(translator.class, node.method_index) {
        Some(method) => method,
        None => return Ok(None),
    };
    if bootstrap.owner != "java/lang/invoke/LambdaMetafactory"
        || (bootstrap.name != "metafactory" && bootstrap.name != "altMetafactory")
    {
        return Ok(None);
    }

    let resolved =
        resolve_method_ref(&translator.class.constant_pool, &Insn::InvokeDynamic(node.clone()))?;
    let interface_type = resolved.parsed_descriptor.return_type.clone();
    let mut captured_args = Vec::with_capacity(resolved.parsed_descriptor.params.len());
    for _ in 0..resolved.parsed_descriptor.params.len() {
        captured_args.push(translator.pop_expr()?.0);
    }
    captured_args.reverse();

    let implementation = bootstrap
        .arguments
        .get(1)
        .and_then(|argument| match argument {
            LoadedBootstrapArgument::MethodHandle(handle) => Some(handle),
            _ => None,
        })
        .ok_or_else(|| {
            DecompileError::Unsupported("lambda bootstrap is missing implementation handle".to_string())
        })?;
    let parameter_types = bootstrap
        .arguments
        .get(2)
        .and_then(|argument| match argument {
            LoadedBootstrapArgument::MethodType(descriptor) => Some(descriptor.as_str()),
            _ => None,
        })
        .map(parse_lambda_method_type)
        .transpose()?
        .unwrap_or_default();

    if let Some(method_reference) =
        try_build_method_reference(implementation, &captured_args, interface_type.clone())
    {
        return Ok(Some(method_reference));
    }

    Ok(Some(StructuredExpr::Lambda {
        implementation_owner: implementation.owner.clone(),
        implementation_name: implementation.name.clone(),
        implementation_descriptor: implementation.descriptor.clone(),
        reference_kind: implementation.reference_kind,
        captured_args,
        parameter_types,
        interface_type,
    }))
}

fn parse_lambda_method_type(descriptor: &str) -> Result<Vec<Type>> {
    match Type::get_method_type(descriptor) {
        Type::Method { argument_types, .. } => Ok(argument_types),
        _ => Err(DecompileError::InvalidClass(format!(
            "invalid lambda method type descriptor: {descriptor}"
        ))),
    }
}

fn try_build_method_reference(
    implementation: &LoadedMethodHandle,
    captured_args: &[StructuredExpr],
    interface_type: Type,
) -> Option<StructuredExpr> {
    if implementation.name.starts_with("lambda$") {
        return None;
    }
    match implementation.reference_kind {
        5 | 7 | 9 if captured_args.len() == 1 => Some(StructuredExpr::MethodReference {
            receiver: Some(Box::new(captured_args[0].clone())),
            owner: implementation.owner.clone(),
            name: implementation.name.clone(),
            descriptor: implementation.descriptor.clone(),
            is_constructor: implementation.name == "<init>",
            interface_type,
        }),
        5 | 6 | 7 | 8 | 9 if captured_args.is_empty() => Some(StructuredExpr::MethodReference {
            receiver: None,
            owner: implementation.owner.clone(),
            name: implementation.name.clone(),
            descriptor: implementation.descriptor.clone(),
            is_constructor: implementation.name == "<init>",
            interface_type,
        }),
        _ => None,
    }
}

fn bootstrap_method_for_callsite<'a>(
    class: &'a LoadedClass,
    invoke_dynamic_index: u16,
) -> Option<&'a crate::loader::LoadedBootstrapMethod> {
    let bootstrap_index = match class.constant_pool.get(invoke_dynamic_index as usize) {
        Some(rust_asm::constant_pool::CpInfo::InvokeDynamic {
            bootstrap_method_attr_index,
            ..
        }) => *bootstrap_method_attr_index as usize,
        _ => return None,
    };
    class.bootstrap_methods.get(bootstrap_index)
}

fn render_bootstrap_literal(argument: &LoadedBootstrapArgument) -> String {
    match argument {
        LoadedBootstrapArgument::String(value) => value.clone(),
        LoadedBootstrapArgument::Int(value) => value.to_string(),
        LoadedBootstrapArgument::Float(value) => value.to_string(),
        LoadedBootstrapArgument::Long(value) => value.to_string(),
        LoadedBootstrapArgument::Double(value) => value.to_string(),
        LoadedBootstrapArgument::Class(ty) => ty.get_descriptor(),
        LoadedBootstrapArgument::MethodType(value) => value.clone(),
        LoadedBootstrapArgument::MethodHandle(handle) => {
            format!(
                "{}::{}{}",
                handle.owner, handle.name, handle.descriptor
            )
        }
        LoadedBootstrapArgument::Unknown(index) => format!("/*bootstrap:{index}*/"),
    }
}

fn translate_ldc_instruction(translator: &mut BlockTranslator<'_>, value: &LdcValue) -> Result<()> {
    match resolve_ldc(&translator.class.constant_pool, value)? {
        ResolvedConstant::Int(value) => push_int(translator, value),
        ResolvedConstant::Float(value) => push_float(translator, value),
        ResolvedConstant::Long(value) => push_long(translator, value),
        ResolvedConstant::Double(value) => push_double(translator, value),
        ResolvedConstant::String(value) => {
            translator.push_expr(
                StructuredExpr::Literal(Literal::String(value)),
                Some(Type::Object("java/lang/String".to_string())),
            );
            Ok(())
        }
        ResolvedConstant::Class(ty) => {
            translator.push_expr(
                StructuredExpr::Literal(Literal::Class(ty)),
                Some(Type::Object("java/lang/Class".to_string())),
            );
            Ok(())
        }
        ResolvedConstant::MethodType(_) => Err(DecompileError::Unsupported(
            "method type ldc is not implemented".to_string(),
        )),
    }
}

fn translate_jump_condition(
    translator: &mut BlockTranslator<'_>,
    opcode: u8,
) -> Result<StructuredExpr> {
    match opcode {
        opcodes::IFEQ => single_compare(translator, BinaryOp::Eq, 0),
        opcodes::IFNE => single_compare(translator, BinaryOp::Ne, 0),
        opcodes::IFLT => single_compare(translator, BinaryOp::Lt, 0),
        opcodes::IFGE => single_compare(translator, BinaryOp::Ge, 0),
        opcodes::IFGT => single_compare(translator, BinaryOp::Gt, 0),
        opcodes::IFLE => single_compare(translator, BinaryOp::Le, 0),
        opcodes::IF_ICMPEQ => pair_compare(translator, BinaryOp::Eq),
        opcodes::IF_ICMPNE => pair_compare(translator, BinaryOp::Ne),
        opcodes::IF_ICMPLT => pair_compare(translator, BinaryOp::Lt),
        opcodes::IF_ICMPGE => pair_compare(translator, BinaryOp::Ge),
        opcodes::IF_ICMPGT => pair_compare(translator, BinaryOp::Gt),
        opcodes::IF_ICMPLE => pair_compare(translator, BinaryOp::Le),
        opcodes::IF_ACMPEQ => pair_compare(translator, BinaryOp::Eq),
        opcodes::IF_ACMPNE => pair_compare(translator, BinaryOp::Ne),
        opcodes::IFNULL => null_compare(translator, BinaryOp::Eq),
        opcodes::IFNONNULL => null_compare(translator, BinaryOp::Ne),
        other => Err(DecompileError::Unsupported(format!(
            "unsupported conditional opcode 0x{other:02x}"
        ))),
    }
}

fn single_compare(
    translator: &mut BlockTranslator<'_>,
    op: BinaryOp,
    rhs: i32,
) -> Result<StructuredExpr> {
    let (left, ty) = translator.pop_expr()?;
    if matches!(ty, Some(Type::Boolean)) && rhs == 0 {
        return Ok(match op {
            BinaryOp::Eq => StructuredExpr::Unary {
                op: UnaryOp::Not,
                expr: Box::new(left),
            },
            BinaryOp::Ne => left,
            _ => StructuredExpr::Binary {
                op,
                left: Box::new(left),
                right: Box::new(StructuredExpr::Literal(Literal::Int(rhs))),
            },
        });
    }
    Ok(StructuredExpr::Binary {
        op,
        left: Box::new(left),
        right: Box::new(StructuredExpr::Literal(Literal::Int(rhs))),
    })
}

fn pair_compare(translator: &mut BlockTranslator<'_>, op: BinaryOp) -> Result<StructuredExpr> {
    let right = translator.pop_expr()?.0;
    let left = translator.pop_expr()?.0;
    Ok(StructuredExpr::Binary {
        op,
        left: Box::new(left),
        right: Box::new(right),
    })
}

fn null_compare(translator: &mut BlockTranslator<'_>, op: BinaryOp) -> Result<StructuredExpr> {
    let left = translator.pop_expr()?.0;
    Ok(StructuredExpr::Binary {
        op,
        left: Box::new(left),
        right: Box::new(StructuredExpr::Literal(Literal::Null)),
    })
}

fn push_var(translator: &mut BlockTranslator<'_>, slot: u16, opcode: u8) -> Result<()> {
    let expr = if !translator.method.is_static() && slot == 0 {
        StructuredExpr::This
    } else {
        StructuredExpr::Var(slot)
    };
    let ty = translator
        .method
        .slot_type(slot)
        .or_else(|| load_opcode_type(opcode));
    translator.push_expr(expr, ty);
    Ok(())
}

fn infer_array_element_type(opcode: u8, array_ty: Option<&Type>) -> Option<Type> {
    match opcode {
        opcodes::IALOAD => Some(Type::Int),
        opcodes::LALOAD => Some(Type::Long),
        opcodes::FALOAD => Some(Type::Float),
        opcodes::DALOAD => Some(Type::Double),
        opcodes::BALOAD => Some(Type::Byte),
        opcodes::CALOAD => Some(Type::Char),
        opcodes::SALOAD => Some(Type::Short),
        opcodes::AALOAD => match array_ty {
            Some(Type::Array(element)) => Some((**element).clone()),
            _ => None,
        },
        _ => None,
    }
}

fn store_local(translator: &mut BlockTranslator<'_>, slot: u16) -> Result<()> {
    let Ok((value, _)) = translator.pop_expr() else {
        // Old jsr/ret-style finally subroutines store the synthetic return address in a local.
        return Ok(());
    };
    translator.statements.push(Stmt::Assign {
        target: StructuredExpr::Var(slot),
        value,
    });
    Ok(())
}

fn binary_op(translator: &mut BlockTranslator<'_>, op: BinaryOp) -> Result<()> {
    let (right, right_ty) = translator.pop_expr()?;
    let (left, left_ty) = translator.pop_expr()?;
    translator.push_expr(
        StructuredExpr::Binary {
            op,
            left: Box::new(left),
            right: Box::new(right),
        },
        left_ty.or(right_ty),
    );
    Ok(())
}

fn cast_top(translator: &mut BlockTranslator<'_>, ty: Type) -> Result<()> {
    let (expr, _) = translator.pop_expr()?;
    translator.push_expr(
        StructuredExpr::Cast {
            ty: ty.clone(),
            expr: Box::new(expr),
        },
        Some(ty),
    );
    Ok(())
}

fn replace_pending_new(stack: &mut [StackValue], id: u32, expr: StructuredExpr) {
    for value in stack {
        if let StackValueKind::PendingNew { id: existing, .. } = value.kind
            && existing == id
        {
            value.kind = StackValueKind::Expr(expr.clone());
        }
    }
}

fn push_int(translator: &mut BlockTranslator<'_>, value: i32) -> Result<()> {
    translator.push_expr(
        StructuredExpr::Literal(Literal::Int(value)),
        Some(Type::Int),
    );
    Ok(())
}

fn push_long(translator: &mut BlockTranslator<'_>, value: i64) -> Result<()> {
    translator.push_expr(
        StructuredExpr::Literal(Literal::Long(value)),
        Some(Type::Long),
    );
    Ok(())
}

fn push_float(translator: &mut BlockTranslator<'_>, value: f32) -> Result<()> {
    translator.push_expr(
        StructuredExpr::Literal(Literal::Float(value)),
        Some(Type::Float),
    );
    Ok(())
}

fn push_double(translator: &mut BlockTranslator<'_>, value: f64) -> Result<()> {
    translator.push_expr(
        StructuredExpr::Literal(Literal::Double(value)),
        Some(Type::Double),
    );
    Ok(())
}

fn primitive_array_type(atype: u8) -> Result<Type> {
    match atype {
        4 => Ok(Type::Boolean),
        5 => Ok(Type::Char),
        6 => Ok(Type::Float),
        7 => Ok(Type::Double),
        8 => Ok(Type::Byte),
        9 => Ok(Type::Short),
        10 => Ok(Type::Int),
        11 => Ok(Type::Long),
        _ => Err(DecompileError::Unsupported(format!(
            "unsupported newarray type {atype}"
        ))),
    }
}

fn slot_from_simple_load(opcode: u8) -> u16 {
    match opcode {
        opcodes::ILOAD_0
        | opcodes::LLOAD_0
        | opcodes::FLOAD_0
        | opcodes::DLOAD_0
        | opcodes::ALOAD_0 => 0,
        opcodes::ILOAD_1
        | opcodes::LLOAD_1
        | opcodes::FLOAD_1
        | opcodes::DLOAD_1
        | opcodes::ALOAD_1 => 1,
        opcodes::ILOAD_2
        | opcodes::LLOAD_2
        | opcodes::FLOAD_2
        | opcodes::DLOAD_2
        | opcodes::ALOAD_2 => 2,
        _ => 3,
    }
}

fn slot_from_simple_store(opcode: u8) -> u16 {
    match opcode {
        opcodes::ISTORE_0
        | opcodes::LSTORE_0
        | opcodes::FSTORE_0
        | opcodes::DSTORE_0
        | opcodes::ASTORE_0 => 0,
        opcodes::ISTORE_1
        | opcodes::LSTORE_1
        | opcodes::FSTORE_1
        | opcodes::DSTORE_1
        | opcodes::ASTORE_1 => 1,
        opcodes::ISTORE_2
        | opcodes::LSTORE_2
        | opcodes::FSTORE_2
        | opcodes::DSTORE_2
        | opcodes::ASTORE_2 => 2,
        _ => 3,
    }
}

fn load_opcode_type(opcode: u8) -> Option<Type> {
    match opcode {
        opcodes::ILOAD..=opcodes::ILOAD_3 => Some(Type::Int),
        opcodes::LLOAD..=opcodes::LLOAD_3 => Some(Type::Long),
        opcodes::FLOAD..=opcodes::FLOAD_3 => Some(Type::Float),
        opcodes::DLOAD..=opcodes::DLOAD_3 => Some(Type::Double),
        opcodes::ALOAD..=opcodes::ALOAD_3 => None,
        _ => None,
    }
}

fn is_goto(opcode: u8) -> bool {
    matches!(opcode, opcodes::GOTO | opcodes::GOTO_W)
}

fn is_conditional_jump(opcode: u8) -> bool {
    matches!(
        opcode,
        opcodes::IFEQ
            | opcodes::IFNE
            | opcodes::IFLT
            | opcodes::IFGE
            | opcodes::IFGT
            | opcodes::IFLE
            | opcodes::IF_ICMPEQ
            | opcodes::IF_ICMPNE
            | opcodes::IF_ICMPLT
            | opcodes::IF_ICMPGE
            | opcodes::IF_ICMPGT
            | opcodes::IF_ICMPLE
            | opcodes::IF_ACMPEQ
            | opcodes::IF_ACMPNE
            | opcodes::IFNULL
            | opcodes::IFNONNULL
    )
}

fn is_return(opcode: u8) -> bool {
    matches!(
        opcode,
        opcodes::IRETURN
            | opcodes::LRETURN
            | opcodes::FRETURN
            | opcodes::DRETURN
            | opcodes::ARETURN
            | opcodes::RETURN
    )
}

fn is_safe_to_duplicate(expr: &StructuredExpr) -> bool {
    matches!(
        expr,
        StructuredExpr::This
            | StructuredExpr::Var(_)
            | StructuredExpr::Temp(_)
            | StructuredExpr::CaughtException(_)
            | StructuredExpr::Literal(_)
            | StructuredExpr::StringConcat { .. }
    )
}

fn has_side_effects(expr: &StructuredExpr) -> bool {
    matches!(
        expr,
        StructuredExpr::Call { .. } | StructuredExpr::New { .. }
    )
}

pub fn negate_condition(expr: StructuredExpr) -> StructuredExpr {
    match expr {
        StructuredExpr::Binary { op, left, right } => StructuredExpr::Binary {
            op: negate_binary_op(op),
            left,
            right,
        },
        StructuredExpr::Unary {
            op: UnaryOp::Not,
            expr,
        } => *expr,
        other => StructuredExpr::Unary {
            op: UnaryOp::Not,
            expr: Box::new(other),
        },
    }
}

fn negate_binary_op(op: BinaryOp) -> BinaryOp {
    match op {
        BinaryOp::Eq => BinaryOp::Ne,
        BinaryOp::Ne => BinaryOp::Eq,
        BinaryOp::Lt => BinaryOp::Ge,
        BinaryOp::Le => BinaryOp::Gt,
        BinaryOp::Gt => BinaryOp::Le,
        BinaryOp::Ge => BinaryOp::Lt,
        other => other,
    }
}

fn handler_entry_type(
    class: &LoadedClass,
    method: &LoadedMethod,
    handler_pc: u16,
) -> Option<Option<Type>> {
    method
        .exception_table
        .iter()
        .find(|entry| entry.handler_pc == handler_pc)
        .map(|entry| {
            if entry.catch_type == 0 {
                Some(Type::Object("java/lang/Throwable".to_string()))
            } else {
                cp_class_name(&class.constant_pool, entry.catch_type)
                    .ok()
                    .map(Type::get_object_type)
            }
        })
}
