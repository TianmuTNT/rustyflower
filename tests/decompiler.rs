use rust_asm::class_writer::ClassWriter;
use rust_asm::constants::ACC_PUBLIC;
use rust_asm::insn::Label;
use rust_asm::opcodes;

fn class_with_single_method(
    name: &str,
    method_name: &str,
    descriptor: &str,
    is_static: bool,
    build: impl FnOnce(&mut rust_asm::class_writer::MethodVisitor),
) -> Vec<u8> {
    let mut writer = ClassWriter::new(0);
    writer.visit(52, 0, ACC_PUBLIC, name, Some("java/lang/Object"), &[]);

    let mut ctor = writer.visit_method(ACC_PUBLIC, "<init>", "()V");
    ctor.visit_code();
    ctor.visit_var_insn(opcodes::ALOAD, 0);
    ctor.visit_method_insn(
        opcodes::INVOKESPECIAL,
        "java/lang/Object",
        "<init>",
        "()V",
        false,
    );
    ctor.visit_insn(opcodes::RETURN);
    ctor.visit_maxs(1, 1);
    ctor.visit_end(&mut writer);

    let access = if is_static {
        ACC_PUBLIC | rust_asm::constants::ACC_STATIC
    } else {
        ACC_PUBLIC
    };
    let mut method = writer.visit_method(access, method_name, descriptor);
    method.visit_code();
    build(&mut method);
    method.visit_end(&mut writer);

    writer.to_bytes().expect("class should encode")
}

#[test]
fn decompiles_straight_line_method() {
    let bytes = class_with_single_method("pkg/TestStraightLine", "sum", "(II)I", true, |method| {
        method.visit_var_insn(opcodes::ILOAD, 0);
        method.visit_var_insn(opcodes::ILOAD, 1);
        method.visit_insn(opcodes::IADD);
        method.visit_var_insn(opcodes::ISTORE, 2);
        method.visit_var_insn(opcodes::ILOAD, 2);
        method.visit_insn(opcodes::IRETURN);
        method.visit_maxs(2, 3);
    });

    let output = rustyflower::decompile_bytes(&bytes).expect("decompilation should succeed");
    assert!(output.contains("public static int sum(int arg0, int arg1)"));
    assert!(output.contains("int var2 = (arg0 + arg1);"));
    assert!(output.contains("return var2;"));
}

#[test]
fn decompiles_simple_if() {
    let bytes = class_with_single_method("pkg/TestIf", "choose", "(I)I", true, |method| {
        let else_label = Label::new();
        method.visit_var_insn(opcodes::ILOAD, 0);
        method.visit_jump_insn(opcodes::IFNE, else_label);
        method.visit_insn(opcodes::ICONST_1);
        method.visit_insn(opcodes::IRETURN);
        method.visit_label(else_label);
        method.visit_insn(opcodes::ICONST_2);
        method.visit_insn(opcodes::IRETURN);
        method.visit_maxs(1, 1);
    });

    let output = rustyflower::decompile_bytes(&bytes).expect("decompilation should succeed");
    assert!(output.contains("if ("));
    assert!(output.contains("return 1;"));
    assert!(output.contains("return 2;"));
}

#[test]
fn decompiles_simple_while_loop() {
    let bytes = class_with_single_method("pkg/TestLoop", "countDown", "(I)I", true, |method| {
        let loop_label = Label::new();
        let exit_label = Label::new();
        method.visit_label(loop_label);
        method.visit_var_insn(opcodes::ILOAD, 0);
        method.visit_jump_insn(opcodes::IFLE, exit_label);
        method.visit_var_insn(opcodes::ILOAD, 0);
        method.visit_insn(opcodes::ICONST_1);
        method.visit_insn(opcodes::ISUB);
        method.visit_var_insn(opcodes::ISTORE, 0);
        method.visit_jump_insn(opcodes::GOTO, loop_label);
        method.visit_label(exit_label);
        method.visit_var_insn(opcodes::ILOAD, 0);
        method.visit_insn(opcodes::IRETURN);
        method.visit_maxs(2, 1);
    });

    let output = rustyflower::decompile_bytes(&bytes).expect("decompilation should succeed");
    assert!(output.contains("while ("));
    assert!(output.contains("arg0 = (arg0 - 1);"));
    assert!(output.contains("return arg0;"));
}

#[test]
fn falls_back_cleanly_for_complex_fixture() {
    let manifest_dir = std::path::Path::new(env!("CARGO_MANIFEST_DIR"));
    let path =
        manifest_dir.join("../vineflower/testData/classes/custom/TestJava1Synchronized.class");
    let output = rustyflower::decompile_path(&path).expect("fixture should decompile");
    assert!(
        output
            .contains("rustyflower: method body decompilation is being implemented incrementally.")
    );
}
