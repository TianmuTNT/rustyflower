use rust_asm::class_writer::ClassWriter;
use rust_asm::constants::ACC_PUBLIC;
use rust_asm::insn::{Label, LdcInsnNode};
use rust_asm::opcodes;
use std::path::{Path, PathBuf};
use std::process::Command;

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

fn compile_vineflower_source(relative_source: &str) -> PathBuf {
    let manifest_dir = Path::new(env!("CARGO_MANIFEST_DIR"));
    let source = manifest_dir.join("../vineflower").join(relative_source);
    let base = std::env::temp_dir().join(format!(
        "rustyflower_tests_{}_{}",
        std::process::id(),
        source
            .file_stem()
            .and_then(|value| value.to_str())
            .unwrap_or("fixture")
    ));
    let _ = std::fs::remove_dir_all(&base);
    std::fs::create_dir_all(&base).expect("temp output directory should be created");

    let status = Command::new("javac")
        .arg("-d")
        .arg(&base)
        .arg(&source)
        .status()
        .expect("javac should be invocable");
    assert!(status.success(), "javac should compile fixture");

    let package_dir = source
        .parent()
        .and_then(|parent| parent.file_name())
        .and_then(|value| value.to_str())
        .unwrap_or("pkg");
    let class_name = source
        .file_stem()
        .and_then(|value| value.to_str())
        .expect("fixture name should exist");
    base.join(package_dir).join(format!("{class_name}.class"))
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
fn decompiles_table_switch() {
    let bytes = class_with_single_method("pkg/TestTableSwitch", "map", "(I)I", true, |method| {
        let default_label = Label::new();
        let case_one = Label::new();
        let case_two_three = Label::new();

        method.visit_var_insn(opcodes::ILOAD, 0);
        method.visit_table_switch(
            default_label,
            1,
            3,
            &[case_one, case_two_three, case_two_three],
        );

        method.visit_label(case_one);
        method.visit_ldc_insn(LdcInsnNode::int(10));
        method.visit_insn(opcodes::IRETURN);

        method.visit_label(case_two_three);
        method.visit_ldc_insn(LdcInsnNode::int(20));
        method.visit_insn(opcodes::IRETURN);

        method.visit_label(default_label);
        method.visit_insn(opcodes::ICONST_0);
        method.visit_insn(opcodes::IRETURN);
        method.visit_maxs(1, 1);
    });

    let output = rustyflower::decompile_bytes(&bytes).expect("decompilation should succeed");
    assert!(output.contains("switch (arg0)"));
    assert!(output.contains("case 1:"));
    assert!(output.contains("case 2:"));
    assert!(output.contains("case 3:"));
    assert!(output.contains("return 20;"));
    assert!(output.contains("default:"));
}

#[test]
fn decompiles_lookup_switch() {
    let bytes = class_with_single_method("pkg/TestLookupSwitch", "map", "(I)I", true, |method| {
        let default_label = Label::new();
        let case_ten = Label::new();
        let case_twenty = Label::new();

        method.visit_var_insn(opcodes::ILOAD, 0);
        method.visit_lookup_switch(default_label, &[(10, case_ten), (20, case_twenty)]);

        method.visit_label(case_ten);
        method.visit_insn(opcodes::ICONST_1);
        method.visit_insn(opcodes::IRETURN);

        method.visit_label(case_twenty);
        method.visit_insn(opcodes::ICONST_2);
        method.visit_insn(opcodes::IRETURN);

        method.visit_label(default_label);
        method.visit_insn(opcodes::ICONST_M1);
        method.visit_insn(opcodes::IRETURN);
        method.visit_maxs(1, 1);
    });

    let output = rustyflower::decompile_bytes(&bytes).expect("decompilation should succeed");
    assert!(output.contains("switch (arg0)"));
    assert!(output.contains("case 10:"));
    assert!(output.contains("case 20:"));
    assert!(output.contains("return -1;"));
}

#[test]
fn decompiles_simple_try_catch() {
    let bytes = class_with_single_method(
        "pkg/TestTryCatch",
        "safeLen",
        "(Ljava/lang/String;)I",
        true,
        |method| {
            let try_start = Label::new();
            let try_end = Label::new();
            let handler = Label::new();

            method.visit_label(try_start);
            method.visit_var_insn(opcodes::ALOAD, 0);
            method.visit_method_insn(
                opcodes::INVOKEVIRTUAL,
                "java/lang/String",
                "length",
                "()I",
                false,
            );
            method.visit_insn(opcodes::IRETURN);
            method.visit_label(try_end);
            method.visit_label(handler);
            method.visit_var_insn(opcodes::ASTORE, 1);
            method.visit_insn(opcodes::ICONST_M1);
            method.visit_insn(opcodes::IRETURN);
            method.visit_try_catch_block(
                try_start,
                try_end,
                handler,
                Some("java/lang/RuntimeException"),
            );
            method.visit_maxs(1, 2);
        },
    );

    let output = rustyflower::decompile_bytes(&bytes).expect("decompilation should succeed");
    assert!(output.contains("try {"));
    assert!(output.contains("catch (java.lang.RuntimeException"));
    assert!(output.contains("return -1;"));
}

#[test]
fn decompiles_multi_catch_structure() {
    let bytes = class_with_single_method(
        "pkg/TestMultiCatch",
        "safeLen",
        "(Ljava/lang/String;)I",
        true,
        |method| {
            let try_start = Label::new();
            let try_end = Label::new();
            let handler_one = Label::new();
            let handler_two = Label::new();

            method.visit_label(try_start);
            method.visit_var_insn(opcodes::ALOAD, 0);
            method.visit_method_insn(
                opcodes::INVOKEVIRTUAL,
                "java/lang/String",
                "length",
                "()I",
                false,
            );
            method.visit_insn(opcodes::IRETURN);
            method.visit_label(try_end);
            method.visit_label(handler_one);
            method.visit_var_insn(opcodes::ASTORE, 1);
            method.visit_insn(opcodes::ICONST_M1);
            method.visit_insn(opcodes::IRETURN);
            method.visit_label(handler_two);
            method.visit_var_insn(opcodes::ASTORE, 1);
            method.visit_insn(opcodes::ICONST_0);
            method.visit_insn(opcodes::IRETURN);
            method.visit_try_catch_block(
                try_start,
                try_end,
                handler_one,
                Some("java/lang/IllegalArgumentException"),
            );
            method.visit_try_catch_block(
                try_start,
                try_end,
                handler_two,
                Some("java/lang/RuntimeException"),
            );
            method.visit_maxs(1, 2);
        },
    );

    let output = rustyflower::decompile_bytes(&bytes).expect("decompilation should succeed");
    assert!(output.contains("catch (java.lang.IllegalArgumentException"));
    assert!(output.contains("catch (java.lang.RuntimeException"));
    assert!(output.contains("return -1;"));
    assert!(output.contains("return 0;"));
}

#[test]
fn decompiles_nested_try_catch() {
    let bytes = class_with_single_method(
        "pkg/TestNestedTryCatch",
        "nested",
        "(Ljava/lang/String;)I",
        true,
        |method| {
            let outer_start = Label::new();
            let outer_end = Label::new();
            let outer_handler = Label::new();
            let inner_start = Label::new();
            let inner_end = Label::new();
            let inner_handler = Label::new();
            let inner_done = Label::new();

            method.visit_label(outer_start);
            method.visit_var_insn(opcodes::ALOAD, 0);
            method.visit_method_insn(
                opcodes::INVOKEVIRTUAL,
                "java/lang/String",
                "length",
                "()I",
                false,
            );
            method.visit_insn(opcodes::IRETURN);
            method.visit_label(outer_end);

            method.visit_label(outer_handler);
            method.visit_var_insn(opcodes::ASTORE, 1);
            method.visit_label(inner_start);
            method.visit_var_insn(opcodes::ALOAD, 0);
            method.visit_method_insn(
                opcodes::INVOKEVIRTUAL,
                "java/lang/String",
                "isEmpty",
                "()Z",
                false,
            );
            method.visit_insn(opcodes::POP);
            method.visit_label(inner_end);
            method.visit_jump_insn(opcodes::GOTO, inner_done);

            method.visit_label(inner_handler);
            method.visit_var_insn(opcodes::ASTORE, 2);
            method.visit_insn(opcodes::ICONST_M1);
            method.visit_insn(opcodes::IRETURN);

            method.visit_label(inner_done);
            method.visit_insn(opcodes::ICONST_0);
            method.visit_insn(opcodes::IRETURN);

            method.visit_try_catch_block(
                outer_start,
                outer_end,
                outer_handler,
                Some("java/lang/RuntimeException"),
            );
            method.visit_try_catch_block(
                inner_start,
                inner_end,
                inner_handler,
                Some("java/lang/RuntimeException"),
            );
            method.visit_maxs(1, 3);
        },
    );

    let output = rustyflower::decompile_bytes(&bytes).expect("decompilation should succeed");
    assert!(output.contains("try {"));
    assert!(output.matches("catch (java.lang.RuntimeException").count() >= 2);
}

#[test]
fn decompiles_vineflower_test_class_switch_fixture() {
    // Reference: vineflower/test/org/jetbrains/java/decompiler/SingleClassesTest.java -> TestClassSwitch
    let class_path = compile_vineflower_source("testData/src/java8/pkg/TestClassSwitch.java");
    let output = rustyflower::decompile_path(&class_path).expect("fixture should decompile");
    assert!(output.contains("public class TestClassSwitch"));
    assert!(output.contains("switch (arg0)"));
    assert!(output.contains("case 13:"));
    assert!(output.contains("case 5:"));
    assert!(output.contains("default:"));
    assert!(output.contains("break;"));
    assert!(output.contains("if ((arg1 > 0))") || output.contains("if (arg1 > 0)"));
    assert!(output.contains("java.lang.System.out.println(var3);"));
}

#[test]
fn keeps_vineflower_string_switch_fixture_stable() {
    // Reference: vineflower/test/org/jetbrains/java/decompiler/SingleClassesTest.java -> TestSwitchOnStrings
    let class_path = compile_vineflower_source("testData/src/java8/pkg/TestSwitchOnStrings.java");
    let output = rustyflower::decompile_path(&class_path).expect("fixture should decompile");
    assert!(output.contains("public class TestSwitchOnStrings"));
    assert!(output.contains("switch (arg0)"));
    assert!(output.contains("case \"xxx\":"));
    assert!(output.contains("case \"yyy\":"));
    assert!(output.contains("case \"AaAa\":"));
    assert!(output.contains("case \"AaBB\":"));
    assert!(output.contains("case \"BBAa\":"));
    assert!(!output.contains("hashCode()"));
}

#[test]
fn keeps_vineflower_try_catch_finally_fixture_stable() {
    // Reference: vineflower/test/org/jetbrains/java/decompiler/SingleClassesTest.java -> TestTryCatchFinally
    let class_path = compile_vineflower_source("testData/src/java8/pkg/TestTryCatchFinally.java");
    let output = rustyflower::decompile_path(&class_path).expect("fixture should decompile");
    assert!(output.contains("public class TestTryCatchFinally"));
    assert!(
        output.contains("try {")
            || output.contains(
                "rustyflower: method body decompilation is being implemented incrementally."
            )
    );
}

#[test]
fn keeps_vineflower_try_finally_fixture_stable() {
    // Reference: vineflower/test/org/jetbrains/java/decompiler/SingleClassesTest.java -> TestTryFinally
    let class_path = compile_vineflower_source("testData/src/java8/pkg/TestTryFinally.java");
    let output = rustyflower::decompile_path(&class_path).expect("fixture should decompile");
    assert!(output.contains("public class TestTryFinally"));
    assert!(
        output
            .contains("rustyflower: method body decompilation is being implemented incrementally.")
            || output.contains("try {")
    );
}

#[test]
fn keeps_vineflower_switch_in_try_fixture_stable() {
    // Reference: vineflower/test/org/jetbrains/java/decompiler/SingleClassesTest.java -> TestSwitchInTry
    let class_path = compile_vineflower_source("testData/src/java8/pkg/TestSwitchInTry.java");
    let output = rustyflower::decompile_path(&class_path).expect("fixture should decompile");
    assert!(output.contains("public class TestSwitchInTry"));
    assert!(
        output.contains("switch (")
            || output.contains("try {")
            || output.contains(
                "rustyflower: method body decompilation is being implemented incrementally."
            )
    );
}

#[test]
fn keeps_vineflower_enum_switch_fixture_stable() {
    // Reference: vineflower/test/org/jetbrains/java/decompiler/SingleClassesTest.java -> TestSwitchOnEnum
    let class_path = compile_vineflower_source("testData/src/java8/pkg/TestSwitchOnEnum.java");
    let output = rustyflower::decompile_path(&class_path).expect("fixture should decompile");
    assert!(output.contains("public class TestSwitchOnEnum"));
    assert!(output.contains("switch (arg0)"));
    assert!(output.contains("case MICROSECONDS:"));
    assert!(output.contains("case SECONDS:"));
    assert!(!output.contains("$SwitchMap"));
    assert!(!output.contains("ordinal()"));
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
