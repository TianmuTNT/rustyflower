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

fn assert_no_unresolved_artifacts(output: &str) {
    assert!(
        !output.contains("rustyflower: method body decompilation is being implemented incrementally."),
        "unexpected incremental fallback:\n{output}"
    );
    assert!(
        !output.contains("rustyflower: unsupported goto"),
        "unexpected unresolved goto:\n{output}"
    );
    assert!(
        !output.contains("<caught-exception>"),
        "unexpected caught-exception placeholder:\n{output}"
    );
}

fn assert_recompiles_output(class_name: &str, output: &str) {
    let base = std::env::temp_dir().join(format!(
        "rustyflower_recompile_{}_{}",
        std::process::id(),
        class_name
    ));
    let _ = std::fs::remove_dir_all(&base);
    std::fs::create_dir_all(&base).expect("temp recompile directory should be created");

    let source_path = base.join(format!("{class_name}.java"));
    std::fs::write(&source_path, output).expect("decompiled source should be written");

    let status = Command::new("javac")
        .arg("-d")
        .arg(&base)
        .arg(&source_path)
        .status()
        .expect("javac should be invocable for recompilation");
    assert!(status.success(), "decompiled output should recompile");
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
    assert!(output.contains("arg0 = (arg0 - 1);") || output.contains("arg0 -= 1;"));
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
fn decompiles_simple_try_finally() {
    let bytes = class_with_single_method("pkg/TestTryFinallySynth", "run", "()V", false, |method| {
        let try_start = Label::new();
        let try_end = Label::new();
        let handler = Label::new();
        let after = Label::new();

        method.visit_label(try_start);
        method.visit_field_insn(
            opcodes::GETSTATIC,
            "java/lang/System",
            "out",
            "Ljava/io/PrintStream;",
        );
        method.visit_ldc_insn(LdcInsnNode::string("Hello"));
        method.visit_method_insn(
            opcodes::INVOKEVIRTUAL,
            "java/io/PrintStream",
            "println",
            "(Ljava/lang/String;)V",
            false,
        );
        method.visit_label(try_end);
        method.visit_field_insn(
            opcodes::GETSTATIC,
            "java/lang/System",
            "out",
            "Ljava/io/PrintStream;",
        );
        method.visit_ldc_insn(LdcInsnNode::string("Finally"));
        method.visit_method_insn(
            opcodes::INVOKEVIRTUAL,
            "java/io/PrintStream",
            "println",
            "(Ljava/lang/String;)V",
            false,
        );
        method.visit_jump_insn(opcodes::GOTO, after);
        method.visit_label(handler);
        method.visit_var_insn(opcodes::ASTORE, 1);
        method.visit_field_insn(
            opcodes::GETSTATIC,
            "java/lang/System",
            "out",
            "Ljava/io/PrintStream;",
        );
        method.visit_ldc_insn(LdcInsnNode::string("Finally"));
        method.visit_method_insn(
            opcodes::INVOKEVIRTUAL,
            "java/io/PrintStream",
            "println",
            "(Ljava/lang/String;)V",
            false,
        );
        method.visit_var_insn(opcodes::ALOAD, 1);
        method.visit_insn(opcodes::ATHROW);
        method.visit_label(after);
        method.visit_insn(opcodes::RETURN);
        method.visit_try_catch_block(try_start, try_end, handler, None);
        method.visit_maxs(2, 2);
    });

    let output = rustyflower::decompile_bytes(&bytes).expect("decompilation should succeed");
    assert!(output.contains("try {"));
    assert!(output.contains("finally {"));
    assert!(output.contains("\"Finally\""));
}

#[test]
fn decompiles_simple_try_catch_finally() {
    let bytes = class_with_single_method("pkg/TestTryCatchFinallySynth", "run", "()I", true, |method| {
        let try_start = Label::new();
        let try_end = Label::new();
        let catch_handler = Label::new();
        let finally_handler = Label::new();
        let after_try = Label::new();
        let after_catch = Label::new();

        method.visit_label(try_start);
        method.visit_insn(opcodes::ICONST_1);
        method.visit_var_insn(opcodes::ISTORE, 1);
        method.visit_label(try_end);
        method.visit_field_insn(
            opcodes::GETSTATIC,
            "java/lang/System",
            "out",
            "Ljava/io/PrintStream;",
        );
        method.visit_ldc_insn(LdcInsnNode::string("Finally"));
        method.visit_method_insn(
            opcodes::INVOKEVIRTUAL,
            "java/io/PrintStream",
            "println",
            "(Ljava/lang/String;)V",
            false,
        );
        method.visit_jump_insn(opcodes::GOTO, after_try);

        method.visit_label(catch_handler);
        method.visit_var_insn(opcodes::ASTORE, 2);
        method.visit_insn(opcodes::ICONST_M1);
        method.visit_var_insn(opcodes::ISTORE, 1);
        method.visit_field_insn(
            opcodes::GETSTATIC,
            "java/lang/System",
            "out",
            "Ljava/io/PrintStream;",
        );
        method.visit_ldc_insn(LdcInsnNode::string("Finally"));
        method.visit_method_insn(
            opcodes::INVOKEVIRTUAL,
            "java/io/PrintStream",
            "println",
            "(Ljava/lang/String;)V",
            false,
        );
        method.visit_jump_insn(opcodes::GOTO, after_catch);

        method.visit_label(finally_handler);
        method.visit_var_insn(opcodes::ASTORE, 3);
        method.visit_field_insn(
            opcodes::GETSTATIC,
            "java/lang/System",
            "out",
            "Ljava/io/PrintStream;",
        );
        method.visit_ldc_insn(LdcInsnNode::string("Finally"));
        method.visit_method_insn(
            opcodes::INVOKEVIRTUAL,
            "java/io/PrintStream",
            "println",
            "(Ljava/lang/String;)V",
            false,
        );
        method.visit_var_insn(opcodes::ALOAD, 3);
        method.visit_insn(opcodes::ATHROW);

        method.visit_label(after_try);
        method.visit_label(after_catch);
        method.visit_var_insn(opcodes::ILOAD, 1);
        method.visit_insn(opcodes::IRETURN);

        method.visit_try_catch_block(try_start, try_end, catch_handler, Some("java/lang/RuntimeException"));
        method.visit_try_catch_block(try_start, try_end, finally_handler, None);
        method.visit_try_catch_block(catch_handler, after_catch, finally_handler, None);
        method.visit_maxs(2, 4);
    });

    let output = rustyflower::decompile_bytes(&bytes).expect("decompilation should succeed");
    assert!(output.contains("try {"));
    assert!(output.contains("catch (java.lang.RuntimeException"));
    assert!(output.contains("finally {"));
    assert!(output.contains("return var1;") || output.contains("return -1;") || output.contains("return 1;"));
    assert_no_unresolved_artifacts(&output);
}

#[test]
fn decompiles_synchronized_block() {
    let bytes = class_with_single_method("pkg/TestSync", "inc", "(I)I", false, |method| {
        let body_start = Label::new();
        let body_end = Label::new();
        let handler = Label::new();
        let after = Label::new();

        method.visit_var_insn(opcodes::ALOAD, 0);
        method.visit_insn(opcodes::DUP);
        method.visit_var_insn(opcodes::ASTORE, 2);
        method.visit_insn(opcodes::MONITORENTER);
        method.visit_label(body_start);
        method.visit_iinc_insn(1, 1);
        method.visit_var_insn(opcodes::ALOAD, 2);
        method.visit_insn(opcodes::MONITOREXIT);
        method.visit_label(body_end);
        method.visit_jump_insn(opcodes::GOTO, after);
        method.visit_label(handler);
        method.visit_var_insn(opcodes::ASTORE, 3);
        method.visit_var_insn(opcodes::ALOAD, 2);
        method.visit_insn(opcodes::MONITOREXIT);
        method.visit_var_insn(opcodes::ALOAD, 3);
        method.visit_insn(opcodes::ATHROW);
        method.visit_label(after);
        method.visit_var_insn(opcodes::ILOAD, 1);
        method.visit_insn(opcodes::IRETURN);
        method.visit_try_catch_block(body_start, body_end, handler, None);
        method.visit_try_catch_block(handler, after, handler, None);
        method.visit_maxs(2, 4);
    });

    let output = rustyflower::decompile_bytes(&bytes).expect("decompilation should succeed");
    assert!(output.contains("synchronized (this)"));
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
fn decompiles_vineflower_try_catch_finally_fixture() {
    // Reference: vineflower/test/org/jetbrains/java/decompiler/SingleClassesTest.java -> TestTryCatchFinally
    let class_path = compile_vineflower_source("testData/src/java8/pkg/TestTryCatchFinally.java");
    let output = rustyflower::decompile_path(&class_path).expect("fixture should decompile");
    assert!(output.contains("public class TestTryCatchFinally"));
    assert!(output.contains("try {"));
    assert!(output.contains("catch (java.lang.Exception"));
    assert!(output.contains("finally {"));
    assert!(output.contains("java.lang.System.out.println(\"sout1\");"));
    assert!(output.contains("java.lang.System.out.println(\"finally\");"));
    assert_no_unresolved_artifacts(&output);
}

#[test]
fn decompiles_vineflower_try_finally_fixture() {
    // Reference: vineflower/test/org/jetbrains/java/decompiler/SingleClassesTest.java -> TestTryFinally
    let class_path = compile_vineflower_source("testData/src/java8/pkg/TestTryFinally.java");
    let output = rustyflower::decompile_path(&class_path).expect("fixture should decompile");
    assert!(output.contains("public class TestTryFinally"));
    assert!(output.contains("finally {"));
    assert!(output.contains("java.lang.System.out.println(\"Finally\");"));
    assert!(output.contains("if ((arg0 > 0))") || output.contains("if (arg0 > 0)"));
    assert_no_unresolved_artifacts(&output);
}

#[test]
fn decompiles_vineflower_synchronized_mapping_fixture() {
    // Reference: vineflower/test/org/jetbrains/java/decompiler/SingleClassesTest.java -> TestSynchronizedMapping
    let class_path = compile_vineflower_source("testData/src/java8/pkg/TestSynchronizedMapping.java");
    let output = rustyflower::decompile_path(&class_path).expect("fixture should decompile");
    assert!(output.contains("public class TestSynchronizedMapping"));
    assert!(output.contains("synchronized (this)"));
    assert!(output.contains("arg0 = (arg0 + 1);") || output.contains("arg0 += 1;"));
    assert_no_unresolved_artifacts(&output);
}

#[test]
fn decompiles_vineflower_switch_in_try_fixture() {
    // Reference: vineflower/test/org/jetbrains/java/decompiler/SingleClassesTest.java -> TestSwitchInTry
    let class_path = compile_vineflower_source("testData/src/java8/pkg/TestSwitchInTry.java");
    let output = rustyflower::decompile_path(&class_path).expect("fixture should decompile");
    assert!(output.contains("public class TestSwitchInTry"));
    assert!(output.contains("while ("));
    assert!(output.contains("try {"));
    assert!(output.contains("switch ("));
    assert!(output.contains("case \"a\":"));
    assert!(output.contains("catch (java.lang.Exception"));
    assert!(!output.contains("hashCode()"));
    assert_no_unresolved_artifacts(&output);
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
fn decompiles_java1_synchronized_fixture_with_clean_legacy_fallback() {
    let manifest_dir = std::path::Path::new(env!("CARGO_MANIFEST_DIR"));
    let path =
        manifest_dir.join("../vineflower/testData/classes/custom/TestJava1Synchronized.class");
    let output = rustyflower::decompile_path(&path).expect("fixture should decompile");
    assert!(output.contains("public class TestJava1Synchronized"));
    assert!(output.contains("synchronized (this)"));
    assert!(output.contains("while ((var4 < arg0))") || output.contains("while (var4 < arg0)"));
    assert!(
        output.matches("rustyflower: method body decompilation is being implemented incrementally.")
            .count()
            == 2,
        "expected exactly the legacy jsr/ret methods to fall back cleanly:\n{output}"
    );
    assert!(!output.contains("rustyflower: unsupported goto"));
    assert!(!output.contains("<caught-exception>"));
}

#[test]
fn decompiles_vineflower_string_concat_fixture() {
    let class_path = compile_vineflower_source("testData/src/java8/pkg/TestStringConcat.java");
    let output = rustyflower::decompile_path(&class_path).expect("fixture should decompile");
    assert!(output.contains("public class TestStringConcat"));
    assert!(output.contains("return arg0 + arg1;"));
    assert!(output.contains("\"(\" + arg0 + \"-\" + arg1"));
    assert!(!output.contains("makeConcatWithConstants"));
    assert_no_unresolved_artifacts(&output);
}

#[test]
fn decompiles_vineflower_java9_string_concat_fixture() {
    let class_path = compile_vineflower_source("testData/src/java9/pkg/TestJava9StringConcat.java");
    let output = rustyflower::decompile_path(&class_path).expect("fixture should decompile");
    assert!(output.contains("public class TestJava9StringConcat"));
    assert!(output.contains("return \"\" + arg0;"));
    assert!(output.contains("return \"\" + arg0 + arg1;"));
    assert!(!output.contains("makeConcatWithConstants"));
    assert_no_unresolved_artifacts(&output);
}

#[test]
fn decompiles_vineflower_java11_string_concat_fixture() {
    let class_path = compile_vineflower_source("testData/src/java11/pkg/TestJava11StringConcat.java");
    let output = rustyflower::decompile_path(&class_path).expect("fixture should decompile");
    assert!(output.contains("public class TestJava11StringConcat"));
    assert!(output.contains("return \"\" + arg0;"));
    assert!(output.contains("return \"\" + arg0 + arg1;"));
    assert!(!output.contains("makeConcatWithConstants"));
    assert_no_unresolved_artifacts(&output);
}

#[test]
fn decompiles_vineflower_array_foreach_fixture() {
    let class_path = compile_vineflower_source("testData/src/java8/pkg/TestArrayForeach.java");
    let output = rustyflower::decompile_path(&class_path).expect("fixture should decompile");
    assert!(output.contains("public class TestArrayForeach"));
    assert!(
        output.contains("for (int var5 : var1)")
            || (output.contains("while ((var4 < var3))")
                && output.contains("int var5 = var2[var4];")),
        "expected either enhanced-for lowering or a correct indexed array loop:\n{output}"
    );
    assert!(!output.contains("iterator()"));
    assert_no_unresolved_artifacts(&output);
    assert_recompiles_output("TestArrayForeach", &output);
}

#[test]
fn decompiles_vineflower_while_foreach_fixture() {
    let class_path = compile_vineflower_source("testData/src/java8/pkg/TestWhileForeach.java");
    let output = rustyflower::decompile_path(&class_path).expect("fixture should decompile");
    assert!(output.contains("public class TestWhileForeach"));
    assert!(output.contains("for (java.lang.Object var4 : this.objects)"));
    assert!(!output.contains("unsupported goto"));
    assert_no_unresolved_artifacts(&output);
}

#[test]
fn decompiles_vineflower_foreach_multiple_loops_fixture() {
    let class_path = compile_vineflower_source("testData/src/java8/pkg/TestForeachMultipleLoops.java");
    let output = rustyflower::decompile_path(&class_path).expect("fixture should decompile");
    assert!(output.contains("public class TestForeachMultipleLoops"));
    assert!(output.matches("for (").count() >= 2);
    assert!(output.contains("for (java.util.Map.Entry"));
    assert!(output.contains("for (java.lang.String var9 : arg1.values())"));
    assert!(!output.contains("iterator()"));
    assert_no_unresolved_artifacts(&output);
}

#[test]
fn decompiles_vineflower_parameterized_types_fixture() {
    let class_path = compile_vineflower_source("testData/src/java8/pkg/TestParameterizedTypes.java");
    let output = rustyflower::decompile_path(&class_path).expect("fixture should decompile");
    assert!(output.contains("public abstract class TestParameterizedTypes<P>"));
    assert!(output.contains("Inner<java.lang.String> getUnspecificInner();"));
    assert!(output.contains("TestParameterizedTypes<java.lang.Number>.Inner<java.lang.String>"));
    assert_recompiles_output("TestParameterizedTypes", &output);
}

#[test]
fn decompiles_vineflower_inner_class_constructor_fixture() {
    let class_path = compile_vineflower_source("testData/src/java8/pkg/TestInnerClassConstructor.java");
    let output = rustyflower::decompile_path(&class_path).expect("fixture should decompile");
    assert!(output.contains("new Inner(\"text\");"));
    assert!(output.contains("new Another(3, 4);"));
    assert!(output.contains("class Another {"));
    assert!(output.contains("final class Inner {"));
    assert!(!output.contains("Inner(this,"));
    assert!(!output.contains("Another(this,"));
    assert_recompiles_output("TestInnerClassConstructor", &output);
}

#[test]
fn decompiles_vineflower_local_class_fixture() {
    let class_path = compile_vineflower_source("testData/src/java8/pkg/TestLocalClass.java");
    let output = rustyflower::decompile_path(&class_path).expect("fixture should decompile");
    assert!(output.contains("class Local {"));
    assert!(output.contains("class C {"));
    assert!(output.contains("Local var2 = new Local();"));
    assert!(output.contains("java.util.function.Supplier var1 = () -> new C();"));
    assert!(!output.contains("1Local"));
    assert!(!output.contains("1C"));
    assert!(!output.contains("lambda$"));
    assert_recompiles_output("TestLocalClass", &output);
}

#[test]
fn decompiles_vineflower_method_reference_fixture() {
    let class_path = compile_vineflower_source("testData/src/java8/pkg/TestMethodReferenceSameName.java");
    let output = rustyflower::decompile_path(&class_path).expect("fixture should decompile");
    assert!(output.contains("((java.lang.Runnable) tmp0::foo).run();"));
    assert!(!output.contains("java.lang.Object.run("));
    assert!(!output.contains("lambda$"));
    assert_recompiles_output("TestMethodReferenceSameName", &output);
}

#[test]
fn decompiles_vineflower_class_lambda_fixture() {
    let class_path = compile_vineflower_source("testData/src/java8/pkg/TestClassLambda.java");
    let output = rustyflower::decompile_path(&class_path).expect("fixture should decompile");
    assert!(output.contains("var1.forEach((arg0) -> {"));
    assert!(output.contains("java.lang.Runnable var2 = () -> {"));
    assert!(output.contains("pkg.TestClassLambda.reduce(java.lang.Math::max);"));
    assert!(output.contains("pkg.TestClassLambda.function(var1::toString);"));
    assert!(output.contains("java.util.Arrays.stream(arg0).map(java.lang.annotation.Annotation::annotationType);"));
    assert!(!output.contains("lambda$"));
    assert!(!output.contains("java.lang.Object.run("));
    assert_no_unresolved_artifacts(&output);
    assert_recompiles_output("TestClassLambda", &output);
}

#[test]
fn decompiles_vineflower_for_continue_fixture() {
    let class_path = compile_vineflower_source("testData/src/java8/pkg/TestForContinue.java");
    let output = rustyflower::decompile_path(&class_path).expect("fixture should decompile");
    assert!(
        output.contains("for (int var2 = 0; (var2 < arg0); var2 = (var2 + 1))")
            || output.contains("for (int var2 = 0; (var2 < arg0); var2 += 1)")
    );
    assert!(
        output.contains("if ((var2 == 4))") || output.contains("if ((var2 != 4))"),
        "expected either explicit continue or inverted-condition form:\n{output}"
    );
    assert!(
        output.contains("continue;") || output.contains("java.lang.System.out.println(var2);"),
        "expected loop body to preserve continue semantics:\n{output}"
    );
    assert!(!output.contains("unsupported goto"));
    assert_recompiles_output("TestForContinue", &output);
}

#[test]
fn decompiles_vineflower_do_while_true_fixture() {
    let class_path = compile_vineflower_source("testData/src/java8/pkg/TestDoWhileTrue.java");
    let output = rustyflower::decompile_path(&class_path).expect("fixture should decompile");
    assert!(output.contains("do {"));
    assert!(output.contains("} while ((var1 < 100));") || output.contains("} while (var1 < 100);"));
    assert!(!output.contains("unsupported goto"));
    assert_recompiles_output("TestDoWhileTrue", &output);
}

#[test]
fn decompiles_vineflower_array_do_while_fixture() {
    let class_path = compile_vineflower_source("testData/src/java8/pkg/TestArrayDoWhile.java");
    let output = rustyflower::decompile_path(&class_path).expect("fixture should decompile");
    assert!(output.contains("do {"));
    assert!(output.contains("var1[(var2 - 1)] = var2;"));
    assert!(output.contains("} while ((var2 < var1.length));") || output.contains("} while (var2 < var1.length);"));
    assert!(!output.contains("unsupported goto"));
    assert_recompiles_output("TestArrayDoWhile", &output);
}

#[test]
fn decompiles_vineflower_loop_break_fixture() {
    let class_path = compile_vineflower_source("testData/src/java8/pkg/TestLoopBreak.java");
    let output = rustyflower::decompile_path(&class_path).expect("fixture should decompile");
    assert!(output.contains("while ((arg0 > 10))") || output.contains("while (arg0 > 10)"));
    assert!(output.contains("if ((arg0 == 15))") || output.contains("if (arg0 == 15)"));
    assert!(output.contains("break;"));
    assert!(!output.contains("unsupported goto"));
    assert_recompiles_output("TestLoopBreak", &output);
}

#[test]
fn decompiles_vineflower_loop_break_continue_fixture() {
    let class_path = compile_vineflower_source("testData/src/java8/pkg/TestLoopBreak2.java");
    let output = rustyflower::decompile_path(&class_path).expect("fixture should decompile");
    assert!(output.contains("continue;"));
    assert!(output.contains("return true;"));
    assert!(output.contains("return false;"));
    assert!(!output.contains("unsupported goto"));
    assert_recompiles_output("TestLoopBreak2", &output);
}

#[test]
fn decompiles_vineflower_while_condition_fixture() {
    let class_path = compile_vineflower_source("testData/src/java8/pkg/TestWhileCondition.java");
    let output = rustyflower::decompile_path(&class_path).expect("fixture should decompile");
    assert!(output.contains("public class TestWhileCondition"));
    assert!(output.matches("while (").count() >= 2);
    assert!(!output.contains("unsupported goto"));
    assert_recompiles_output("TestWhileCondition", &output);
}

#[test]
fn decompiles_previous_panic_fixtures_without_fallback_comment() {
    for fixture in [
        "testData/src/java8/pkg/TestAmbiguousArraylen.java",
        "testData/src/java8/pkg/TestAssignmentInDoWhile.java",
        "testData/src/java8/pkg/TestAssignmentTernaryConstantSimplification.java",
        "testData/src/java8/pkg/TestGenericCastCall.java",
    ] {
        let class_path = compile_vineflower_source(fixture);
        let output = rustyflower::decompile_path(&class_path).expect("fixture should decompile");
        assert!(
            !output.contains("rustyflower: method body decompilation is being implemented incrementally."),
            "fixture regressed to incremental fallback: {fixture}\n{output}"
        );
    }
}

#[test]
fn decompiles_vineflower_generics_fixture_with_array_casts_and_static_init() {
    let class_path = compile_vineflower_source("testData/src/java8/pkg/TestGenerics.java");
    let output = rustyflower::decompile_path(&class_path).expect("fixture should decompile");
    assert!(output.contains("this.aArray = ((A[]) new java.lang.Object[10]);"));
    assert!(output.contains("this.aArray = ((A[]) new java.lang.Object[20]);"));
    assert!(output.contains(
        "pkg.TestGenerics.field = ((java.util.Map<java.lang.String, java.lang.Boolean>) pkg.TestGenerics.Maps.newHashMap());"
    ));
    assert!(!output.contains("rustyflower: method body decompilation is being implemented incrementally."));
}

#[test]
fn decompiles_vineflower_try_with_resources_fixture_resugars_primary_patterns() {
    let class_path = compile_vineflower_source("testData/src/java8/pkg/TestTryWithResources.java");
    let output = rustyflower::decompile_path(&class_path).expect("fixture should decompile");
    assert!(output.contains("try (java.nio.file.FileSystem var0 ="));
    assert!(output.contains("try (java.io.InputStream var1 ="));
    assert!(!output.contains("catch (java.lang.Throwable var2) {\n        }\n        try {\n            var0.close();"));
}

#[test]
fn decompiles_vineflower_compound_assignment_fixture_resugars_basic_ops() {
    let class_path = compile_vineflower_source("testData/src/java8/pkg/TestCompoundAssignment.java");
    let output = rustyflower::decompile_path(&class_path).expect("fixture should decompile");
    assert!(output.contains("arg0 += arg1;"));
    assert!(output.contains("arg0 += (arg1 + arg2);"));
    assert!(output.contains("arg0 += ((arg1 + arg2) * arg3);"));
    assert!(output.contains("arg2[arg3] = arg1;"));
    assert!(output.contains("arg0 += arg1;"));
}
