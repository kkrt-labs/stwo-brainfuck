use brainfuck_vm::{compiler::Compiler, test_helper::*};
use std::fs;
use stwo_prover::core::fields::m31::BaseField;

fn compile_from_path(path: &str) -> Vec<BaseField> {
    let code =
        fs::read_to_string(path).unwrap_or_else(|_| panic!("Failed to read file")).replace(' ', "");
    let mut bf_compiler = Compiler::new(&code);
    bf_compiler.compile()
}

#[test]
fn test_a_bc() {
    let path = "../../brainfuck_programs/a-bc.bf";

    let code = compile_from_path(path);
    let input = b"a";
    let (mut machine, output) = create_test_machine(&code, input);
    machine.execute().unwrap();
    let expected_output = b"bc".to_vec();
    assert_eq!(output.get_output(), expected_output);
}

#[test]
fn test_collatz() {
    let path = "../../brainfuck_programs/collatz.bf";

    let code = compile_from_path(path);
    let input = &[0x37, 10]; // 7 EOF
    let (mut machine, output) = create_test_machine(&code, input);
    machine.execute().unwrap();
    let expected_output = [0x31, 0x36, 10].to_vec(); // 16 EOF
    assert_eq!(output.get_output(), expected_output);
}

#[test]
fn test_hello_world_1() {
    let path = "../../brainfuck_programs/hello1.bf";

    let code = compile_from_path(path);
    let (mut machine, output) = create_test_machine(&code, &[]);
    machine.execute().unwrap();
    let expected_output = b"Hello World!\n".to_vec();
    assert_eq!(output.get_output(), expected_output);
}

#[test]
fn test_hello_world_2() {
    let path = "../../brainfuck_programs/hello2.bf";

    let code = compile_from_path(path);
    let (mut machine, output) = create_test_machine(&code, &[]);
    machine.execute().unwrap();
    let expected_output = b"Hello World!\n".to_vec();
    assert_eq!(output.get_output(), expected_output);
}

#[test]
fn test_hello_world_3() {
    let path = "../../brainfuck_programs/hello3.bf";

    let code = compile_from_path(path);
    let (mut machine, output) = create_test_machine(&code, &[]);
    machine.execute().unwrap();
    let expected_output = b"Hello, World!\n".to_vec();
    assert_eq!(output.get_output(), expected_output);
}

#[test]
fn test_hello_world_4() {
    let path = "../../brainfuck_programs/hello4.bf";

    let code = compile_from_path(path);
    let (mut machine, output) = create_test_machine(&code, &[]);
    machine.execute().unwrap();
    let expected_output = b"Hello World!\n".to_vec();
    assert_eq!(output.get_output(), expected_output);
}
