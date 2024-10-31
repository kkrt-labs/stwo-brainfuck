// Adapted from rkdud007 brainfuck-zkvm https://github.com/rkdud007/brainfuck-zkvm/blob/main/src/main.rs

pub mod compiler;
pub mod instruction;
pub mod machine;
pub mod registers;

use clap::{Parser, ValueHint};
use std::{
    fs,
    io::{stdin, stdout},
    path::PathBuf,
};

use compiler::Compiler;
use machine::Machine;

#[derive(Parser)]
#[clap(author, version, about, long_about = None)]
struct Args {
    #[clap(value_parser, value_hint=ValueHint::FilePath)]
    filename: PathBuf,
    #[structopt(long = "print_trace")]
    print_trace: bool,
}

fn main() {
    let args = Args::parse();

    let code = fs::read_to_string(&args.filename)
        .unwrap_or_else(|_| panic!("Failed to read file"))
        .replace(' ', "");
    let mut bf_compiler = Compiler::new(code);
    let ins = bf_compiler.compile();
    println!("{}", ins.len());
    print!("Assembled Instructions: ");
    print!("[");
    for (index, ins) in ins.iter().enumerate() {
        if index > 0 {
            print!(", ");
        }
        print!("{}", ins);
    }
    println!("]");

    println!("======================== ");
    println!("Brainfuck program execution");
    let stdin = stdin();
    let stdout = stdout();
    let mut bf_vm = Machine::new(ins, stdin, stdout);
    println!("Input: ");
    bf_vm.execute().unwrap();
    println!();
    let traces = bf_vm.get_trace();
    if args.print_trace {
        println!("======================== ");
        println!("Execution trace:");
        for trace in traces {
            println!("{:?}", trace);
        }
    }
}
