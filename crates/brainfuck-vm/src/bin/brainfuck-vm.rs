// Adapted from rkdud007 brainfuck-zkvm https://github.com/rkdud007/brainfuck-zkvm/blob/main/src/main.rs

use clap::{Parser, ValueHint};
use std::{
    fs,
    io::{stdin, stdout},
    path::PathBuf,
};

use brainfuck_vm::{compiler::Compiler, machine::Machine};

#[derive(Parser)]
#[clap(author, version, about, long_about = None)]
struct Args {
    #[clap(value_parser, value_hint=ValueHint::FilePath)]
    filename: PathBuf,
    #[clap(long)]
    print_trace: bool,
    #[clap(long)]
    ram_size: Option<usize>,
}

fn main() {
    let args = Args::parse();

    let code = fs::read_to_string(&args.filename)
        .unwrap_or_else(|_| panic!("Failed to read file"))
        .replace(' ', "");
    let mut bf_compiler = Compiler::new(code);
    let ins = bf_compiler.compile();
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
    let mut bf_vm = match args.ram_size {
        Some(size) => Machine::new_with_config(ins, stdin, stdout, size),
        None => Machine::new(ins, stdin, stdout),
    };
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
        println!("======================== ");
        println!("Padded Execution trace:");
        bf_vm.pad_trace();
        let traces = bf_vm.get_trace();
        for trace in traces {
            println!("{:?}", trace);
        }
    }
}
