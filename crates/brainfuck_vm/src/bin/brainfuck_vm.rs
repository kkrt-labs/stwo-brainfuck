// Adapted from rkdud007 brainfuck-zkvm https://github.com/rkdud007/brainfuck-zkvm/blob/main/src/main.rs

use brainfuck_vm::{
    compiler::Compiler,
    machine::{Machine, MachineError},
};
use clap::{Parser, ValueHint};
use std::{
    fs,
    io::{stdin, stdout},
    path::PathBuf,
};

#[derive(Parser)]
#[clap(author, version, about, long_about = None)]
struct Args {
    #[clap(value_parser, value_hint=ValueHint::FilePath)]
    filename: PathBuf,
    #[clap(long, default_value = "info")]
    log: String,
    #[clap(long)]
    trace: bool,
    #[clap(long)]
    pad_trace: bool,
    #[clap(long)]
    ram_size: Option<usize>,
}

fn main() -> Result<(), MachineError> {
    let args = Args::parse();

    tracing_subscriber::fmt().with_env_filter(args.log).init();

    let code = fs::read_to_string(&args.filename).expect("Failed to read file");
    let mut bf_compiler = Compiler::new(&code);
    let ins = bf_compiler.compile();
    tracing::info!("Assembled instructions: {:?}", ins.iter().map(|x| x.0).collect::<Vec<u32>>());
    tracing::info!("Program execution");
    let stdin = stdin();
    let stdout = stdout();
    let mut bf_vm = match args.ram_size {
        Some(size) => Machine::new_with_config(&ins, stdin, stdout, size)?,
        None => Machine::new(&ins, stdin, stdout)?,
    };
    tracing::info!("Provide inputs separated by linefeeds: ");
    bf_vm.execute().unwrap();
    if args.trace {
        let trace = bf_vm.trace();
        tracing::info!("Execution trace: {:#?}", trace);
    }
    Ok(())
}
