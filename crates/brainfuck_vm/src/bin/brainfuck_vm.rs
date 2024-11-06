// Adapted from rkdud007 brainfuck-zkvm https://github.com/rkdud007/brainfuck-zkvm/blob/main/src/main.rs

use clap::{Parser, ValueHint};
use std::{
    fs,
    io::{stdin, stdout},
    path::PathBuf,
};
use tracing_subscriber::{fmt, EnvFilter};

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

    // Constructs a subscriber whose severity level is filtered by `RUST_LOG`
    fmt().with_env_filter(EnvFilter::from_default_env()).init();

    let code = fs::read_to_string(&args.filename)
        .unwrap_or_else(|_| panic!("Failed to read file"))
        .replace(' ', "");
    let mut bf_compiler = Compiler::new(code);
    let ins = bf_compiler.compile();
    tracing::info!(
        "Assembled instructions: {:?}",
        ins.iter().map(|x| x.0).collect::<Vec<u32>>()
    );
    tracing::info!("Program execution");
    let stdin = stdin();
    let stdout = stdout();
    let mut bf_vm = match args.ram_size {
        Some(size) => Machine::new_with_config(ins, stdin, stdout, size),
        None => Machine::new(ins, stdin, stdout),
    };
    tracing::info!("Provide inputs separated by linefeeds: ");
    bf_vm.execute().unwrap();
    let trace = bf_vm.get_trace();
    if args.print_trace {
        tracing::info!("Execution trace: {:#?}", trace);
        bf_vm.pad_trace();
        let trace = bf_vm.get_trace();
        tracing::info!("Padded execution trace: {:#?}", trace);
    }
    // Ok(())
}
