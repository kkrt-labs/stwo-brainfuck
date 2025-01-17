use brainfuck_prover::brainfuck_air::{prove_brainfuck, verify_brainfuck};
use brainfuck_vm::{compiler::Compiler, machine::Machine};
use clap::{ArgGroup, Parser, Subcommand, ValueHint};
use std::{
    fs::{self, File},
    io::{stdin, stdout, Write},
    path::PathBuf,
    time::Instant,
};
use stwo_prover::core::prover::ProvingError;

#[derive(Parser, Debug)]
#[command(author, version, about, long_about = None)]
struct Cli {
    #[command(subcommand)]
    command: Commands,
}

#[derive(Subcommand, Debug)]
enum Commands {
    /// Generate a proof
    #[command(group(
        ArgGroup::new("input_mode")
            .args(["file", "code"])
            .required(true),
    ))]
    #[command(group(
        ArgGroup::new("output_mode")
            .args(["output", "print"]),
    ))]
    Prove {
        /// Path to the Brainfuck program file.
        #[clap(value_parser, long, value_hint=ValueHint::FilePath)]
        file: Option<PathBuf>,
        /// Direct Brainfuck code input.
        #[clap(long)]
        code: Option<String>,
        /// Log Level.
        #[clap(long, default_value = "info")]
        log: String,
        /// Print the Brainfuck VM execution trace.
        #[clap(long)]
        trace: bool,
        /// Print the Brainfuck VM memory.
        #[clap(long)]
        memory: bool,
        /// Configure the size of the memory.
        #[clap(long)]
        ram_size: Option<usize>,
        /// Export the output to the provided filepath.
        #[clap(short, long)]
        output: Option<PathBuf>,
        /// Print the output to stdout.
        #[arg(long)]
        print: bool,
    },
    /// Verify a proof
    Verify {
        /// Path to the CSTARK proof of the Brainfuck program execution.
        #[clap(value_parser, value_hint=ValueHint::FilePath)]
        filename: PathBuf,
        /// Log Level.
        #[clap(long, default_value = "info")]
        log: String,
    },
}

struct ExecutionConfig {
    file: Option<PathBuf>,
    code: Option<String>,
    trace: bool,
    memory: bool,
    ram_size: Option<usize>,
    output: Option<PathBuf>,
    print: bool,
}

/// Generate a CSTARK Proof from a given Brainfuck filepath.
fn prove(execution_config: ExecutionConfig) -> Result<(), ProvingError> {
    tracing::info!("Program compilation");

    let code = if let Some(path) = execution_config.file {
        fs::read_to_string(path).expect("Failed to read file")
    } else {
        execution_config.code.unwrap()
    };

    let mut bf_compiler = Compiler::new(&code);
    let ins = bf_compiler.compile();

    tracing::info!("Program execution");
    let stdin = stdin();
    let stdout = stdout();
    let mut bf_vm = match execution_config.ram_size {
        Some(size) => Machine::new_with_config(&ins, stdin, stdout, size).unwrap(),
        None => Machine::new(&ins, stdin, stdout).unwrap(),
    };

    tracing::info!("Provide inputs if any:");
    let trace_start = Instant::now();
    bf_vm.execute().unwrap();
    let trace = bf_vm.trace();
    let trace_duration = trace_start.elapsed();
    let steps = trace.len();
    let trace_mhz = (steps as f64) / trace_duration.as_secs_f64() / 1_000_000.0;
    tracing::info!("Steps: {}", steps);
    tracing::info!("Trace generation speed: {:.2} MHz", trace_mhz);

    if execution_config.trace {
        tracing::info!("Execution Trace");
        println!("{trace:#?}");
    }

    if execution_config.memory {
        tracing::info!("Memory");
        println!("{:?}", bf_vm.memory());
    }

    tracing::info!("Proof Generation");
    let proof_start = Instant::now();
    let bf_proof = prove_brainfuck(&bf_vm)?;
    let proof_duration = proof_start.elapsed();
    let proof_mhz = (steps as f64) / proof_duration.as_secs_f64() / 1_000_000.0;
    tracing::info!("Proof successfully generated!");
    tracing::info!("Proof generation speed: {:.2} MHz", proof_mhz);

    if let Some(path) = execution_config.output {
        tracing::info!("Exporting Proof");
        let json_bf_proof = serde_json::to_string(&bf_proof).unwrap();
        let mut file = File::create(&path).unwrap();
        file.write_all(json_bf_proof.as_bytes()).unwrap();
    } else if execution_config.print {
        tracing::info!("Printing Proof");
        println!("{bf_proof:#?}");
    }

    tracing::info!("Trace execution time: {:.2}s", trace_duration.as_secs_f64());
    tracing::info!("Proof generation time: {:.2}s", proof_duration.as_secs_f64());
    tracing::info!("Total execution time: {:.2}s", (trace_duration + proof_duration).as_secs_f64());

    Ok(())
}

/// Verify a CSTARK Proof for the Brainfuck ZK-VM from the proof filepath.
fn verify(path: &PathBuf) {
    tracing::info!("Reading Proof from file");
    let bf_proof_str = fs::read_to_string(path).expect("Failed to read file");
    let bf_proof = serde_json::from_str(&bf_proof_str).unwrap();

    tracing::info!("Proof Verification");
    verify_brainfuck(bf_proof).unwrap();
}

fn main() {
    let cli = Cli::parse();

    match &cli.command {
        Commands::Prove { file, code, log, trace, memory, ram_size, output, print } => {
            tracing_subscriber::fmt().with_env_filter(log).init();
            tracing::info!("Brainfuck ZK-VM - Prove");
            let execution_config = ExecutionConfig {
                file: file.clone(),
                code: code.clone(),
                trace: *trace,
                memory: *memory,
                ram_size: *ram_size,
                output: output.clone(),
                print: *print,
            };

            prove(execution_config).unwrap();
        }
        Commands::Verify { filename, log } => {
            tracing_subscriber::fmt().with_env_filter(log).init();
            tracing::info!("Brainfuck ZK-VM - Verify");
            verify(filename);
            tracing::info!("Verification succeed!");
        }
    }
}
