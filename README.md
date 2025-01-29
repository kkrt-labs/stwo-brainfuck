# stwo-brainfuck

`stwo-brainfuck` is a ZK-VM for the Brainfuck language[^1], based on Stwo[^2].

## CLI - Installation

Here are the steps to get the Brainfuck ZK-VM up and running.

You can either download the binaries from the [releases](https://github.com/kkrt-labs/stwo-brainfuck/releases), or build them from source.

### Build from Source

1. Clone the repository

```shell
git clone git@github.com:kkrt-labs/stwo-brainfuck.git
```

2. Build the `brainfuck_prover`

The `brainfuck_prover` has a feature flag which enables the CPU parallelization feature of Stwo.

No feature flags:

```shell
cargo build --package brainfuck_prover --release
```

Parallel feature flag:

```shell
cargo build --package brainfuck_prover --features parallel --release
```

## CLI - Usage

The `brainfuck_prover` CLI has two subcommands:

- `prove`, which generates a CSTARK proof from a given Brainfuck program file or code string.
- `verify`, which verify a CSTARK proof from a given Brainfuck proof file.

For more information, try `brainfuck_prover --help`, `brainfuck_prover prove --help` and `brainfuck_prover verify --help`.

### Example usage

Consider this Brainfuck program which, given an ASCII character from Stdin, outputs the following two characters in the ASCII table:

```brainfuck
++>,<[>+.<-]
```

### Prove

To generate a proof of this program, you can provide the Brainfuck program as a string, with the `--code` argument,
or store it in a file `my_program.bf` and provide the path to it with the `--file` argument.

Here, the proof will be serialized to a JSON file `my_program_proof.json`.
You can also print the proof to `stdout` with the `--print` flag.

1. Proof from a Brainfuck program given in the command

```shell
brainfuck_prover prove --code "++>,<[>+.<-]" --output my_program_proof.json
```

Or if you built from source,

```shell
./target/release/brainfuck_prover prove --code "++>,<[>+.<-]" --output my_program_proof.json
```

2. Proof from program file

```shell
brainfuck_prover prove --file my_program.bf --output my_program_proof.json
```

Or if you built from source,

```shell
./target/release/brainfuck_prover prove --file ./brainfuck_programs/hello_kakarot.bf --output hello_kakarot_proof.json
```

### Verify

To verify a proof, the proof must be stored in a JSON file (`--output` flag from the `prove` subcommand).

```shell
brainfuck_prover verify my_program_proof.json
```

Or if you built from source and previously generated the proof of the `hello_kakarot` example:

```shell
./target/release/brainfuck_prover verify hello_kakarot_proof.json
```

### Visualizing the memory

To visualize the memory of the Brainfuck VM, use the `--memory` flag of the `brainfuck_prover`, and reduce the RAM size to avoid printing too much memory cells to your terminal with the `--ram-size` flag.

Let's try it with a Brainfuck program that yields the 19th Fibonacci number. Note that it is a bit more resource intensive than the other example programs.

```shell
./target/release/brainfuck_prover prove --file ./brainfuck_programs/fib19.bf --output fib19_proof.json --memory --ram-size 5
```

You should be able to see:

```shell
[M31(0), M31(2584), M31(4181), M31(0), M31(0)]
```

The third memory cell contains the desired output: `Fibonacci(19) = 4181`.

## Project Objectives

- Capacity of generating and verifying a proof for arbitrary Brainfuck programs.
- Understanding of using Stwo for building ZK-VMs
- Understanding of modern AIR (RAP) design for (C)STARK-based systems.

## Design choices

### Brainfuck VM

The Brainfuck language has a very loose specification, though,
a [general specification](https://esolangs.org/wiki/Brainfuck#Conventions) has been established as a minimal base.
We try to follow these guidelines.

- The memory cells take values in the Mersenne31 (M31) field: $[0..2^{31} - 1)$
- Memory is fixed at 30,000 cells by default, but is configurable.
- Memory wraps on overflow/underflow.
  - It can be used for memory value `mv` and memory pointer `mp`,
    but it will usually panic for `mp` as the memory size will be much smaller than $2^{31} - 1$.
- Inputs are line-buffered (ends with the linefeed ASCII character `10`).
- CLI uses Stdin and Stdout for IO.
- For library use, input can be simulated by any reader (e.g. `Cursor`) and
  output with any writer (e.g. a custom writer).

## Acknowledgements

The constraints used here rely on work made by Alan Szepieniec[^3]
and sibling article from Neptune Cash[^4].
The Brainfuck compiler and interpreter have been adapted from rkdud007[^5]

[^1]: [Brainfuck Language](https://esolangs.org/wiki/Brainfuck)

[^2]: [Stwo repository](https://github.com/starkware-libs/stwo)

[^3]: [BrainSTARK - Alan Szepieniec](https://aszepieniec.github.io/stark-brainfuck/)

[^4]: [BrainSTARK - Neptune Cash](https://neptune.cash/learn/brainfuck-tutorial)

[^5]: [rkdud007 brainfuck-zkvm repo](https://github.com/rkdud007/brainfuck-zkvm)
