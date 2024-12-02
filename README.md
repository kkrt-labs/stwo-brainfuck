# stwo-brainfuck

`stwo-brainfuck` is a ZK-VM for the Brainfuck language[^1], based on Stwo[^2].

## Objectives

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
