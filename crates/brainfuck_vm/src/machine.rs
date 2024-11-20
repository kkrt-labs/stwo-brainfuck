// Adapted from rkdud007 brainfuck-zkvm https://github.com/rkdud007/brainfuck-zkvm/blob/main/src/machine.rs

use crate::{
    instruction::{InstructionError, InstructionType},
    registers::Registers,
};
use num_traits::identities::{One, Zero};
use std::io::{Read, Write};
use stwo_prover::core::fields::{m31::BaseField, FieldExpOps};
use thiserror::Error;

/// Custom error type for the Machine.
#[derive(Debug, Error)]
pub enum MachineError {
    /// I/O operation failed.
    #[error("I/O operation failed: {0}")]
    IoError(#[from] std::io::Error),

    /// Instructions related error.
    #[error("Instruction error: {0}")]
    Instruction(#[from] InstructionError),
}

pub struct MachineBuilder {
    code: Vec<BaseField>,
    input: Option<Box<dyn Read>>,
    output: Option<Box<dyn Write>>,
    ram_size: usize,
}

impl MachineBuilder {
    /// Creates a new [`MachineBuilder`] with the specified code.
    pub fn new(code: &[BaseField]) -> Self {
        Self { code: code.to_vec(), input: None, output: None, ram_size: Machine::DEFAULT_RAM_SIZE }
    }

    /// Sets the input stream for the machine.
    #[must_use]
    pub fn with_input<R: Read + 'static>(mut self, input: R) -> Self {
        self.input = Some(Box::new(input));
        self
    }

    /// Sets the output stream for the machine.
    #[must_use]
    pub fn with_output<W: Write + 'static>(mut self, output: W) -> Self {
        self.output = Some(Box::new(output));
        self
    }

    /// Sets the RAM size for the machine.
    #[must_use]
    pub const fn with_ram_size(mut self, ram_size: usize) -> Self {
        self.ram_size = ram_size;
        self
    }

    /// Builds the [`Machine`] instance with the provided configuration.
    pub fn build(self) -> Result<Machine, MachineError> {
        if self.input.is_none() || self.output.is_none() {
            return Err(std::io::Error::new(
                std::io::ErrorKind::Other,
                "Input and output streams must be provided",
            )
            .into());
        }

        Ok(Machine {
            program: ProgramMemory { code: self.code },
            state: MutableState {
                ram: vec![BaseField::zero(); self.ram_size],
                registers: Registers::new(),
            },
            io: IO { input: self.input.unwrap(), output: self.output.unwrap() },
            trace: vec![],
        })
    }
}

#[derive(Debug, Default, PartialEq, Eq)]
pub struct ProgramMemory {
    code: Vec<BaseField>,
}

impl ProgramMemory {
    pub fn new(code: Vec<BaseField>) -> Self {
        Self { code }
    }

    pub fn code(&self) -> &[BaseField] {
        &self.code
    }
}

#[derive(Debug, Default, PartialEq, Eq)]
pub struct MutableState {
    ram: Vec<BaseField>,
    registers: Registers,
}

pub struct IO {
    input: Box<dyn Read>,
    output: Box<dyn Write>,
}

pub struct Machine {
    program: ProgramMemory,
    state: MutableState,
    io: IO,
    trace: Vec<Registers>,
}

impl Machine {
    pub const DEFAULT_RAM_SIZE: usize = 30000;

    pub fn new_with_config<R, W>(
        code: &[BaseField],
        input: R,
        output: W,
        ram_size: usize,
    ) -> Result<Self, MachineError>
    where
        R: Read + 'static,
        W: Write + 'static,
    {
        MachineBuilder::new(code)
            .with_input(input)
            .with_output(output)
            .with_ram_size(ram_size)
            .build()
    }

    pub fn new<R, W>(code: &[BaseField], input: R, output: W) -> Result<Self, MachineError>
    where
        R: Read + 'static,
        W: Write + 'static,
    {
        MachineBuilder::new(code).with_input(input).with_output(output).build()
    }

    pub fn execute(&mut self) -> Result<(), MachineError> {
        while self.state.registers.ip < BaseField::from(self.program.code.len()) {
            self.state.registers.ci = self.program.code[self.state.registers.ip.0 as usize];
            self.state.registers.ni =
                if self.state.registers.ip == BaseField::from(self.program.code.len() - 1) {
                    BaseField::zero()
                } else {
                    self.program.code[(self.state.registers.ip + BaseField::one()).0 as usize]
                };
            self.write_trace();
            let ins_type = InstructionType::try_from(self.state.registers.ci.0 as u8)?;
            self.execute_instruction(&ins_type)?;
            self.next_clock_cycle();
        }

        // Last clock cycle
        self.state.registers.ci = BaseField::zero();
        self.state.registers.ni = BaseField::zero();
        self.write_trace();
        Ok(())
    }

    fn read_char(&mut self) -> Result<(), MachineError> {
        let mut buf = [0; 1];
        self.io.input.read_exact(&mut buf)?;
        let input_char = buf[0] as usize;
        self.state.ram[self.state.registers.mp.0 as usize] = BaseField::from(input_char as u32);
        Ok(())
    }

    fn write_char(&mut self) -> Result<(), MachineError> {
        let char_to_write = self.state.ram[self.state.registers.mp.0 as usize].0 as u8;
        self.io.output.write_all(&[char_to_write])?;
        Ok(())
    }

    fn execute_instruction(&mut self, ins: &InstructionType) -> Result<(), MachineError> {
        match ins {
            InstructionType::Right => {
                self.state.registers.mp += BaseField::one();
            }
            InstructionType::Left => {
                self.state.registers.mp -= BaseField::one();
            }
            InstructionType::Plus => {
                let mp = self.state.registers.mp;
                self.state.ram[mp.0 as usize] += BaseField::one();
            }
            InstructionType::Minus => {
                let mp = self.state.registers.mp;
                self.state.ram[mp.0 as usize] -= BaseField::one();
            }
            InstructionType::ReadChar => {
                self.read_char()?;
            }
            InstructionType::PutChar => {
                self.write_char()?;
            }
            InstructionType::JumpIfZero => {
                let mp = self.state.registers.mp;
                let ip = self.state.registers.ip;
                let argument = self.program.code[(ip + BaseField::one()).0 as usize];
                self.state.registers.ni = argument;
                if self.state.ram[mp.0 as usize] == BaseField::zero() {
                    self.state.registers.ip = argument;
                    return Ok(());
                }
                self.state.registers.ip += BaseField::one();
            }
            InstructionType::JumpIfNotZero => {
                let mp = self.state.registers.mp;
                let ip = self.state.registers.ip;
                let argument = self.program.code[(ip + BaseField::one()).0 as usize];
                if self.state.ram[mp.0 as usize] != BaseField::zero() {
                    self.state.registers.ip = argument - BaseField::one();
                    return Ok(());
                }
                self.state.registers.ip += BaseField::one();
            }
        }
        self.state.registers.mv = self.state.ram[self.state.registers.mp.0 as usize];
        self.state.registers.mvi = if self.state.registers.mv == BaseField::zero() {
            BaseField::zero()
        } else {
            self.state.registers.mv.inverse()
        };

        Ok(())
    }

    fn next_clock_cycle(&mut self) {
        self.state.registers.clk += BaseField::one();
        self.state.registers.ip += BaseField::one();
    }

    fn write_trace(&mut self) {
        self.trace.push(self.state.registers.clone());
    }

    pub fn trace(&self) -> Vec<Registers> {
        self.trace.clone()
    }

    pub fn pad_trace(&mut self) {
        let last_register = &self.state.registers;
        let trace_len = self.trace.len() as u32;
        let padding_offset = trace_len.next_power_of_two() + 1 - trace_len;
        for i in 1..padding_offset {
            let dummy = Registers {
                clk: BaseField::from(last_register.clk.0 + i),
                ..last_register.clone()
            };
            self.trace.push(dummy);
        }
    }

    pub const fn program(&self) -> &ProgramMemory {
        &self.program
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::test_helper::*;
    use stwo_prover::core::fields::m31::P;

    #[test]
    fn test_default_machine_initialization() {
        let code = vec![BaseField::from(43)];
        let (machine, _) = create_test_machine(&code, &[]);

        assert_eq!(machine.program, ProgramMemory { code });
        assert_eq!(
            machine.state,
            MutableState {
                ram: vec![BaseField::zero(); Machine::DEFAULT_RAM_SIZE],
                ..Default::default()
            }
        );
    }

    #[test]
    fn test_custom_ram_machine_initialization() {
        let code = vec![BaseField::from(43)];
        let input: &[u8] = &[];
        let output = TestWriter::new();
        let ram_size = 55000;
        let machine = Machine::new_with_config(&code, input, output, ram_size)
            .expect("Machine creation failed");

        assert_eq!(machine.program, ProgramMemory { code });
        assert_eq!(
            machine.state,
            MutableState { ram: vec![BaseField::zero(); ram_size], ..Default::default() }
        );
    }

    #[test]
    fn test_right_instruction() -> Result<(), MachineError> {
        // '>>'
        let code = vec![BaseField::from(62), BaseField::from(62)];
        let (mut machine, _) = create_test_machine(&code, &[]);
        machine.execute()?;

        assert_eq!(machine.program, ProgramMemory { code });
        assert_eq!(machine.state.registers.mp, BaseField::from(2));
        Ok(())
    }

    #[test]
    fn test_left_instruction() -> Result<(), MachineError> {
        // '>><'
        let code = vec![BaseField::from(62), BaseField::from(62), BaseField::from(60)];
        let (mut machine, _) = create_test_machine(&code, &[]);
        machine.execute()?;

        assert_eq!(machine.state.registers.mp, BaseField::one());
        Ok(())
    }

    #[test]
    fn test_plus_instruction() -> Result<(), MachineError> {
        // '+'
        let code = vec![BaseField::from(43)];
        let (mut machine, _) = create_test_machine(&code, &[]);
        machine.execute()?;

        assert_eq!(machine.state.ram[0], BaseField::one());
        assert_eq!(machine.state.registers.mv, BaseField::one());
        Ok(())
    }

    #[test]
    fn test_minus_instruction() -> Result<(), MachineError> {
        // '--'
        let code = vec![BaseField::from(45), BaseField::from(45)];
        let (mut machine, _) = create_test_machine(&code, &[]);
        machine.execute()?;

        assert_eq!(machine.state.ram[0], BaseField::from(P - 2));
        assert_eq!(machine.state.registers.mv, BaseField::from(P - 2));
        Ok(())
    }

    #[test]
    fn test_read_write_char() -> Result<(), MachineError> {
        // ',.'
        let code = vec![BaseField::from(44), BaseField::from(46)];
        let input = b"a";
        let (mut machine, output) = create_test_machine(&code, input);

        machine.execute()?;

        let output_data = output.get_output();
        assert_eq!(output_data, input);
        Ok(())
    }

    #[test]
    fn test_skip_loop() -> Result<(), MachineError> {
        // Skip the loop
        // '[-]+'
        let code = vec![
            BaseField::from(91),
            BaseField::from(4),  // Jump to index 5 if zero
            BaseField::from(45), // This should be skipped
            BaseField::from(93),
            BaseField::from(2),
            BaseField::from(43),
        ];
        let (mut machine, _) = create_test_machine(&code, &[]);
        machine.execute()?;

        assert_eq!(machine.state.ram[0], BaseField::one());
        assert_eq!(machine.state.registers.mv, BaseField::one());
        Ok(())
    }

    #[test]
    fn test_enter_loop() -> Result<(), MachineError> {
        // Enter the loop
        // '+[+>]'
        let code = vec![
            BaseField::from(43),
            BaseField::from(91),
            BaseField::from(6),
            BaseField::from(43),
            BaseField::from(62),
            BaseField::from(93),
            BaseField::from(3),
        ];
        let (mut machine, _) = create_test_machine(&code, &[]);
        machine.execute()?;

        assert_eq!(machine.state.ram[0], BaseField::from(2));
        assert_eq!(machine.state.registers.mp, BaseField::one());
        assert_eq!(machine.state.registers.mv, BaseField::zero());
        Ok(())
    }

    #[test]
    fn test_trace() -> Result<(), MachineError> {
        // '++'
        let code = vec![BaseField::from(43), BaseField::from(43)];
        let (mut machine, _) = create_test_machine(&code, &[]);
        machine.execute()?;

        // Initial state + executed instructions
        let trace = machine.trace();
        let initial_state = Registers {
            clk: BaseField::zero(),
            ip: BaseField::zero(),
            ci: BaseField::from(43),
            ni: BaseField::from(43),
            mp: BaseField::zero(),
            mv: BaseField::zero(),
            mvi: BaseField::zero(),
        };
        let intermediate_state = Registers {
            clk: BaseField::one(),
            ip: BaseField::one(),
            ci: BaseField::from(43),
            ni: BaseField::zero(),
            mp: BaseField::zero(),
            mv: BaseField::one(),
            mvi: BaseField::one(),
        };
        let final_state = Registers {
            clk: BaseField::from(2),
            ip: BaseField::from(2),
            ci: BaseField::zero(),
            ni: BaseField::zero(),
            mp: BaseField::zero(),
            mv: BaseField::from(2),
            mvi: BaseField::from(2).inverse(),
        };

        assert_eq!(trace, vec![initial_state, intermediate_state, final_state]);
        Ok(())
    }

    #[test]
    fn test_pad_trace() -> Result<(), MachineError> {
        // '++'
        let code = vec![BaseField::from(43), BaseField::from(43)];
        let (mut machine, _) = create_test_machine(&code, &[]);
        machine.execute()?;

        // Initial state + executed instructions
        let trace = machine.trace();
        let initial_state = Registers {
            clk: BaseField::zero(),
            ip: BaseField::zero(),
            ci: BaseField::from(43),
            ni: BaseField::from(43),
            mp: BaseField::zero(),
            mv: BaseField::zero(),
            mvi: BaseField::zero(),
        };
        let intermediate_state = Registers {
            clk: BaseField::one(),
            ip: BaseField::one(),
            ci: BaseField::from(43),
            ni: BaseField::zero(),
            mp: BaseField::zero(),
            mv: BaseField::one(),
            mvi: BaseField::one(),
        };
        let final_state = Registers {
            clk: BaseField::from(2),
            ip: BaseField::from(2),
            ci: BaseField::zero(),
            ni: BaseField::zero(),
            mp: BaseField::zero(),
            mv: BaseField::from(2),
            mvi: BaseField::from(2).inverse(),
        };

        assert_eq!(trace.len(), 3);
        assert_eq!(trace[0], initial_state);
        assert_eq!(trace[1], intermediate_state);
        assert_eq!(trace[2], final_state);

        machine.pad_trace();
        let trace = machine.trace();
        let dummy = Registers { clk: final_state.clk + BaseField::one(), ..final_state };

        assert_eq!(trace.len(), 4);
        assert_eq!(trace[0], initial_state);
        assert_eq!(trace[1], intermediate_state);
        assert_eq!(trace[2], final_state);
        assert_eq!(trace[3], dummy);

        Ok(())
    }
}
