// Adapted from rkdud007 brainfuck-zkvm https://github.com/rkdud007/brainfuck-zkvm/blob/main/src/machine.rs

use std::{
    error::Error,
    io::{Read, Write},
};

use num_traits::identities::{One, Zero};

use stwo_prover::core::fields::{m31::BaseField, FieldExpOps};

use crate::{instruction::InstructionType, registers::Registers};

pub struct ProgramMemory {
    code: Vec<BaseField>,
}

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
    pub fn new<R, W>(code: Vec<BaseField>, input: R, output: W) -> Machine
    where
        R: Read + 'static,
        W: Write + 'static,
    {
        Machine {
            program: ProgramMemory { code },
            state: MutableState {
                ram: vec![BaseField::zero(); 30000],
                registers: Registers::new(),
            },
            io: IO {
                input: Box::new(input),
                output: Box::new(output),
            },
            trace: vec![],
        }
    }

    pub fn execute(&mut self) -> Result<(), Box<dyn Error>> {
        // =============================
        // First clock cycle
        // =============================
        self.state.registers.ci = self.program.code[self.state.registers.ip.0 as usize];
        self.state.registers.ni =
            self.program.code[(self.state.registers.ip + BaseField::one()).0 as usize];
        let target_ci = self.state.registers.ci;
        let ins_type = InstructionType::from_u8(target_ci.0 as u8);
        self.write_trace();
        self.execute_instruction(ins_type)?;

        while self.state.registers.ip < BaseField::from(self.program.code.len() - 1) {
            // ============================
            // Middle clock cycles
            // ============================
            self.next_clock_cycle();
            self.state.registers.ci = self.program.code[self.state.registers.ip.0 as usize];
            self.state.registers.ni =
                if self.state.registers.ip == BaseField::from(self.program.code.len() - 1) {
                    BaseField::zero()
                } else {
                    self.program.code[(self.state.registers.ip + BaseField::one()).0 as usize]
                };
            self.write_trace();
            let ins_type = InstructionType::from_u8(self.state.registers.ci.0 as u8);
            self.execute_instruction(ins_type)?;
        }

        // ============================
        // Last clock cycle
        // ============================
        self.next_clock_cycle();
        self.state.registers.ci = BaseField::zero();
        self.state.registers.ni = BaseField::zero();
        self.write_trace();
        Ok(())
    }

    fn read_char(&mut self) -> Result<(), std::io::Error> {
        let mut buf = [0; 1];
        self.io.input.read_exact(&mut buf)?;
        let input_char = buf[0] as usize;
        self.state.ram[self.state.registers.mp.0 as usize] = BaseField::from(input_char as u32);
        Ok(())
    }

    fn write_char(&mut self) -> Result<(), std::io::Error> {
        let char_to_write = self.state.ram[self.state.registers.mp.0 as usize].0 as u8;
        self.io.output.write_all(&[char_to_write])?;
        Ok(())
    }

    fn execute_instruction(&mut self, ins: InstructionType) -> Result<(), Box<dyn Error>> {
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

    pub fn get_trace(&self) -> Vec<Registers> {
        self.trace.clone()
    }
}
