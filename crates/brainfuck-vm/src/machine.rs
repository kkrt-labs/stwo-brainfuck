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
        while self.state.registers.ip < BaseField::from(self.program.code.len()) {
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
            self.next_clock_cycle();
        }

        // Last clock cycle
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
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::test_helper::*;
    use stwo_prover::core::fields::m31::P;

    #[test]
    fn test_machine_initialization() {
        // '+'
        let code = vec![BaseField::from(43)];
        let (machine, _) = create_test_machine(code.clone(), &[]);

        assert_eq!(machine.program.code, code);
        assert_eq!(machine.state.ram.len(), 30000);
        assert!(machine.state.ram.iter().all(|&x| x == BaseField::zero()));
    }

    #[test]
    fn test_right_instruction() -> Result<(), Box<dyn Error>> {
        // '>>'
        let code = vec![BaseField::from(62), BaseField::from(62)];
        let (mut machine, _) = create_test_machine(code, &[]);
        machine.execute()?;

        assert_eq!(machine.state.registers.mp, BaseField::from(2));
        Ok(())
    }

    #[test]
    fn test_left_instruction() -> Result<(), Box<dyn Error>> {
        // '>><'
        let code = vec![
            BaseField::from(62),
            BaseField::from(62),
            BaseField::from(60),
        ];
        let (mut machine, _) = create_test_machine(code, &[]);
        machine.execute()?;

        assert_eq!(machine.state.registers.mp, BaseField::from(1));
        Ok(())
    }

    #[test]
    fn test_plus_instruction() -> Result<(), Box<dyn Error>> {
        // '+'
        let code = vec![BaseField::from(43)];
        let (mut machine, _) = create_test_machine(code, &[]);
        machine.execute()?;

        assert_eq!(machine.state.ram[0], BaseField::from(1));
        assert_eq!(machine.state.registers.mv, BaseField::from(1));
        Ok(())
    }
    #[test]

    fn test_minus_instruction() -> Result<(), Box<dyn Error>> {
        // '--'
        let code = vec![BaseField::from(45), BaseField::from(45)];
        let (mut machine, _) = create_test_machine(code, &[]);
        machine.execute()?;

        assert_eq!(machine.state.ram[0], BaseField::from(P - 2));
        assert_eq!(machine.state.registers.mv, BaseField::from(P - 2));
        Ok(())
    }

    #[test]
    fn test_read_write_char() -> Result<(), Box<dyn Error>> {
        // ',.'
        let code = vec![BaseField::from(44), BaseField::from(46)];
        let input = b"a";
        let (mut machine, output) = create_test_machine(code, input);

        machine.execute()?;

        let output_data = output.get_output();
        assert_eq!(output_data, input);
        Ok(())
    }

    #[test]
    fn test_skip_loop() -> Result<(), Box<dyn Error>> {
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
        let (mut machine, _) = create_test_machine(code, &[]);
        machine.execute()?;

        assert_eq!(machine.state.ram[0], BaseField::one());
        assert_eq!(machine.state.registers.mv, BaseField::one());
        Ok(())
    }

    #[test]
    fn test_enter_loop() -> Result<(), Box<dyn Error>> {
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
        let (mut machine, _) = create_test_machine(code, &[]);
        machine.execute()?;

        assert_eq!(machine.state.ram[0], BaseField::from(2));
        assert_eq!(machine.state.registers.mp, BaseField::one());
        assert_eq!(machine.state.registers.mv, BaseField::zero());
        Ok(())
    }

    #[test]
    fn test_get_trace() -> Result<(), Box<dyn Error>> {
        // '++'
        let code = vec![BaseField::from(43), BaseField::from(43)];
        let (mut machine, _) = create_test_machine(code, &[]);
        machine.execute()?;

        // Initial state + executed instructions
        let trace = machine.get_trace();
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
            ci: BaseField::from(0),
            ni: BaseField::from(0),
            mp: BaseField::zero(),
            mv: BaseField::from(2),
            mvi: BaseField::from(2).inverse(),
        };

        assert_eq!(trace.len(), 3);
        assert_eq!(trace[0], initial_state);
        assert_eq!(trace[1], intermediate_state);
        assert_eq!(trace[2], final_state);

        Ok(())
    }

    #[test]
    fn test_pad_trace() -> Result<(), Box<dyn Error>> {
        // '++'
        let code = vec![BaseField::from(43), BaseField::from(43)];
        let (mut machine, _) = create_test_machine(code, &[]);
        machine.execute()?;

        // Initial state + executed instructions
        let trace = machine.get_trace();
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
            ci: BaseField::from(0),
            ni: BaseField::from(0),
            mp: BaseField::zero(),
            mv: BaseField::from(2),
            mvi: BaseField::from(2).inverse(),
        };

        assert_eq!(trace.len(), 3);
        assert_eq!(trace[0], initial_state);
        assert_eq!(trace[1], intermediate_state);
        assert_eq!(trace[2], final_state);

        machine.pad_trace();
        let trace = machine.get_trace();
        let dummy = Registers {
            clk: final_state.clk + BaseField::one(),
            ..final_state
        };

        assert_eq!(trace.len(), 4);
        assert_eq!(trace[0], initial_state);
        assert_eq!(trace[1], intermediate_state);
        assert_eq!(trace[2], final_state);
        assert_eq!(trace[3], dummy);

        Ok(())
    }
}
