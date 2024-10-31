use std::{fmt::Display, str::FromStr};

#[derive(Debug, Clone)]
pub struct Instruction {
    pub ins_type: InstructionType,
    pub argument: u8,
}

#[derive(PartialEq, Debug, Clone)]
pub enum InstructionType {
    // '>': Increment the data pointer (to point to the next cell to the right).
    Right,
    // '<': Decrement the data pointer (to point to the next cell to the left).
    Left,
    // '+': Increment (increase by one) the byte at the data pointer.
    Plus,
    // '-': Decrement (decrease by one) the byte at the data pointer.
    Minus,
    // '.': Output the byte at the data pointer.
    PutChar,
    // ',': Accept one byte of input, storing its value in the byte at the data pointer.
    ReadChar,
    // '[': If the byte at the data pointer is zero, then instead of moving the instruction pointer forward to the next command, jump it forward to the command after the matching ']' command.
    JumpIfZero,
    // ']': If the byte at the data pointer is nonzero, then instead of moving the instruction pointer forward to the next command, jump it back to the command after the matching '[' command.
    JumpIfNotZero,
}

impl FromStr for InstructionType {
    type Err = ();

    fn from_str(s: &str) -> Result<Self, Self::Err> {
        match s {
            ">" => Ok(InstructionType::Right),
            "<" => Ok(InstructionType::Left),
            "+" => Ok(InstructionType::Plus),
            "-" => Ok(InstructionType::Minus),
            "." => Ok(InstructionType::PutChar),
            "," => Ok(InstructionType::ReadChar),
            "[" => Ok(InstructionType::JumpIfZero),
            "]" => Ok(InstructionType::JumpIfNotZero),
            _ => Err(()),
        }
    }
}

impl Display for InstructionType {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let symbol = match self {
            InstructionType::Right => ">",
            InstructionType::Left => "<",
            InstructionType::Plus => "+",
            InstructionType::Minus => "-",
            InstructionType::PutChar => ".",
            InstructionType::ReadChar => ",",
            InstructionType::JumpIfZero => "[",
            InstructionType::JumpIfNotZero => "]",
        };
        write!(f, "{}", symbol)
    }
}

impl InstructionType {
    pub fn from_u8(ins: u8) -> Self {
        Self::from_str(&(ins as char).to_string()).expect("Invalid instruction")
    }
}
