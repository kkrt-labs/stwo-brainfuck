// Taken from rkdud007 brainfuck-zkvm https://github.com/rkdud007/brainfuck-zkvm/blob/main/src/instruction.rs

use std::{fmt::Display, str::FromStr};
use thiserror::Error;

/// Custom error type for instructions
#[derive(Debug, Error, PartialEq, Eq)]
pub enum InstructionError {
    /// Error when converting a character to an instruction
    #[error("Value `{0}` is not a valid instruction")]
    Conversion(char),
}

#[derive(Debug, Clone)]
pub struct Instruction {
    pub ins_type: InstructionType,
    pub argument: u8,
}

#[derive(PartialEq, Eq, Debug, Clone)]
pub enum InstructionType {
    /// '>': Increment the data pointer (to point to the next cell to the right).
    Right,
    /// '<': Decrement the data pointer (to point to the next cell to the left).
    Left,
    /// '+': Increment (increase by one) the byte at the data pointer.
    Plus,
    /// '-': Decrement (decrease by one) the byte at the data pointer.
    Minus,
    /// '.': Output the byte at the data pointer.
    PutChar,
    /// ',': Accept one byte of input, storing its value in the byte at the data pointer.
    ReadChar,
    /// '[': If the byte at the data pointer is zero, then instead of moving the instruction
    /// pointer forward to the next command, jump it forward to the command after the matching ']'
    /// command.
    JumpIfZero,
    /// ']': If the byte at the data pointer is nonzero, then instead of moving the instruction
    /// pointer forward to the next command, jump it back to the command after the matching '['
    /// command.
    JumpIfNotZero,
}

impl FromStr for InstructionType {
    type Err = ();

    fn from_str(s: &str) -> Result<Self, Self::Err> {
        match s {
            ">" => Ok(Self::Right),
            "<" => Ok(Self::Left),
            "+" => Ok(Self::Plus),
            "-" => Ok(Self::Minus),
            "." => Ok(Self::PutChar),
            "," => Ok(Self::ReadChar),
            "[" => Ok(Self::JumpIfZero),
            "]" => Ok(Self::JumpIfNotZero),
            _ => Err(()),
        }
    }
}

impl Display for InstructionType {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let symbol = match self {
            Self::Right => ">",
            Self::Left => "<",
            Self::Plus => "+",
            Self::Minus => "-",
            Self::PutChar => ".",
            Self::ReadChar => ",",
            Self::JumpIfZero => "[",
            Self::JumpIfNotZero => "]",
        };
        write!(f, "{symbol}")
    }
}

impl TryFrom<u8> for InstructionType {
    type Error = InstructionError;

    fn try_from(value: u8) -> Result<Self, Self::Error> {
        Self::from_str(&(value as char).to_string())
            .map_err(|_| InstructionError::Conversion(value as char))
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    // Test FromStr implementation
    #[test]
    fn test_instruction_type_from_str() {
        // Test valid instruction mappings
        assert_eq!(InstructionType::from_str(">").unwrap(), InstructionType::Right);
        assert_eq!(InstructionType::from_str("<").unwrap(), InstructionType::Left);
        assert_eq!(InstructionType::from_str("+").unwrap(), InstructionType::Plus);
        assert_eq!(InstructionType::from_str("-").unwrap(), InstructionType::Minus);
        assert_eq!(InstructionType::from_str(".").unwrap(), InstructionType::PutChar);
        assert_eq!(InstructionType::from_str(",").unwrap(), InstructionType::ReadChar);
        assert_eq!(InstructionType::from_str("[").unwrap(), InstructionType::JumpIfZero);
        assert_eq!(InstructionType::from_str("]").unwrap(), InstructionType::JumpIfNotZero);
    }

    // Test invalid input for FromStr
    #[test]
    fn test_instruction_type_from_str_invalid() {
        assert!(InstructionType::from_str("x").is_err());
        assert!(InstructionType::from_str("").is_err());
        assert!(InstructionType::from_str("++").is_err());
    }

    // Test Display implementation
    #[test]
    fn test_instruction_type_display() {
        assert_eq!(format!("{}", InstructionType::Right), ">");
        assert_eq!(format!("{}", InstructionType::Left), "<");
        assert_eq!(format!("{}", InstructionType::Plus), "+");
        assert_eq!(format!("{}", InstructionType::Minus), "-");
        assert_eq!(format!("{}", InstructionType::PutChar), ".");
        assert_eq!(format!("{}", InstructionType::ReadChar), ",");
        assert_eq!(format!("{}", InstructionType::JumpIfZero), "[");
        assert_eq!(format!("{}", InstructionType::JumpIfNotZero), "]");
    }

    // Test from_u8 implementation
    #[test]
    fn test_instruction_type_from_u8() {
        assert_eq!(InstructionType::try_from(b'>').unwrap(), InstructionType::Right);
        assert_eq!(InstructionType::try_from(b'<').unwrap(), InstructionType::Left);
        assert_eq!(InstructionType::try_from(b'+').unwrap(), InstructionType::Plus);
        assert_eq!(InstructionType::try_from(b'-').unwrap(), InstructionType::Minus);
        assert_eq!(InstructionType::try_from(b'.').unwrap(), InstructionType::PutChar);
        assert_eq!(InstructionType::try_from(b',').unwrap(), InstructionType::ReadChar);
        assert_eq!(InstructionType::try_from(b'[').unwrap(), InstructionType::JumpIfZero);
        assert_eq!(InstructionType::try_from(b']').unwrap(), InstructionType::JumpIfNotZero);
    }

    // Test to ensure invalid input as u8 returns an error
    #[test]
    fn test_instruction_type_from_u8_invalid() {
        let result = InstructionType::try_from(b'x');
        assert_eq!(result, Err(InstructionError::Conversion('x')));
    }

    // Test Instruction struct creation
    #[test]
    fn test_instruction_creation() {
        let instruction = Instruction { ins_type: InstructionType::Right, argument: 42 };

        assert_eq!(instruction.ins_type, InstructionType::Right);
        assert_eq!(instruction.argument, 42);
    }
}
