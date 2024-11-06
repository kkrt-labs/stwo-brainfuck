// Taken from rkdud007 brainfuck-zkvm https://github.com/rkdud007/brainfuck-zkvm/blob/main/src/instruction.rs

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

#[cfg(test)]
mod tests {
    use super::*;

    // Test FromStr implementation
    #[test]
    fn test_instruction_type_from_str() {
        // Test valid instruction mappings
        assert_eq!(
            InstructionType::from_str(">").unwrap(),
            InstructionType::Right
        );
        assert_eq!(
            InstructionType::from_str("<").unwrap(),
            InstructionType::Left
        );
        assert_eq!(
            InstructionType::from_str("+").unwrap(),
            InstructionType::Plus
        );
        assert_eq!(
            InstructionType::from_str("-").unwrap(),
            InstructionType::Minus
        );
        assert_eq!(
            InstructionType::from_str(".").unwrap(),
            InstructionType::PutChar
        );
        assert_eq!(
            InstructionType::from_str(",").unwrap(),
            InstructionType::ReadChar
        );
        assert_eq!(
            InstructionType::from_str("[").unwrap(),
            InstructionType::JumpIfZero
        );
        assert_eq!(
            InstructionType::from_str("]").unwrap(),
            InstructionType::JumpIfNotZero
        );
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
        assert_eq!(InstructionType::from_u8(b'>'), InstructionType::Right);
        assert_eq!(InstructionType::from_u8(b'<'), InstructionType::Left);
        assert_eq!(InstructionType::from_u8(b'+'), InstructionType::Plus);
        assert_eq!(InstructionType::from_u8(b'-'), InstructionType::Minus);
        assert_eq!(InstructionType::from_u8(b'.'), InstructionType::PutChar);
        assert_eq!(InstructionType::from_u8(b','), InstructionType::ReadChar);
        assert_eq!(InstructionType::from_u8(b'['), InstructionType::JumpIfZero);
        assert_eq!(
            InstructionType::from_u8(b']'),
            InstructionType::JumpIfNotZero
        );
    }

    // Test from_u8 with invalid input (should panic)
    #[test]
    #[should_panic(expected = "Invalid instruction")]
    fn test_instruction_type_from_u8_invalid() {
        InstructionType::from_u8(b'x');
    }

    // Test Instruction struct creation
    #[test]
    fn test_instruction_creation() {
        let instruction = Instruction {
            ins_type: InstructionType::Right,
            argument: 42,
        };

        assert_eq!(instruction.ins_type, InstructionType::Right);
        assert_eq!(instruction.argument, 42);
    }
}