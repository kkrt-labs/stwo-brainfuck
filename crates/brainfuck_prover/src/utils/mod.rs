use stwo_prover::core::fields::m31::BaseField;

pub const SHIFT_RIGHT_INSTRUCTION: u32 = b'>' as u32;
pub const SHIFT_LEFT_INSTRUCTION: u32 = b'<' as u32;
pub const INCREMENT_INSTRUCTION: u32 = b'+' as u32;
pub const DECREMENT_INSTRUCTION: u32 = b'-' as u32;
pub const INPUT_INSTRUCTION: u32 = b',' as u32;
pub const OUTPUT_INSTRUCTION: u32 = b'.' as u32;
pub const JUMP_IF_ZERO_INSTRUCTION: u32 = b'[' as u32;
pub const JUMP_IF_NON_ZERO_INSTRUCTION: u32 = b']' as u32;

pub const VALID_INSTRUCTIONS: [BaseField; 8] = [
    BaseField::from_u32_unchecked(SHIFT_RIGHT_INSTRUCTION),
    BaseField::from_u32_unchecked(SHIFT_LEFT_INSTRUCTION),
    BaseField::from_u32_unchecked(INCREMENT_INSTRUCTION),
    BaseField::from_u32_unchecked(DECREMENT_INSTRUCTION),
    BaseField::from_u32_unchecked(INPUT_INSTRUCTION),
    BaseField::from_u32_unchecked(OUTPUT_INSTRUCTION),
    BaseField::from_u32_unchecked(JUMP_IF_ZERO_INSTRUCTION),
    BaseField::from_u32_unchecked(JUMP_IF_NON_ZERO_INSTRUCTION),
];
