use stwo_prover::core::fields::m31::BaseField;

pub const SHIFT_RIGHT_INSTRUCTION: u32 = b'>' as u32;
pub const SHIFT_LEFT_INSTRUCTION: u32 = b'<' as u32;
pub const INCREMENT_INSTRUCTION: u32 = b'+' as u32;
pub const DECREMENT_INSTRUCTION: u32 = b'-' as u32;
pub const INPUT_INSTRUCTION: u32 = b',' as u32;
pub const OUTPUT_INSTRUCTION: u32 = b'.' as u32;
pub const JUMP_IF_ZERO_INSTRUCTION: u32 = b'[' as u32;
pub const JUMP_IF_NON_ZERO_INSTRUCTION: u32 = b']' as u32;

pub const SHIFT_RIGHT_INSTRUCTION_BF: BaseField =
    BaseField::from_u32_unchecked(SHIFT_RIGHT_INSTRUCTION);
pub const SHIFT_LEFT_INSTRUCTION_BF: BaseField =
    BaseField::from_u32_unchecked(SHIFT_LEFT_INSTRUCTION);
pub const INCREMENT_INSTRUCTION_BF: BaseField =
    BaseField::from_u32_unchecked(INCREMENT_INSTRUCTION);
pub const DECREMENT_INSTRUCTION_BF: BaseField =
    BaseField::from_u32_unchecked(DECREMENT_INSTRUCTION);
pub const INPUT_INSTRUCTION_BF: BaseField = BaseField::from_u32_unchecked(INPUT_INSTRUCTION);
pub const OUTPUT_INSTRUCTION_BF: BaseField = BaseField::from_u32_unchecked(OUTPUT_INSTRUCTION);
pub const JUMP_IF_ZERO_INSTRUCTION_BF: BaseField =
    BaseField::from_u32_unchecked(JUMP_IF_ZERO_INSTRUCTION);
pub const JUMP_IF_NON_ZERO_INSTRUCTION_BF: BaseField =
    BaseField::from_u32_unchecked(JUMP_IF_NON_ZERO_INSTRUCTION);

pub const VALID_INSTRUCTIONS: [BaseField; 8] = [
    SHIFT_RIGHT_INSTRUCTION_BF,
    SHIFT_LEFT_INSTRUCTION_BF,
    INCREMENT_INSTRUCTION_BF,
    DECREMENT_INSTRUCTION_BF,
    INPUT_INSTRUCTION_BF,
    OUTPUT_INSTRUCTION_BF,
    JUMP_IF_ZERO_INSTRUCTION_BF,
    JUMP_IF_NON_ZERO_INSTRUCTION_BF,
];
