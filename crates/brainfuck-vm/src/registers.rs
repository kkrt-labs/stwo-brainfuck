// Adapted from rkdud007 brainfuck-zkvm https://github.com/rkdud007/brainfuck-zkvm/blob/main/src/registers.rs

use num_traits::identities::Zero;
use stwo_prover::core::fields::m31::BaseField;

#[derive(Clone)]
pub struct Registers {
    /// Clock Cycle Counter
    pub clk: BaseField,
    /// Instruction Pointer (i.e. PC)
    pub ip: BaseField,
    /// Current Instruction
    pub ci: BaseField,
    /// Next Instruction
    pub ni: BaseField,
    /// Memory Pointer (i.e. AP)
    pub mp: BaseField,
    /// Memory Value (i.e. [AP])
    pub mv: BaseField,
    /// Memory Value Inverse
    pub mvi: BaseField,
}

impl Default for Registers {
    fn default() -> Self {
        Self::new()
    }
}

impl Registers {
    pub fn new() -> Registers {
        Registers {
            clk: BaseField::zero(),
            ip: BaseField::zero(),
            ci: BaseField::zero(),
            ni: BaseField::zero(),
            mp: BaseField::zero(),
            mv: BaseField::zero(),
            mvi: BaseField::zero(),
        }
    }
}

impl std::fmt::Display for Registers {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(
            f,
            "clk:{}, ip:{}, ci:{}, ni:{}, mp:{}, mv:{}, mvi:{}",
            self.clk, self.ip, self.ci, self.ni, self.mp, self.mv, self.mvi
        )
    }
}

impl std::fmt::Debug for Registers {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(
            f,
            "clk:{}, ip:{}, ci:{}, ni:{}, mp:{}, mv:{}, mvi:{}",
            self.clk, self.ip, self.ci, self.ni, self.mp, self.mv, self.mvi
        )
    }
}
