// Adapted from rkdud007 brainfuck-zkvm https://github.com/rkdud007/brainfuck-zkvm/blob/main/src/registers.rs

use num_traits::identities::Zero;
use stwo_prover::core::fields::m31::BaseField;

#[derive(PartialEq, Eq, Clone, Debug)]
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
    pub fn new() -> Self {
        Self {
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

#[cfg(test)]
mod tests {
    use super::*;
    use num_traits::Zero;

    // Test default and new() implementation
    #[test]
    fn test_registers_default_and_new() {
        // Create registers using default() method
        let default_registers = Registers::default();

        // Create registers using new() method
        let new_registers = Registers::new();

        // Check that all fields are zero
        assert!(default_registers.clk.is_zero(), "Clock cycle should be zero");
        assert!(default_registers.ip.is_zero(), "Instruction pointer should be zero");
        assert!(default_registers.ci.is_zero(), "Current instruction should be zero");
        assert!(default_registers.ni.is_zero(), "Next instruction should be zero");
        assert!(default_registers.mp.is_zero(), "Memory pointer should be zero");
        assert!(default_registers.mv.is_zero(), "Memory value should be zero");
        assert!(default_registers.mvi.is_zero(), "Memory value inverse should be zero");

        // Ensure default() and new() produce identical results
        assert_eq!(default_registers.clk, new_registers.clk);
        assert_eq!(default_registers.ip, new_registers.ip);
        assert_eq!(default_registers.ci, new_registers.ci);
        assert_eq!(default_registers.ni, new_registers.ni);
        assert_eq!(default_registers.mp, new_registers.mp);
        assert_eq!(default_registers.mv, new_registers.mv);
        assert_eq!(default_registers.mvi, new_registers.mvi);
    }

    // Test Display implementation
    #[test]
    fn test_registers_display() {
        let registers = Registers {
            clk: BaseField::from(1),
            ip: BaseField::from(2),
            ci: BaseField::from(3),
            ni: BaseField::from(4),
            mp: BaseField::from(5),
            mv: BaseField::from(6),
            mvi: BaseField::from(7),
        };

        let display_string = format!("{registers}");
        assert_eq!(
            display_string, "clk:1, ip:2, ci:3, ni:4, mp:5, mv:6, mvi:7",
            "Display format should match expected output"
        );
    }
}
