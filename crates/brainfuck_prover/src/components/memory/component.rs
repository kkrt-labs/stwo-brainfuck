use super::table::MemoryElements;
use crate::components::MemoryClaim;
use stwo_prover::{
    constraint_framework::{EvalAtRow, FrameworkComponent, FrameworkEval},
    core::{channel::Channel, fields::qm31::SecureField},
};

pub type MemoryComponent = FrameworkComponent<MemoryEval>;

#[allow(dead_code)]
pub struct MemoryEval {
    log_size: u32,
    memory_lookup_elements: MemoryElements,
    claimed_sum: SecureField,
}

impl MemoryEval {
    pub const fn new(
        claim: &MemoryClaim,
        memory_lookup_elements: MemoryElements,
        interaction_claim: &InteractionClaim,
    ) -> Self {
        Self {
            log_size: claim.log_size,
            memory_lookup_elements,
            claimed_sum: interaction_claim.claimed_sum,
        }
    }
}

impl FrameworkEval for MemoryEval {
    fn log_size(&self) -> u32 {
        self.log_size
    }

    fn max_constraint_log_degree_bound(&self) -> u32 {
        self.log_size + 1
    }

    fn evaluate<E: EvalAtRow>(&self, mut _eval: E) -> E {
        todo!()
    }
}

/// The claim of the interaction phase 2 (with the logUp protocol).
///
/// The total sum is the computed sum of the logUp extension column,
/// including the padded rows.
/// It allows proving that the Memory main trace is a permutation
/// of the Processor trace (which is the execution trace provided by the `brainfuck_vm`).
#[derive(Debug, Eq, PartialEq)]
pub struct InteractionClaim {
    /// The computed sum of the logUp extension column, including padded rows.
    pub claimed_sum: SecureField,
}

impl InteractionClaim {
    /// Mix the sums from the logUp protocol into the Fiat-Shamir [`Channel`],
    /// to bind the proof to the trace.
    pub fn mix_into(&self, channel: &mut impl Channel) {
        channel.mix_felts(&[self.claimed_sum]);
    }
}
