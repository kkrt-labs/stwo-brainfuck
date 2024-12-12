use super::table::InstructionElements;
use crate::components::InstructionClaim;
use stwo_prover::{
    constraint_framework::{EvalAtRow, FrameworkComponent, FrameworkEval},
    core::{channel::Channel, fields::qm31::SecureField},
};

/// Implementation of `Component` and `ComponentProver`
/// for the `SimdBackend` from the constraint framework provided by Stwo
pub type InstructionComponent = FrameworkComponent<InstructionEval>;

/// The AIR for the Instruction component.
///
/// Constraints are defined through the `FrameworkEval`
/// provided by the constraint framework of Stwo.
pub struct InstructionEval {
    log_size: u32,
    _instruction_lookup_elements: InstructionElements,
}

impl InstructionEval {
    pub const fn new(
        claim: &InstructionClaim,
        instruction_lookup_elements: InstructionElements,
    ) -> Self {
        Self { log_size: claim.log_size, _instruction_lookup_elements: instruction_lookup_elements }
    }
}

impl FrameworkEval for InstructionEval {
    /// Returns the log size from the main claim.
    fn log_size(&self) -> u32 {
        self.log_size
    }

    /// The degree of the constraints is bounded by the size of the trace.
    ///
    /// Returns the ilog2 (upper) bound of the constraint degree for the component.
    fn max_constraint_log_degree_bound(&self) -> u32 {
        self.log_size + 1
    }

    /// Defines the AIR for the Instruction component
    ///
    /// Registers values from the current row are obtained through masks.
    /// When you apply a mask, you target the current column and then pass to the next
    /// one: the register order matters to correctly fetch them.
    ///
    /// - Use `eval.next_trace_mask()` to get the current register from the main trace
    ///   (`ORIGINAL_TRACE_IDX`)
    ///
    /// Use `eval.add_constraint` to define a local constraint (boundary, transition).
    /// Use `eval.add_to_relation` to define a global constraint for the logUp protocol.
    ///
    /// The logUp must be finalized with `eval.finalize_logup()`.
    #[allow(clippy::similar_names)]
    fn evaluate<E: EvalAtRow>(&self, _eval: E) -> E {
        todo!()
    }
}

// TODO: Eventually refactor all InteractionClaim into a common struct at the components mod root.
/// The claim of the interaction phase 2 (with the logUp protocol).
///
/// The total sum is the computed sum of the logUp extension column,
/// including the padded rows.
/// It allows proving two things on two disjoint subset of the Instruction main trace (whose union
/// constitutes the Instruction):
/// - One is the permutation of the Processor trace
/// - The other is a subset of the Program trace (order preserved).
/// of the Processor trace (which is the execution trace provided by the `brainfuck_vm`).
#[derive(Debug, Eq, PartialEq)]
pub struct InteractionClaim {
    /// The computed sum of the logUp extension column, including padded rows.
    pub claimed_sum: SecureField,
}

impl InteractionClaim {
    /// Mix the sums from the logUp protocol into the Fiat-Shamir [`Channel`],
    /// to bound the proof to the trace.
    pub fn mix_into(&self, channel: &mut impl Channel) {
        channel.mix_felts(&[self.claimed_sum]);
    }
}
