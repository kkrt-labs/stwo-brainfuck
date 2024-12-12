use crate::components::{
    instruction::table::InstructionElements, io::table::IoElements, memory::table::MemoryElements,
    ProcessorClaim,
};
use stwo_prover::{
    constraint_framework::{EvalAtRow, FrameworkComponent, FrameworkEval},
    core::{channel::Channel, fields::qm31::SecureField},
};

/// Implementation of `Component` and `ComponentProver`
/// for the `SimdBackend` from the constraint framework provided by Stwo
pub type ProcessorComponent = FrameworkComponent<ProcessorEval>;

/// The AIR for the Processor component.
///
/// Constraints are defined through the `FrameworkEval`
/// provided by the constraint framework of Stwo.
pub struct ProcessorEval {
    log_size: u32,
    _input_lookup_elements: IoElements,
    _output_lookup_elements: IoElements,
    _memory_lookup_elements: MemoryElements,
    _instruction_lookup_elements: InstructionElements,
}

impl ProcessorEval {
    pub const fn new(
        claim: &ProcessorClaim,
        input_lookup_elements: IoElements,
        output_lookup_elements: IoElements,
        memory_lookup_elements: MemoryElements,
        instruction_lookup_elements: InstructionElements,
    ) -> Self {
        Self {
            log_size: claim.log_size,
            _input_lookup_elements: input_lookup_elements,
            _output_lookup_elements: output_lookup_elements,
            _memory_lookup_elements: memory_lookup_elements,
            _instruction_lookup_elements: instruction_lookup_elements,
        }
    }
}

impl FrameworkEval for ProcessorEval {
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

    /// Defines the AIR for the Processor component
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
    fn evaluate<E: EvalAtRow>(&self, _eval: E) -> E {
        todo!()
    }
}

/// The claim of the interaction phase 2 (with the logUp protocol).
///
/// The total sum is the computed sum of the logUp extension column,
/// including the padded rows.
/// It allows proving that the Processor main trace is:
/// - A permutation of the Memory trace.
/// - A permutation of a subset of the Instruction trace.
/// - That the I/O values are the ones in the I/O components, in the same order.
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
