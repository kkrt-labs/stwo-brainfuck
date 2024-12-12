use brainfuck_vm::instruction::InstructionType;
use stwo_prover::{
    constraint_framework::{EvalAtRow, FrameworkComponent, FrameworkEval},
    core::{channel::Channel, fields::qm31::SecureField},
};

use crate::components::IoClaim;

use super::table::IoElements;

/// Implementation of `Component` and `ComponentProver`
/// for the `SimdBackend` from the constraint framework provided by Stwo
pub type InputComponent = FrameworkComponent<IoEval<{ InstructionType::ReadChar.to_u32() }>>;

/// Implementation of `Component` and `ComponentProver`
/// for the `SimdBackend` from the constraint framework provided by Stwo
pub type OutputComponent = FrameworkComponent<IoEval<{ InstructionType::PutChar.to_u32() }>>;

/// The AIR for the I/O components.
///
/// Constraints are defined through the `FrameworkEval`
/// provided by the constraint framework of Stwo.
pub struct IoEval<const N: u32> {
    log_size: u32,
    _io_lookup_elements: IoElements,
}

impl<const N: u32> IoEval<N> {
    pub const fn new(claim: &IoClaim, io_lookup_elements: IoElements) -> Self {
        Self { log_size: claim.log_size, _io_lookup_elements: io_lookup_elements }
    }
}

impl<const N: u32> FrameworkEval for IoEval<N> {
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

    /// Defines the AIR for the I/O components
    ///
    /// Both the Input and Output component have the same constraints.
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

/// The claim of the interaction phase 2 (with the logUp protocol).
///
/// The total sum is the computed sum of the logUp extension column,
/// including the padded rows.
/// It allows proving that the I/O main trace is a sublist
/// of the Processor trace (which is the execution trace provided by the `brainfuck_vm`):
/// all input and output values are the same as the one from the execution, in the same order.
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
