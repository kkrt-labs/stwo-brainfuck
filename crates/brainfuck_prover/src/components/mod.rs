use instruction::table::InstructionColumn;
use memory::table::MemoryColumn;
use processor::{
    instructions::{
        end_of_execution::table::EndOfExecutionColumn, jump::table::JumpColumn,
        table::ProcessorInstructionColumn,
    },
    table::ProcessorColumn,
};
use program::table::ProgramColumn;
use stwo_prover::core::{
    backend::simd::SimdBackend,
    channel::Channel,
    fields::{m31::BaseField, qm31::SecureField, secure_column::SECURE_EXTENSION_DEGREE},
    pcs::TreeVec,
    poly::{circle::CircleEvaluation, BitReversedOrder},
    ColumnVec,
};
use thiserror::Error;

pub mod instruction;
pub mod memory;
pub mod processor;
pub mod program;

/// Custom error type for the Trace.
#[derive(Debug, Error, Eq, PartialEq)]
pub enum TraceError {
    /// The component trace is empty.
    #[error("The trace is empty.")]
    EmptyTrace,
    /// The trace of the End of Execution component is not equal to one.
    #[error("The end of execution trace is not equal to one.")]
    InvalidEndOfExecution,
}

/// Type for trace evaluation to be used in Stwo.
pub type TraceEval = ColumnVec<CircleEvaluation<SimdBackend, BaseField, BitReversedOrder>>;

/// Claim for the Memory trace.
pub type MemoryClaim = Claim<MemoryColumn>;

/// Claim for the Instruction trace.
pub type InstructionClaim = Claim<InstructionColumn>;

/// Claim for the Processor trace.
pub type ProcessorClaim = Claim<ProcessorColumn>;

/// Claim for the Program trace.
pub type ProgramClaim = Claim<ProgramColumn>;

/// Claim for all the instructions traces (all except jumps and end of execution).
pub type ProcessorInstructionClaim = Claim<ProcessorInstructionColumn>;

/// Claims for the `JumpIfNotZero` and `JumpIfZero` traces.
pub type JumpClaim = Claim<JumpColumn>;

/// Claim for the `EndOfExecution` trace.
pub type EndOfExecutionClaim = Claim<EndOfExecutionColumn>;

/// The claim of the interaction phase 2 (with the logUp protocol).
///
/// The claimed sum is the total sum, which is the computed sum of the logUp extension column,
/// including the padding rows.
/// It allows proving that the main trace of a component is either a permutation, or a sublist of
/// another.
#[derive(Debug, Eq, PartialEq)]
pub struct InteractionClaim {
    /// The computed sum of the logUp extension column, including padding rows (which are actually
    /// set to a multiplicity of 0).
    pub claimed_sum: SecureField,
}

impl InteractionClaim {
    /// Mix the sum from the logUp protocol into the Fiat-Shamir [`Channel`],
    /// to bound the proof to the trace.
    pub fn mix_into(&self, channel: &mut impl Channel) {
        channel.mix_felts(&[self.claimed_sum]);
    }
}

/// Represents a claim associated with a specific trace in the Brainfuck STARK proving system.
#[derive(Debug, Eq, PartialEq)]
pub struct Claim<T: TraceColumn> {
    /// Logarithmic size (`log2`) of the evaluated trace.
    pub log_size: u32,
    /// Marker for the trace type.
    _marker: std::marker::PhantomData<T>,
}

impl<T: TraceColumn> Claim<T> {
    /// Creates a new claim for the given trace type.
    pub const fn new(log_size: u32) -> Self {
        Self { log_size, _marker: std::marker::PhantomData }
    }

    /// Returns the `log_size` for each type of trace committed for the given trace type:
    /// - Preprocessed trace,
    /// - Main trace,
    /// - Interaction trace.
    ///
    /// The number of columns of each trace is known before actually evaluating them.
    /// The `log_size` is known once the main trace has been evaluated
    /// (the log2 of the size of the [`super::table::MemoryTable`], to which we add
    /// [`stwo_prover::core::backend::simd::m31::LOG_N_LANES`]
    /// for the [`stwo_prover::core::backend::simd::SimdBackend`])
    ///
    /// Each element of the [`TreeVec`] is dedicated to the commitment of one type of trace.
    /// First element is for the preprocessed trace, second for the main trace and third for the
    /// interaction one.
    ///
    /// NOTE: Currently only the main trace is provided.
    pub fn log_sizes(&self) -> TreeVec<Vec<u32>> {
        let (main_trace_cols, interaction_trace_cols) = T::count();
        let preprocessed_trace_log_sizes: Vec<u32> = vec![self.log_size];
        let trace_log_sizes = vec![self.log_size; main_trace_cols];
        let interaction_trace_log_sizes: Vec<u32> =
            vec![self.log_size; SECURE_EXTENSION_DEGREE * interaction_trace_cols];
        TreeVec::new(vec![
            preprocessed_trace_log_sizes,
            trace_log_sizes,
            interaction_trace_log_sizes,
        ])
    }

    /// Mix the log size of the table to the Fiat-Shamir [`Channel`],
    /// to bound the channel randomness and the trace.
    pub fn mix_into(&self, channel: &mut impl Channel) {
        channel.mix_u64(self.log_size.into());
    }
}

/// Represents columns of a trace.
pub trait TraceColumn {
    /// Returns the number of columns associated with the specific trace type.
    ///
    /// Main trace columns: first element of the tuple
    /// Interaction trace columns: second element of the tuple
    fn count() -> (usize, usize);
}
