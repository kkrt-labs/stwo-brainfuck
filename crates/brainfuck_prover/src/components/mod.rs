use instruction::table::InstructionColumn;
use io::table::IoColumn;
use memory::table::MemoryColumn;
use processor::table::ProcessorColumn;
use program::table::ProgramColumn;
use stwo_prover::core::{
    backend::simd::SimdBackend,
    channel::Channel,
    fields::{m31::BaseField, secure_column::SECURE_EXTENSION_DEGREE},
    pcs::TreeVec,
    poly::{circle::CircleEvaluation, BitReversedOrder},
    ColumnVec,
};
use thiserror::Error;

pub mod instruction;
pub mod io;
pub mod memory;
pub mod processor;
pub mod program;

/// Type for trace evaluation to be used in Stwo.
pub type TraceEval = ColumnVec<CircleEvaluation<SimdBackend, BaseField, BitReversedOrder>>;

/// Memory claim for the Trace.
pub type MemoryClaim = Claim<MemoryColumn>;

/// Instruction claim for the Trace.
pub type InstructionClaim = Claim<InstructionColumn>;

/// IO claim for the Trace.
pub type IoClaim = Claim<IoColumn>;

/// Processor claim for the Trace.
pub type ProcessorClaim = Claim<ProcessorColumn>;

/// Program claim for the Trace.
pub type ProgramClaim = Claim<ProgramColumn>;

/// Custom error type for the Trace.
#[derive(Debug, Error, Eq, PartialEq)]
pub enum TraceError {
    /// The component trace is empty.
    #[error("The trace is empty.")]
    EmptyTrace,
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
