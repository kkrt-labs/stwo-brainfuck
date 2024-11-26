use instruction::table::InstructionColumn;
use io::table::IoColumn;
use memory::table::MemoryColumn;
use stwo_prover::core::{
    backend::simd::SimdBackend,
    channel::Channel,
    fields::m31::BaseField,
    pcs::TreeVec,
    poly::{circle::CircleEvaluation, BitReversedOrder},
    ColumnVec,
};
use thiserror::Error;

pub mod instruction;
pub mod io;
pub mod memory;
pub mod processor;

/// Type for trace evaluation to be used in Stwo.
pub type TraceEval = ColumnVec<CircleEvaluation<SimdBackend, BaseField, BitReversedOrder>>;

/// Custom error type for the Trace.
#[derive(Debug, Error, Eq, PartialEq)]
pub enum TraceError {
    /// The component trace is empty.
    #[error("The trace is empty.")]
    EmptyTrace,
}

/// Represents the different trace types used in the Brainfuck STARK proving system.
#[derive(Debug, Eq, PartialEq)]
pub enum TraceType {
    /// Memory access trace.
    Memory,
    /// Instruction execution trace.
    Instruction,
    /// Input/output trace.
    Io,
    /// Processor trace (register).
    Processor,
}

impl TraceType {
    /// Returns the number of columns associated with the specific trace type.
    pub fn column_count(&self) -> usize {
        match self {
            Self::Memory => MemoryColumn::count(),
            Self::Instruction => InstructionColumn::count(),
            Self::Io => IoColumn::count(),
            Self::Processor => unimplemented!(),
        }
    }
}

/// Represents a claim associated with a specific trace in the Brainfuck STARK proving system.
#[derive(Debug, Eq, PartialEq)]
pub struct Claim {
    /// Logarithmic size (`log2`) of the evaluated trace.
    pub log_size: u32,
    /// Type of the associated trace.
    pub trace: TraceType,
}

impl Claim {
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
        // TODO: Add the preprocessed and interaction trace correct sizes
        let preprocessed_trace_log_sizes: Vec<u32> = vec![];
        let trace_log_sizes = vec![self.log_size; self.trace.column_count()];
        let interaction_trace_log_sizes: Vec<u32> = vec![];
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
