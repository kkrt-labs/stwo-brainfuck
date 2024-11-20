use stwo_prover::core::{
    backend::simd::SimdBackend,
    fields::m31::BaseField,
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
