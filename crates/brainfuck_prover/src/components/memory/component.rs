use super::table::MemoryColumn;
use stwo_prover::core::{
    channel::Channel,
    fields::{qm31::SecureField, secure_column::SECURE_EXTENSION_DEGREE},
    pcs::TreeVec,
};

/// The claim for the Memory component
#[derive(Debug, Eq, PartialEq)]
pub struct Claim {
    pub log_size: u32,
}

impl Claim {
    /// Returns the `log_size` of the each type of trace commited for the Memory component:
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
        let trace_log_sizes = vec![self.log_size; MemoryColumn::count()];
        let interaction_trace_log_sizes: Vec<u32> = vec![self.log_size; SECURE_EXTENSION_DEGREE];
        TreeVec::new(vec![
            preprocessed_trace_log_sizes,
            trace_log_sizes,
            interaction_trace_log_sizes,
        ])
    }

    /// Mix the log size of the Memory table to the Fiat-Shamir [`Channel`],
    /// to bound the channel randomness and the trace.
    pub fn mix_into(&self, channel: &mut impl Channel) {
        channel.mix_u64(self.log_size.into());
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
    /// to bound the proof to the trace.
    pub fn mix_into(&self, channel: &mut impl Channel) {
        channel.mix_felts(&[self.claimed_sum]);
    }
}
