use super::table::MemoryColumn;
use stwo_prover::{
    constraint_framework::logup::ClaimedPrefixSum,
    core::{channel::Channel, fields::qm31::SecureField, pcs::TreeVec},
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
        let interaction_trace_log_sizes: Vec<u32> = vec![];
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

/// The claim of the interaction phase 2 (with the LogUp protocol).
///
/// The total sum is the computed sum of the LogUp extension column,
/// including the padded rows.
/// It allows proving that the Memory main trace is a permutation
/// of the Processor trace (which is the execution trace provided by the brainfuck_vm).
///
/// The [`ClaimedPrefixSum`] is the sum of the 'real' rows (i.e. without the padding rows).
/// The total sum and the claimed sum should be equal.
#[derive(Debug, Eq, PartialEq)]
pub struct InteractionClaim {
    pub total_sum: SecureField,
    pub claimed_sum: Option<ClaimedPrefixSum>,
}
impl InteractionClaim {
    /// Mix the sums from the LogUp protocol into the Fiat-Shamir [`Channel`],
    /// to bound the proof to the trace.
    ///
    /// If the trace has been padded, both the total sum and the claimed
    /// sum are mixed, as well as the index in the extension column
    /// where the claimed_sum is.
    pub fn mix_into(&self, channel: &mut impl Channel) {
        if let Some((claimed_sum, claimed_index)) = self.claimed_sum {
            channel.mix_felts(&[self.total_sum, claimed_sum]);
            channel.mix_u64(claimed_index as u64);
        } else {
            channel.mix_felts(&[self.total_sum]);
        }
    }
}
