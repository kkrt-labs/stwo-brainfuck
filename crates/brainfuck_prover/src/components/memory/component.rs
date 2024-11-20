use super::table::N_COLS_MEMORY_TABLE;
use stwo_prover::core::{channel::Channel, pcs::TreeVec};

/// The claim for the Memory component
#[derive(Debug, Eq, PartialEq)]
pub struct Claim {
    pub log_size: u32,
}

impl Claim {
    /// Returns the log_size of the each type of trace commited for the Memory component:
    /// - Preprocessed trace,
    /// - Main trace,
    /// - Interaction trace.
    ///
    /// The number of columns of each trace is known before actually evaluating them.
    /// The `log_size` is known once the main trace has been evaluated
    /// (the log2 of the size of the [`super::table::MemoryTable`], to which we add LOG_N_LANES for
    /// the SimdBackend)
    ///
    /// Each element of the [`TreeVec`] is dedicated to the commitment of one type of trace.
    /// First element is for the preprocessed trace, second for the main trace and third for the
    /// interaction one.
    ///
    /// NOTE: Currently only the main trace is provided.
    pub fn log_sizes(&self) -> TreeVec<Vec<u32>> {
        // TODO: Add the preprocessed and interaction trace sizes
        let trace_log_sizes = vec![self.log_size; N_COLS_MEMORY_TABLE];
        TreeVec::new(vec![trace_log_sizes])
    }

    /// Mix the log size of the Memory table to the Fiat-Shamir channel,
    /// to bound the channel randomness and the trace.
    pub fn mix_into(&self, channel: &mut impl Channel) {
        channel.mix_u64(u64::from(self.log_size));
    }
}
