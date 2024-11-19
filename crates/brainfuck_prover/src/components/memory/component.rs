use stwo_prover::core::{channel::Channel, pcs::TreeVec};

use super::table::N_COLS_MEMORY_TABLE;

/// The claim for the Memory component
#[derive(Debug, PartialEq)]
pub struct Claim {
    pub log_size: u32,
}
impl Claim {
    pub fn log_sizes(&self) -> TreeVec<Vec<u32>> {
        let trace_log_sizes = vec![self.log_size; N_COLS_MEMORY_TABLE];
        TreeVec::new(vec![trace_log_sizes])
    }

    pub fn mix_into(&self, channel: &mut impl Channel) {
        channel.mix_u64(self.log_size as u64);
    }
}
