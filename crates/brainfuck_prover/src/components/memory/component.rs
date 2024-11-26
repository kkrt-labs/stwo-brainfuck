use stwo_prover::core::{channel::Channel, fields::qm31::SecureField};

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
