use super::table::MemoryElements;
use crate::components::MemoryClaim;
use num_traits::One;
use stwo_prover::{
    constraint_framework::{
        preprocessed_columns::PreprocessedColumn, EvalAtRow, FrameworkComponent, FrameworkEval,
        RelationEntry, ORIGINAL_TRACE_IDX,
    },
    core::{
        channel::Channel,
        fields::{m31::BaseField, qm31::SecureField},
    },
};

/// Implementation of `Component` and `ComponentProver`
/// for the `SimdBackend` from the constraint framework provided by Stwo
pub type MemoryComponent = FrameworkComponent<MemoryEval>;

/// The AIR for the Memory component.
///
/// Constraints are defined through the `FrameworkEval`
/// provided by the constraint framework of Stwo.
pub struct MemoryEval {
    log_size: u32,
    memory_lookup_elements: MemoryElements,
}

impl MemoryEval {
    pub const fn new(claim: &MemoryClaim, memory_lookup_elements: MemoryElements) -> Self {
        Self { log_size: claim.log_size, memory_lookup_elements }
    }
}

impl FrameworkEval for MemoryEval {
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

    /// Defines the AIR for the Memory component
    ///
    /// Registers values from the current row (and potentially neighbors) are obtained through
    /// masks: When you apply a mask, you target the current column and then pass to the next
    /// one: the register order matters to correctly fetch them.
    /// All required registers from a same column must be fetched in one call:
    /// - Use `eval.next_trace_mask()` to get the current register from the main trace
    ///   (`ORIGINAL_TRACE_IDX`)
    /// - Use `eval.next_interaction_mask(interaction: usize, offsets: [isize; N])` to get multiple
    ///   values from one register (e.g. the current one and the next one).
    ///
    /// Use `eval.add_constraint` to define a local constraint (boundary, transition).
    /// Use `eval.add_to_relation` to define a global constraint for the logUp protocol.
    ///
    /// The logUp must be finalized with `eval.finalize_logup()`.
    #[allow(clippy::similar_names)]
    fn evaluate<E: EvalAtRow>(&self, mut eval: E) -> E {
        // Get the preprocessed column to check boundary constraints
        let is_first = eval.get_preprocessed_column(PreprocessedColumn::IsFirst(self.log_size()));

        // Get all the required registers' values
        let [clk, next_clk] = eval.next_interaction_mask(ORIGINAL_TRACE_IDX, [0, 1]);
        let [mp, next_mp] = eval.next_interaction_mask(ORIGINAL_TRACE_IDX, [0, 1]);
        let [mv, next_mv] = eval.next_interaction_mask(ORIGINAL_TRACE_IDX, [0, 1]);
        let [d, next_d] = eval.next_interaction_mask(ORIGINAL_TRACE_IDX, [0, 1]);

        // Boundary constraints
        eval.add_constraint(is_first.clone() * clk.clone());
        eval.add_constraint(is_first.clone() * mp.clone());
        eval.add_constraint(is_first.clone() * mv.clone());
        eval.add_constraint(is_first * d.clone());

        // `mp` increases by 0 or 1
        eval.add_constraint(
            (next_mp.clone() - mp.clone()) *
                (next_mp.clone() - mp.clone() - BaseField::one().into()),
        );

        // If `mp` remains the same, `clk` increases by 1
        eval.add_constraint(
            (next_mp.clone() - mp.clone()) * (next_clk - clk.clone() - BaseField::one().into()),
        );

        // If `mp` increases by 1, then `mv` must be 0
        eval.add_constraint(
            (next_mp.clone() - mp.clone() - BaseField::one().into()) * next_mv.clone(),
        );

        // The next dummy is either 0 or 1
        eval.add_constraint(next_d.clone() * (next_d - BaseField::one().into()));

        // If `d` is set, then `mp` remains the same
        eval.add_constraint(d.clone() * (next_mp - mp.clone()));

        // If `d` is set, then `mv` remains the same
        eval.add_constraint(d * (next_mv - mv.clone()));

        // LogUp of `clk`, `mp` and `mv`
        eval.add_to_relation(&[RelationEntry::new(
            &self.memory_lookup_elements,
            -E::EF::one(),
            &[clk, mp, mv],
        )]);

        eval.finalize_logup();

        eval
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
    /// to bind the proof to the trace.
    pub fn mix_into(&self, channel: &mut impl Channel) {
        channel.mix_felts(&[self.claimed_sum]);
    }
}
