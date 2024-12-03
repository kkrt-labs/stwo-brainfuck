use super::table::MemoryElements;
use crate::components::MemoryClaim;
use num_traits::One;
use stwo_prover::{
    constraint_framework::{
        preprocessed_columns::PreprocessedColumn, EvalAtRow, FrameworkComponent, FrameworkEval,
        RelationEntry,
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
        let clk = eval.next_trace_mask();
        let mp = eval.next_trace_mask();
        let mv = eval.next_trace_mask();
        let d = eval.next_trace_mask();
        let next_clk = eval.next_trace_mask();
        let next_mp = eval.next_trace_mask();
        let next_mv = eval.next_trace_mask();
        let next_d = eval.next_trace_mask();

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
            (next_mp.clone() - mp.clone() - BaseField::one().into()) *
                (next_clk.clone() - clk.clone() - BaseField::one().into()),
        );

        // If `mp` increases by 1, then `next_mv` must be 0
        eval.add_constraint((next_mp.clone() - mp.clone()) * next_mv.clone());

        // The next dummy is either 0 or 1
        eval.add_constraint(next_d.clone() * (next_d.clone() - BaseField::one().into()));

        // If `d` is set, then `mp` remains the same
        eval.add_constraint(d.clone() * (next_mp.clone() - mp.clone()));

        // If `d` is set, then `mv` remains the same
        eval.add_constraint(d.clone() * (next_mv.clone() - mv.clone()));

        // LogUp of `clk`, `mp` and `mv`
        let multiplicity_row = E::EF::from(d) - E::EF::one();
        // LogUp of `next_clk`, `next_mp` and `next_mv`
        let multiplicity_next_row = E::EF::from(next_d) - E::EF::one();
        eval.add_to_relation(&[
            RelationEntry::new(&self.memory_lookup_elements, multiplicity_row, &[clk, mp, mv]),
            RelationEntry::new(
                &self.memory_lookup_elements,
                multiplicity_next_row,
                &[next_clk, next_mp, next_mv],
            ),
        ]);

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
    /// to bound the proof to the trace.
    pub fn mix_into(&self, channel: &mut impl Channel) {
        channel.mix_felts(&[self.claimed_sum]);
    }
}

#[cfg(test)]
mod tests {
    use crate::components::memory::{
        component::MemoryEval,
        table::{interaction_trace_evaluation, MemoryElements, MemoryTable},
    };
    use brainfuck_vm::{compiler::Compiler, test_helper::create_test_machine};
    use stwo_prover::{
        constraint_framework::{
            assert_constraints, preprocessed_columns::gen_is_first, FrameworkEval,
        },
        core::{
            pcs::TreeVec,
            poly::circle::{CanonicCoset, CircleEvaluation},
        },
    };

    #[test]
    fn test_memory_constraints() {
        const LOG_SIZE: u32 = 9;

        // Get an execution trace from a valid Brainfuck program
        let code = "+>,<[>+.<-]";
        let mut compiler = Compiler::new(code);
        let instructions = compiler.compile();
        let (mut machine, _) = create_test_machine(&instructions, &[1]);
        let () = machine.execute().expect("Failed to execute machine");

        let trace_vm = machine.trace();

        // Construct the IsFirst preprocessed column
        let is_first_col = gen_is_first(LOG_SIZE);
        let is_first_col_2 = gen_is_first(LOG_SIZE);
        let preprocessed_trace = vec![is_first_col, is_first_col_2];

        // Construct the main trace from the execution trace
        let table = MemoryTable::from(trace_vm);
        let (main_trace, claim) = table.trace_evaluation().unwrap();

        // Draw Interaction elements
        let memory_lookup_elements = MemoryElements::dummy();

        // Generate interaction trace
        let (interaction_trace, interaction_claim) =
            interaction_trace_evaluation(&main_trace, &memory_lookup_elements).unwrap();

        // Create the trace evaluation TreeVec
        let trace = TreeVec::new(vec![preprocessed_trace, main_trace, interaction_trace]);

        // Interpolate the trace for the evaluation
        let trace_polys = trace.map_cols(CircleEvaluation::interpolate);

        // Get the Memory AIR evaluator
        let memory_eval = MemoryEval::new(&claim, memory_lookup_elements);

        // Assert that the constraints are valid for a valid Brainfuck program.
        assert_constraints(
            &trace_polys,
            CanonicCoset::new(LOG_SIZE),
            |eval| {
                memory_eval.evaluate(eval);
            },
            (interaction_claim.claimed_sum, None),
        );
    }
}
