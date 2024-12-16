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
    /// Registers values from the current row are obtained through masks.
    /// When you apply a mask, you target the current column and then pass to the next
    /// one: the register order matters to correctly fetch them.
    ///
    /// - Use `eval.next_trace_mask()` to get the current register from the main trace
    ///   (`ORIGINAL_TRACE_IDX`)
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
        // Note: `mp` increases by 0 or 1, if `mp` increases, then the
        // constraints on `clk` increasing should be void, hence the
        // (`next_mp` - `mp` - 1)
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
    use brainfuck_vm::{
        compiler::Compiler, registers::Registers, test_helper::create_test_machine,
    };
    use num_traits::One;
    use stwo_prover::{
        constraint_framework::{
            assert_constraints, preprocessed_columns::gen_is_first, FrameworkEval,
        },
        core::{
            channel::Blake2sChannel,
            fields::m31::BaseField,
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
        let table = MemoryTable::from(&trace_vm);
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

    #[test]
    #[should_panic = "assertion `left == right` failed: row: 0
  left: (1 + 0i) + (0 + 0i)u
 right: (0 + 0i) + (0 + 0i)u"]
    fn test_invalid_boundary_clk() {
        const LOG_SIZE: u32 = 4;

        let is_first_col = gen_is_first(LOG_SIZE);
        let preprocessed_trace_eval = vec![is_first_col];

        let registers = vec![Registers { clk: BaseField::one(), ..Default::default() }];
        let memory_table = MemoryTable::from(&registers);
        let (main_trace_eval, claim) = memory_table.trace_evaluation().unwrap();

        // Required to use `MemoryElements::draw(channel: &mut impl Channel)`
        // because `MemoryElements::dummy()` returns a denominator of 0
        // for a `MemoryTableEntry {1, 0, 0, 0}`
        let channel = &mut Blake2sChannel::default();
        let memory_lookup_elements = MemoryElements::draw(channel);

        let (interaction_trace_eval, interaction_claim) =
            interaction_trace_evaluation(&main_trace_eval, &memory_lookup_elements).unwrap();

        let trace =
            TreeVec::new(vec![preprocessed_trace_eval, main_trace_eval, interaction_trace_eval]);

        let trace_polys = trace.map_cols(CircleEvaluation::interpolate);

        let memory_eval = MemoryEval::new(&claim, memory_lookup_elements);

        assert_constraints(
            &trace_polys,
            CanonicCoset::new(LOG_SIZE),
            |eval| {
                memory_eval.evaluate(eval);
            },
            (interaction_claim.claimed_sum, None),
        );
    }

    #[test]
    #[should_panic = "assertion `left == right` failed: row: 0
  left: (1 + 0i) + (0 + 0i)u
 right: (0 + 0i) + (0 + 0i)u"]
    fn test_invalid_boundary_mp() {
        const LOG_SIZE: u32 = 4;

        let is_first_col = gen_is_first(LOG_SIZE);
        let preprocessed_trace_eval = vec![is_first_col];

        let registers = vec![Registers { mp: BaseField::one(), ..Default::default() }];
        let memory_table = MemoryTable::from(&registers);
        let (main_trace_eval, claim) = memory_table.trace_evaluation().unwrap();

        let channel = &mut Blake2sChannel::default();
        let memory_lookup_elements = MemoryElements::draw(channel);

        let (interaction_trace_eval, interaction_claim) =
            interaction_trace_evaluation(&main_trace_eval, &memory_lookup_elements).unwrap();

        let trace =
            TreeVec::new(vec![preprocessed_trace_eval, main_trace_eval, interaction_trace_eval]);

        let trace_polys = trace.map_cols(CircleEvaluation::interpolate);

        let memory_eval = MemoryEval::new(&claim, memory_lookup_elements);

        assert_constraints(
            &trace_polys,
            CanonicCoset::new(LOG_SIZE),
            |eval| {
                memory_eval.evaluate(eval);
            },
            (interaction_claim.claimed_sum, None),
        );
    }

    #[test]
    #[should_panic = "assertion `left == right` failed: row: 0
  left: (1 + 0i) + (0 + 0i)u
 right: (0 + 0i) + (0 + 0i)u"]
    fn test_invalid_boundary_mv() {
        const LOG_SIZE: u32 = 4;

        let is_first_col = gen_is_first(LOG_SIZE);
        let preprocessed_trace_eval = vec![is_first_col];

        let registers = vec![Registers { mv: BaseField::one(), ..Default::default() }];
        let memory_table = MemoryTable::from(&registers);
        let (main_trace_eval, claim) = memory_table.trace_evaluation().unwrap();

        let channel = &mut Blake2sChannel::default();
        let memory_lookup_elements = MemoryElements::draw(channel);

        let (interaction_trace_eval, interaction_claim) =
            interaction_trace_evaluation(&main_trace_eval, &memory_lookup_elements).unwrap();

        let trace =
            TreeVec::new(vec![preprocessed_trace_eval, main_trace_eval, interaction_trace_eval]);

        let trace_polys = trace.map_cols(CircleEvaluation::interpolate);

        let memory_eval = MemoryEval::new(&claim, memory_lookup_elements);

        assert_constraints(
            &trace_polys,
            CanonicCoset::new(LOG_SIZE),
            |eval| {
                memory_eval.evaluate(eval);
            },
            (interaction_claim.claimed_sum, None),
        );
    }

    #[test]
    #[should_panic = "assertion `left == right` failed: row: 0
  left: (1 + 0i) + (0 + 0i)u
 right: (0 + 0i) + (0 + 0i)u"]
    fn test_invalid_boundary_d() {
        const LOG_SIZE: u32 = 4;

        let is_first_col = gen_is_first(LOG_SIZE);
        let preprocessed_trace_eval = vec![is_first_col];

        let registers = vec![Default::default()];
        let mut memory_table = MemoryTable::from(&registers);
        // We must manually modify the value of d as rows from `Vec<Registers>` are assumed real.
        memory_table.table[0].d = BaseField::one();
        let (main_trace_eval, claim) = memory_table.trace_evaluation().unwrap();

        let channel = &mut Blake2sChannel::default();
        let memory_lookup_elements = MemoryElements::draw(channel);

        let (interaction_trace_eval, interaction_claim) =
            interaction_trace_evaluation(&main_trace_eval, &memory_lookup_elements).unwrap();

        let trace =
            TreeVec::new(vec![preprocessed_trace_eval, main_trace_eval, interaction_trace_eval]);

        let trace_polys = trace.map_cols(CircleEvaluation::interpolate);

        let memory_eval = MemoryEval::new(&claim, memory_lookup_elements);

        assert_constraints(
            &trace_polys,
            CanonicCoset::new(LOG_SIZE),
            |eval| {
                memory_eval.evaluate(eval);
            },
            (interaction_claim.claimed_sum, None),
        );
    }

    #[test]
    #[should_panic = "assertion `left == right` failed: row: 0
  left: (2 + 0i) + (0 + 0i)u
 right: (0 + 0i) + (0 + 0i)u"]
    fn test_invalid_transition_mp_increase() {
        const LOG_SIZE: u32 = 5;

        let is_first_col = gen_is_first(LOG_SIZE);
        let preprocessed_trace_eval = vec![is_first_col];

        // `mp` should increase by 0 or 1, here it increases by 2.
        let registers =
            vec![Default::default(), Registers { mp: BaseField::from(2), ..Default::default() }];
        let memory_table = MemoryTable::from(&registers);
        let (main_trace_eval, claim) = memory_table.trace_evaluation().unwrap();

        let memory_lookup_elements = MemoryElements::dummy();

        let (interaction_trace_eval, interaction_claim) =
            interaction_trace_evaluation(&main_trace_eval, &memory_lookup_elements).unwrap();

        let trace =
            TreeVec::new(vec![preprocessed_trace_eval, main_trace_eval, interaction_trace_eval]);

        let trace_polys = trace.map_cols(CircleEvaluation::interpolate);

        let memory_eval = MemoryEval::new(&claim, memory_lookup_elements);

        assert_constraints(
            &trace_polys,
            CanonicCoset::new(LOG_SIZE),
            |eval| {
                memory_eval.evaluate(eval);
            },
            (interaction_claim.claimed_sum, None),
        );
    }

    #[test]
    #[should_panic = "assertion `left == right` failed: row: 0
  left: (1 + 0i) + (0 + 0i)u
 right: (0 + 0i) + (0 + 0i)u"]
    fn test_invalid_transition_clk_increase() {
        const LOG_SIZE: u32 = 5;

        let is_first_col = gen_is_first(LOG_SIZE);
        let preprocessed_trace_eval = vec![is_first_col];

        // `mp` remains the same, but `clk` is not increased by 1.
        let registers = vec![Default::default(), Default::default()];
        let memory_table = MemoryTable::from(&registers);
        let (main_trace_eval, claim) = memory_table.trace_evaluation().unwrap();

        let channel = &mut Blake2sChannel::default();
        let memory_lookup_elements = MemoryElements::draw(channel);

        let (interaction_trace_eval, interaction_claim) =
            interaction_trace_evaluation(&main_trace_eval, &memory_lookup_elements).unwrap();

        let trace =
            TreeVec::new(vec![preprocessed_trace_eval, main_trace_eval, interaction_trace_eval]);

        let trace_polys = trace.map_cols(CircleEvaluation::interpolate);

        let memory_eval = MemoryEval::new(&claim, memory_lookup_elements);

        assert_constraints(
            &trace_polys,
            CanonicCoset::new(LOG_SIZE),
            |eval| {
                memory_eval.evaluate(eval);
            },
            (interaction_claim.claimed_sum, None),
        );
    }

    #[test]
    #[should_panic = "assertion `left == right` failed: row: 0
  left: (1 + 0i) + (0 + 0i)u
 right: (0 + 0i) + (0 + 0i)u"]
    fn test_invalid_transition_mp_increase_next_mv() {
        const LOG_SIZE: u32 = 5;

        let is_first_col = gen_is_first(LOG_SIZE);
        let preprocessed_trace_eval = vec![is_first_col];

        // `mp` increases by 1, but `next_mv` is not 0.
        let registers = vec![
            Default::default(),
            Registers { mp: BaseField::one(), mv: BaseField::one(), ..Default::default() },
        ];
        let memory_table = MemoryTable::from(&registers);
        let (main_trace_eval, claim) = memory_table.trace_evaluation().unwrap();

        let channel = &mut Blake2sChannel::default();
        let memory_lookup_elements = MemoryElements::draw(channel);

        let (interaction_trace_eval, interaction_claim) =
            interaction_trace_evaluation(&main_trace_eval, &memory_lookup_elements).unwrap();

        let trace =
            TreeVec::new(vec![preprocessed_trace_eval, main_trace_eval, interaction_trace_eval]);

        let trace_polys = trace.map_cols(CircleEvaluation::interpolate);

        let memory_eval = MemoryEval::new(&claim, memory_lookup_elements);

        assert_constraints(
            &trace_polys,
            CanonicCoset::new(LOG_SIZE),
            |eval| {
                memory_eval.evaluate(eval);
            },
            (interaction_claim.claimed_sum, None),
        );
    }

    #[test]
    #[should_panic = "assertion `left == right` failed: row: 0
  left: (2 + 0i) + (0 + 0i)u
 right: (0 + 0i) + (0 + 0i)u"]
    fn test_invalid_transition_next_dummy() {
        const LOG_SIZE: u32 = 5;

        let is_first_col = gen_is_first(LOG_SIZE);
        let preprocessed_trace_eval = vec![is_first_col];

        // The next dummy register flag `next_d` is set to 2.
        let registers =
            vec![Default::default(), Registers { mp: BaseField::one(), ..Default::default() }];
        let mut memory_table = MemoryTable::from(&registers);
        memory_table.table[0].next_d = BaseField::from(2);
        let (main_trace_eval, claim) = memory_table.trace_evaluation().unwrap();

        let channel = &mut Blake2sChannel::default();
        let memory_lookup_elements = MemoryElements::draw(channel);

        let (interaction_trace_eval, interaction_claim) =
            interaction_trace_evaluation(&main_trace_eval, &memory_lookup_elements).unwrap();

        let trace =
            TreeVec::new(vec![preprocessed_trace_eval, main_trace_eval, interaction_trace_eval]);

        let trace_polys = trace.map_cols(CircleEvaluation::interpolate);

        let memory_eval = MemoryEval::new(&claim, memory_lookup_elements);

        assert_constraints(
            &trace_polys,
            CanonicCoset::new(LOG_SIZE),
            |eval| {
                memory_eval.evaluate(eval);
            },
            (interaction_claim.claimed_sum, None),
        );
    }

    #[test]
    #[should_panic = "assertion `left == right` failed: row: 1
  left: (1 + 0i) + (0 + 0i)u
 right: (0 + 0i) + (0 + 0i)u"]
    fn test_invalid_transition_d_mp() {
        const LOG_SIZE: u32 = 5;

        let is_first_col = gen_is_first(LOG_SIZE);
        let is_first_col_2 = gen_is_first(LOG_SIZE);
        let preprocessed_trace_eval = vec![is_first_col, is_first_col_2];

        // We create a table with 2 real entries
        // The second row will be padded,
        // We set first entry of the second row as a dummy one (`d` = 1)
        // And we modify the second entry of the second row to have `next_mp` different from `mp`
        let registers =
            vec![Default::default(), Registers { mp: BaseField::one(), ..Default::default() }];
        let mut memory_table = MemoryTable::from(&registers);
        memory_table.table[1].d = BaseField::one();
        memory_table.table[1].next_mp = BaseField::from(2);
        let (main_trace_eval, claim) = memory_table.trace_evaluation().unwrap();

        let channel = &mut Blake2sChannel::default();
        let memory_lookup_elements = MemoryElements::draw(channel);

        let (interaction_trace_eval, interaction_claim) =
            interaction_trace_evaluation(&main_trace_eval, &memory_lookup_elements).unwrap();

        let trace =
            TreeVec::new(vec![preprocessed_trace_eval, main_trace_eval, interaction_trace_eval]);

        let trace_polys = trace.map_cols(CircleEvaluation::interpolate);

        let memory_eval = MemoryEval::new(&claim, memory_lookup_elements);

        assert_constraints(
            &trace_polys,
            CanonicCoset::new(LOG_SIZE),
            |eval| {
                memory_eval.evaluate(eval);
            },
            (interaction_claim.claimed_sum, None),
        );
    }

    #[test]
    #[should_panic = "assertion `left == right` failed: row: 1
  left: (1 + 0i) + (0 + 0i)u
 right: (0 + 0i) + (0 + 0i)u"]
    fn test_invalid_transition_d_mv() {
        const LOG_SIZE: u32 = 5;

        let is_first_col = gen_is_first(LOG_SIZE);
        let is_first_col_2 = gen_is_first(LOG_SIZE);
        let preprocessed_trace_eval = vec![is_first_col, is_first_col_2];

        // We create a table with 2 real entries
        // The second row will be padded,
        // We set first entry of the second row as a dummy one (`d` = 1)
        // And we modify the second entry of the second row to have `next_mv` different from `mv`
        let registers =
            vec![Default::default(), Registers { mp: BaseField::one(), ..Default::default() }];
        let mut memory_table = MemoryTable::from(&registers);
        memory_table.table[1].d = BaseField::one();
        memory_table.table[1].next_mv = BaseField::one();
        let (main_trace_eval, claim) = memory_table.trace_evaluation().unwrap();

        let channel = &mut Blake2sChannel::default();
        let memory_lookup_elements = MemoryElements::draw(channel);

        let (interaction_trace_eval, interaction_claim) =
            interaction_trace_evaluation(&main_trace_eval, &memory_lookup_elements).unwrap();

        let trace =
            TreeVec::new(vec![preprocessed_trace_eval, main_trace_eval, interaction_trace_eval]);

        let trace_polys = trace.map_cols(CircleEvaluation::interpolate);

        let memory_eval = MemoryEval::new(&claim, memory_lookup_elements);

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
