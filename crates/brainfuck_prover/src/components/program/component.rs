use crate::components::{instruction::table::InstructionElements, ProgramClaim};
use num_traits::One;
use stwo_prover::{
    constraint_framework::{
        preprocessed_columns::PreprocessedColumn, EvalAtRow, FrameworkComponent, FrameworkEval,
        RelationEntry,
    },
    core::fields::m31::BaseField,
};

/// Implementation of `Component` and `ComponentProver` for the [`ProgramComponent`].
/// It targets the `SimdBackend` from the Stwo constraint framework, with a fallback
/// on `CpuBackend` for small traces.
pub type ProgramComponent = FrameworkComponent<ProgramEval>;
/// The AIR for the [`ProgramComponent`].
///
/// Constraints are defined through the [`FrameworkEval`]
/// provided by the constraint framework of Stwo.
pub struct ProgramEval {
    /// The log size of the component's main trace height.
    log_size: u32,
    /// The random elements used for the lookup protocol linking the instruction and
    /// program components to the processor one.
    instruction_lookup_elements: InstructionElements,
}

impl ProgramEval {
    pub const fn new(
        claim: &ProgramClaim,
        instruction_lookup_elements: InstructionElements,
    ) -> Self {
        Self { log_size: claim.log_size, instruction_lookup_elements }
    }
}

impl FrameworkEval for ProgramEval {
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
    /// Defines the AIR for the Program component.
    ///
    /// Registers' values from the current row are obtained through masks.
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
    fn evaluate<E: EvalAtRow>(&self, mut eval: E) -> E {
        // Get the preprocessed column to check boundary constraints
        let is_first = eval.get_preprocessed_column(PreprocessedColumn::IsFirst(self.log_size()));

        // Get all the registers' columns
        let ip = eval.next_trace_mask();
        let ci = eval.next_trace_mask();
        let ni = eval.next_trace_mask();
        let d = eval.next_trace_mask();

        // ┌──────────────────────────┐
        // │   Boundary Constraints   │
        // └──────────────────────────┘

        // `ip` starts at 0.
        eval.add_constraint(is_first * ip.clone());

        // ┌─────────────────────────────┐
        // │   Consistency Constraints   │
        // └─────────────────────────────┘

        // The dummy flag `d` is either 0 or 1.
        eval.add_constraint(d.clone() * (d.clone() - BaseField::one().into()));

        // If `d` is set, then `ci` equals 0
        eval.add_constraint(d.clone() * ci.clone());

        // If `d` is set, then `ni` equals 0
        eval.add_constraint(d.clone() * ni.clone());

        // ┌─────────────────────────────┐
        // │   Interaction Constraints   │
        // └─────────────────────────────┘

        let num = E::F::one() - d;
        eval.add_to_relation(RelationEntry::new(
            &self.instruction_lookup_elements,
            num.into(),
            &[ip, ci, ni],
        ));

        eval.finalize_logup();

        eval
    }
}

#[cfg(test)]
mod tests {
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

    use crate::components::{
        instruction::table::InstructionElements,
        program::{
            component::ProgramEval,
            table::{interaction_trace_evaluation, ProgramTable},
        },
    };

    #[test]
    fn test_program_constraints() {
        const LOG_SIZE: u32 = 8;

        // Get an execution trace from a valid Brainfuck program
        let code = "+>,<[>+.<-]";
        let mut compiler = Compiler::new(code);
        let instructions = compiler.compile();
        let (mut machine, _) = create_test_machine(&instructions, &[1]);
        let () = machine.execute().expect("Failed to execute machine");

        // Construct the IsFirst preprocessed column
        let is_first_col = gen_is_first(LOG_SIZE);
        let is_first_col_2 = gen_is_first(LOG_SIZE);
        let preprocessed_trace = vec![is_first_col, is_first_col_2];

        // Construct the main trace from the execution trace
        let table = ProgramTable::from(machine.program());
        let (instruction_trace, claim) = table.trace_evaluation().unwrap();

        // Draw Interaction elements
        let instruction_lookup_elements = InstructionElements::dummy();

        // Generate interaction trace
        let (interaction_trace, interaction_claim) =
            interaction_trace_evaluation(&instruction_trace, &instruction_lookup_elements).unwrap();

        // Create the trace evaluation TreeVec
        let trace = TreeVec::new(vec![preprocessed_trace, instruction_trace, interaction_trace]);

        // Interpolate the trace for the evaluation
        let trace_polys = trace.map_cols(CircleEvaluation::interpolate);

        // Get the Instruction AIR evaluator
        let instruction_eval = ProgramEval::new(&claim, instruction_lookup_elements);

        // Assert that the constraints are valid for a valid Brainfuck program.
        assert_constraints(
            &trace_polys,
            CanonicCoset::new(LOG_SIZE),
            |eval| {
                instruction_eval.evaluate(eval);
            },
            (interaction_claim.claimed_sum, None),
        );
    }
}
