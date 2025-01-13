use super::table::InstructionElements;
use crate::components::InstructionClaim;
use num_traits::One;
use stwo_prover::{
    constraint_framework::{
        preprocessed_columns::PreprocessedColumn, EvalAtRow, FrameworkComponent, FrameworkEval,
        RelationEntry,
    },
    core::fields::m31::BaseField,
};

/// Implementation of `Component` and `ComponentProver` for the Instruction component.
/// It targets the `SimdBackend` from the Stwo constraint framework, with a fallback
/// on `CpuBakend` for small traces.
pub type InstructionComponent = FrameworkComponent<InstructionEval>;

/// The AIR for the [`InstructionComponent`].
///
/// Constraints are defined through the [`FrameworkEval`]
/// provided by the constraint framework of Stwo.
pub struct InstructionEval {
    /// The log size of the component's main trace height.
    log_size: u32,
    /// The random elements used for the lookup protocol linking the instruction and
    /// program components to the processor one.
    instruction_lookup_elements: InstructionElements,
}

impl InstructionEval {
    pub const fn new(
        claim: &InstructionClaim,
        instruction_lookup_elements: InstructionElements,
    ) -> Self {
        Self { log_size: claim.log_size, instruction_lookup_elements }
    }
}

impl FrameworkEval for InstructionEval {
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

    /// Defines the AIR for the Instruction component.
    ///
    /// Registers' values from the current row are obtained through masks.
    /// When you apply a mask, you target the current column and then pass to the next
    /// one: the register order matters to correctly fetch them, and all registers must be fetched.
    ///
    /// - Use `eval.next_trace_mask()` to get the current register from the main trace
    ///   (`ORIGINAL_TRACE_IDX`)
    ///
    /// Use `eval.add_constraint` to define a local constraint (boundary, consistency, transition).
    /// Use `eval.add_to_relation` to define a global constraint for the logUp protocol.
    ///
    /// The logUp must be finalized with `eval.finalize_logup()`.
    #[allow(clippy::similar_names)]
    fn evaluate<E: EvalAtRow>(&self, mut eval: E) -> E {
        // Get the preprocessed column to check boundary constraints
        let is_first = eval.get_preprocessed_column(PreprocessedColumn::IsFirst(self.log_size()));

        // Get all the registers' columns
        let ip = eval.next_trace_mask();
        let ci = eval.next_trace_mask();
        let ni = eval.next_trace_mask();
        let d = eval.next_trace_mask();
        let next_ip = eval.next_trace_mask();
        let next_ci = eval.next_trace_mask();
        let next_ni = eval.next_trace_mask();
        let next_d = eval.next_trace_mask();

        // ┌──────────────────────────┐
        // │   Boundary Constraints   │
        // └──────────────────────────┘

        // The first `ip` value equals 0.
        eval.add_constraint(is_first * ip.clone());

        // ┌─────────────────────────────┐
        // │   Consistency Constraints   │
        // └─────────────────────────────┘

        // `d` is either 0 or 1.
        eval.add_constraint(d.clone() * (d.clone() - BaseField::one().into()));

        // `next_d` is either 0 or 1.
        eval.add_constraint(next_d.clone() * (next_d.clone() - BaseField::one().into()));

        // If `d` is set, then `ci` equals 0.
        eval.add_constraint(d.clone() * ci.clone());

        // If `d` is set, then `ni` equals 0.
        eval.add_constraint(d.clone() * ni.clone());

        // If `next_d` is set, then `next_ci` equals 0.
        eval.add_constraint(next_d.clone() * next_ci.clone());

        // If `next_d` is set, then `ni` equals 0.
        eval.add_constraint(next_d * next_ni.clone());

        // ┌────────────────────────────┐
        // │   Transition Constraints   │
        // └────────────────────────────┘

        // `ip` increases by 0 or 1
        eval.add_constraint(
            (next_ip.clone() - ip.clone()) *
                (next_ip.clone() - ip.clone() - BaseField::one().into()),
        );

        // If `ip` remains the same, then `ci` remains the same
        eval.add_constraint(
            (next_ip.clone() - ip.clone() - BaseField::one().into()) * (next_ci - ci.clone()),
        );

        // If `ip` remains the same, then `ni` remains the same
        eval.add_constraint(
            (next_ip - ip.clone() - BaseField::one().into()) * (next_ni - ni.clone()),
        );

        // ┌─────────────────────────────┐
        // │   Interaction Constraints   │
        // └─────────────────────────────┘

        let num = d - E::F::one();
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

    use crate::components::instruction::{
        component::InstructionEval,
        table::{interaction_trace_evaluation, InstructionElements, InstructionTable},
    };

    #[test]
    fn test_instruction_constraints() {
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
        let table = InstructionTable::from((&trace_vm, machine.program()));
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
        let instruction_eval = InstructionEval::new(&claim, instruction_lookup_elements);

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
