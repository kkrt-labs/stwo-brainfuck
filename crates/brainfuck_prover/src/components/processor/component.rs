use crate::components::{
    instruction::table::InstructionElements, io::table::IoElements, memory::table::MemoryElements,
    ProcessorClaim,
};
use num_traits::One;
use stwo_prover::{
    constraint_framework::{
        preprocessed_columns::PreprocessedColumn, EvalAtRow, FrameworkComponent, FrameworkEval,
        RelationEntry,
    },
    core::{channel::Channel, fields::qm31::SecureField},
};

/// Implementation of `Component` and `ComponentProver`
/// for the `SimdBackend` from the constraint framework provided by Stwo
pub type ProcessorComponent = FrameworkComponent<ProcessorEval>;

/// The AIR for the Processor component.
///
/// Constraints are defined through the `FrameworkEval`
/// provided by the constraint framework of Stwo.
pub struct ProcessorEval {
    log_size: u32,
    input_lookup_elements: IoElements,
    output_lookup_elements: IoElements,
    memory_lookup_elements: MemoryElements,
    instruction_lookup_elements: InstructionElements,
}

impl ProcessorEval {
    pub const fn new(
        claim: &ProcessorClaim,
        input_lookup_elements: IoElements,
        output_lookup_elements: IoElements,
        memory_lookup_elements: MemoryElements,
        instruction_lookup_elements: InstructionElements,
    ) -> Self {
        Self {
            log_size: claim.log_size,
            input_lookup_elements,
            output_lookup_elements,
            memory_lookup_elements,
            instruction_lookup_elements,
        }
    }
}

impl FrameworkEval for ProcessorEval {
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

    /// Defines the AIR for the Processor component
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
    #[allow(clippy::too_many_lines)]
    fn evaluate<E: EvalAtRow>(&self, mut eval: E) -> E {
        // Get the preprocessed column to check boundary constraints
        let is_first = eval.get_preprocessed_column(PreprocessedColumn::IsFirst(self.log_size()));

        // Get all the required registers' values
        let clk = eval.next_trace_mask();
        let ip = eval.next_trace_mask();
        let ci = eval.next_trace_mask();
        let ni = eval.next_trace_mask();
        let mp = eval.next_trace_mask();
        let mv = eval.next_trace_mask();
        let mvi = eval.next_trace_mask();
        let d = eval.next_trace_mask();
        let next_clk = eval.next_trace_mask();
        let _next_ip = eval.next_trace_mask();
        let _next_ci = eval.next_trace_mask();
        let _next_ni = eval.next_trace_mask();
        let next_mp = eval.next_trace_mask();
        let next_mv = eval.next_trace_mask();
        let _next_mvi = eval.next_trace_mask();
        let next_d = eval.next_trace_mask();

        // Boundary constraints
        // `clk` starts at 0
        eval.add_constraint(is_first.clone() * clk.clone());
        // `ip` starts at 0
        eval.add_constraint(is_first.clone() * ip.clone());
        // `mp` starts at 0
        eval.add_constraint(is_first.clone() * mp.clone());
        // `mv` starts at 0
        eval.add_constraint(is_first * mv.clone());

        // Consistency constraints
        // `mv` is the inverse of `mvi`
        eval.add_constraint(mv.clone() * (mv.clone() * mvi.clone() - E::F::one()));
        // `mvi` is the inverse of `mv`
        eval.add_constraint(mvi.clone() * (mv.clone() * mvi - E::F::one()));

        // Transition constraints

        // `clk` increases by 1
        eval.add_constraint(next_clk.clone() - clk.clone() - E::F::one());

        // Lookup arguments

        // Processor & Input
        let multiplicity_row = E::EF::one() - E::EF::from(d);
        let multiplicity_next_row = E::EF::one() - E::EF::from(next_d);
        eval.add_to_relation(&[RelationEntry::new(
            &self.input_lookup_elements,
            multiplicity_row.clone(),
            &[clk.clone(), ci.clone(), mv.clone()],
        )]);

        // Processor & Output
        eval.add_to_relation(&[RelationEntry::new(
            &self.output_lookup_elements,
            multiplicity_row.clone(),
            &[clk.clone(), ci.clone(), mv.clone()],
        )]);

        // Processor & Instruction
        eval.add_to_relation(&[RelationEntry::new(
            &self.instruction_lookup_elements,
            multiplicity_row.clone(),
            &[ip, ci, ni],
        )]);

        // Processor & Memory
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
/// It allows proving that the Processor main trace is:
/// - A permutation of the Memory trace.
/// - A permutation of a subset of the Instruction trace.
/// - That the I/O values are the ones in the I/O components, in the same order.
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
    use crate::components::{
        instruction::table::InstructionElements,
        io::table::IoElements,
        memory::table::MemoryElements,
        processor::{
            component::ProcessorEval,
            table::{interaction_trace_evaluation, ProcessorTable},
        },
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
    fn test_processor_constraints() {
        const LOG_SIZE: u32 = 9;

        // Get an execution trace from a valid Brainfuck program
        let code = "+++>,<[>+.<-]";
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
        let table = ProcessorTable::from(trace_vm);
        let (main_trace, claim) = table.trace_evaluation().unwrap();

        // Draw Interaction elements
        let input_lookup_elements = IoElements::dummy();
        let output_lookup_elements = IoElements::dummy();
        let instruction_lookup_elements = InstructionElements::dummy();
        let memory_lookup_elements = MemoryElements::dummy();

        // Generate interaction trace
        let (interaction_trace, interaction_claim) = interaction_trace_evaluation(
            &main_trace,
            &input_lookup_elements,
            &output_lookup_elements,
            &instruction_lookup_elements,
            &memory_lookup_elements,
        )
        .unwrap();

        // Create the trace evaluation TreeVec
        let trace = TreeVec::new(vec![preprocessed_trace, main_trace, interaction_trace]);

        // Interpolate the trace for the evaluation
        let trace_polys = trace.map_cols(CircleEvaluation::interpolate);

        // Get the Memory AIR evaluator
        let processor_eval = ProcessorEval::new(
            &claim,
            input_lookup_elements,
            output_lookup_elements,
            memory_lookup_elements,
            instruction_lookup_elements,
        );

        // Assert that the constraints are valid for a valid Brainfuck program.
        assert_constraints(
            &trace_polys,
            CanonicCoset::new(LOG_SIZE),
            |eval| {
                processor_eval.evaluate(eval);
            },
            (interaction_claim.claimed_sum, None),
        );
    }
}
