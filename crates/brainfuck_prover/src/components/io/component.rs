use brainfuck_vm::instruction::InstructionType;
use num_traits::One;
use stwo_prover::{
    constraint_framework::{EvalAtRow, FrameworkComponent, FrameworkEval, RelationEntry},
    core::{
        channel::Channel,
        fields::{m31::BaseField, qm31::SecureField},
    },
};

use crate::components::IoClaim;

use super::table::IoElements;

/// Implementation of `Component` and `ComponentProver`
/// for the `SimdBackend` from the constraint framework provided by Stwo
pub type InputComponent = FrameworkComponent<InputEval>;

/// The `FrameworkEval` for the Input component
pub type InputEval = IoEval<{ InstructionType::ReadChar.to_u32() }>;

/// Implementation of `Component` and `ComponentProver`
/// for the `SimdBackend` from the constraint framework provided by Stwo
pub type OutputComponent = FrameworkComponent<OutputEval>;

/// The `FrameworkEval` for the Output component
pub type OutputEval = IoEval<{ InstructionType::PutChar.to_u32() }>;

/// The AIR for the I/O components.
///
/// Constraints are defined through the `FrameworkEval`
/// provided by the constraint framework of Stwo.
pub struct IoEval<const N: u32> {
    log_size: u32,
    io_lookup_elements: IoElements,
}

impl<const N: u32> IoEval<N> {
    pub const fn new(claim: &IoClaim, io_lookup_elements: IoElements) -> Self {
        Self { log_size: claim.log_size, io_lookup_elements }
    }
}

impl<const N: u32> FrameworkEval for IoEval<N> {
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

    /// Defines the AIR for the I/O components
    ///
    /// Both the Input and Output component have the same constraints.
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
    fn evaluate<E: EvalAtRow>(&self, mut eval: E) -> E {
        let clk = eval.next_trace_mask();
        let ci = eval.next_trace_mask();
        let mv = eval.next_trace_mask();
        let d = eval.next_trace_mask();

        // `ci` is either 0 (dummy row), or equal to the I/O instruction
        let is_io_instruction =
            ci.clone() - InstructionType::try_from(N).unwrap().to_base_field().into();
        eval.add_constraint(ci.clone() * is_io_instruction);

        // The dummy is either 0 or 1
        eval.add_constraint(d.clone() * (d.clone() - BaseField::one().into()));

        // If d is set, then `mv` equals 0
        eval.add_constraint(d.clone() * mv.clone());

        // If ci is set, then `ci` equals 0
        eval.add_constraint(d.clone() * ci.clone());

        let num = E::EF::from(d) - E::EF::one();

        eval.add_to_relation(&[RelationEntry::new(&self.io_lookup_elements, num, &[clk, ci, mv])]);

        eval.finalize_logup();

        eval
    }
}

/// The claim of the interaction phase 2 (with the logUp protocol).
///
/// The total sum is the computed sum of the logUp extension column,
/// including the padded rows.
/// It allows proving that the I/O main trace is a sublist
/// of the Processor trace (which is the execution trace provided by the `brainfuck_vm`):
/// all input and output values are the same as the one from the execution, in the same order.
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
mod test {
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

    use crate::components::io::{
        component::{InputEval, OutputEval},
        table::{interaction_trace_evaluation, InputTable, IoElements, OutputTable},
    };

    #[test]
    fn test_input_constraints() {
        const LOG_SIZE: u32 = 4;

        // Get an execution trace from a valid Brainfuck program
        let code = "+++>,<[>+.<-]";
        let mut compiler = Compiler::new(code);
        let instructions = compiler.compile();
        let (mut machine, _) = create_test_machine(&instructions, &[1]);
        let () = machine.execute().expect("Failed to execute machine");

        let trace_vm = machine.trace();

        // Construct the IsFirst preprocessed column
        let is_first_col = gen_is_first(LOG_SIZE);
        let preprocessed_trace = vec![is_first_col];

        // Construct the main trace from the execution trace
        let table = InputTable::from(trace_vm);
        let (main_trace, claim) = table.trace_evaluation();

        // Draw Interaction elements
        let input_lookup_elements = IoElements::dummy();

        // Generate interaction trace
        let (interaction_trace, interaction_claim) =
            interaction_trace_evaluation(&main_trace, &input_lookup_elements).unwrap();

        // Create the trace evaluation TreeVec
        let trace = TreeVec::new(vec![preprocessed_trace, main_trace, interaction_trace]);

        // Interpolate the trace for the evaluation
        let trace_polys = trace.map_cols(CircleEvaluation::interpolate);

        // Get the Memory AIR evaluator
        let input_eval = InputEval::new(&claim, input_lookup_elements);

        // Assert that the constraints are valid for a valid Brainfuck program.
        assert_constraints(
            &trace_polys,
            CanonicCoset::new(LOG_SIZE),
            |eval| {
                input_eval.evaluate(eval);
            },
            (interaction_claim.claimed_sum, None),
        );
    }

    #[test]
    fn test_output_constraints() {
        const LOG_SIZE: u32 = 6;

        // Get an execution trace from a valid Brainfuck program
        let code = "+++>,<[>+.<-]";
        let mut compiler = Compiler::new(code);
        let instructions = compiler.compile();
        let (mut machine, _) = create_test_machine(&instructions, &[1]);
        let () = machine.execute().expect("Failed to execute machine");

        let trace_vm = machine.trace();

        // Construct the IsFirst preprocessed column
        let is_first_col = gen_is_first(LOG_SIZE);
        let preprocessed_trace = vec![is_first_col];

        // Construct the main trace from the execution trace
        let table = OutputTable::from(trace_vm);
        let (main_trace, claim) = table.trace_evaluation();

        // Draw Interaction elements
        let output_lookup_elements = IoElements::dummy();

        // Generate interaction trace
        let (interaction_trace, interaction_claim) =
            interaction_trace_evaluation(&main_trace, &output_lookup_elements).unwrap();

        // Create the trace evaluation TreeVec
        let trace = TreeVec::new(vec![preprocessed_trace, main_trace, interaction_trace]);

        // Interpolate the trace for the evaluation
        let trace_polys = trace.map_cols(CircleEvaluation::interpolate);

        // Get the Memory AIR evaluator
        let output_eval = OutputEval::new(&claim, output_lookup_elements);

        // Assert that the constraints are valid for a valid Brainfuck program.
        assert_constraints(
            &trace_polys,
            CanonicCoset::new(LOG_SIZE),
            |eval| {
                output_eval.evaluate(eval);
            },
            (interaction_claim.claimed_sum, None),
        );
    }
}
