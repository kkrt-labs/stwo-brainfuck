use crate::components::{
    instruction::table::InstructionElements, io::table::IoElements, memory::table::MemoryElements,
    ProcessorClaim,
};
use brainfuck_vm::instruction::{InstructionType, VALID_INSTRUCTIONS_BF};
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

/// Computes the value of the deselector polynomial for a given `ci` value from the trace
/// and the wanted instruction.
///
/// This polynomial allows to conditionally render AIR for the various instructions.
///
/// # Arguments
/// * ci - The evaluated value on which the deselector polynomial is evaluated upon.
/// * instruction - The type of instruction which
///
/// # Returns
/// It returns zero when `ci` is 0 or different from the available instructions except one.
/// If `ci` equals the `instruction`, then it returns something non-zero.
pub fn deselector_polynomial<E: EvalAtRow>(ci: &E::F, instruction: &InstructionType) -> E::F {
    VALID_INSTRUCTIONS_BF
        .iter()
        .filter(|&&val| val != instruction.to_base_field())
        .fold(ci.clone(), |acc, &val| acc * (ci.clone() - val.into()))
}

#[cfg(test)]
/// Equivalent of `deselector_polynomial` with the [`BaseField`],
/// used to easily test the logic.
pub fn deselector_poly(ci: &BaseField, instruction: &InstructionType) -> BaseField {
    VALID_INSTRUCTIONS_BF
        .iter()
        .filter(|&&val| val != instruction.to_base_field())
        .fold(*ci, |acc, &val| acc * (*ci - val))
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
        let next_ip = eval.next_trace_mask();
        let _next_ci = eval.next_trace_mask();
        let _next_ni = eval.next_trace_mask();
        let next_mp = eval.next_trace_mask();
        let next_mv = eval.next_trace_mask();
        let _next_mvi = eval.next_trace_mask();
        let next_d = eval.next_trace_mask();

        // TODO: Huge inefficiency (implies constraints of degree at least 8...)
        // TODO: Remove this deselector by splitting all instructions into their own components.
        let deselector_jump_if_zero = deselector_polynomial::<E>(&ci, &InstructionType::JumpIfZero);
        let deselector_jump_if_not_zero =
            deselector_polynomial::<E>(&ci, &InstructionType::JumpIfNotZero);
        let deselector_left = deselector_polynomial::<E>(&ci, &InstructionType::Left);
        let deselector_right = deselector_polynomial::<E>(&ci, &InstructionType::Right);
        let deselector_minus = deselector_polynomial::<E>(&ci, &InstructionType::Minus);
        let deselector_plus = deselector_polynomial::<E>(&ci, &InstructionType::Plus);
        let deselector_input = deselector_polynomial::<E>(&ci, &InstructionType::ReadChar);
        let deselector_output = deselector_polynomial::<E>(&ci, &InstructionType::PutChar);

        let is_mv_zero = E::F::one() - mv.clone() * mvi.clone();

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
        eval.add_constraint(mvi.clone() * (mv.clone() * mvi.clone() - E::F::one()));

        // Transition constraints

        // `clk` increases by 1
        eval.add_constraint(next_clk.clone() - clk.clone() - E::F::one());

        // JumpIfZero - [
        // Jump to `ni` if `mv = 0`. Otherwise, skip two.
        eval.add_constraint(
            deselector_jump_if_zero.clone() *
                (mvi.clone() * (next_ip.clone() - ip.clone() - BaseField::from(2).into()) +
                    is_mv_zero.clone() * (next_ip.clone() - ni.clone())),
        );
        // `mp` remains the same
        eval.add_constraint(deselector_jump_if_zero.clone() * (next_mp.clone() - mp.clone()));
        // `mv` remains the same
        eval.add_constraint(deselector_jump_if_zero * (next_mv.clone() - mv.clone()));

        // JumpIfNotZero - ]
        // Jump to `ni` if `mv != 0`. Otherwise, skip two.
        eval.add_constraint(
            deselector_jump_if_not_zero.clone() *
                (is_mv_zero * (next_ip.clone() - ip.clone() - BaseField::from(2).into()) +
                    mvi * (next_ip.clone() - ni.clone())),
        );
        // `mp` remains the same
        eval.add_constraint(deselector_jump_if_not_zero.clone() * (next_mp.clone() - mp.clone())); // `mv` remains the same
        eval.add_constraint(deselector_jump_if_not_zero * (next_mv.clone() - mv.clone()));

        // ShiftLeft - <

        // `ip` increases by one
        eval.add_constraint(deselector_left.clone() * (next_ip.clone() - ip.clone() - E::F::one())); // `mp` decreases by one
        eval.add_constraint(deselector_left * (next_mp.clone() - mp.clone() + E::F::one()));

        // ShiftRight - >
        // `ip` increases by one
        eval.add_constraint(
            deselector_right.clone() * (next_ip.clone() - ip.clone() - E::F::one()),
        );
        // `mp` increases by one
        eval.add_constraint(deselector_right * (next_mp.clone() - mp.clone() - E::F::one()));

        // MemoryDecrement - -
        // `ip` increases by one
        eval.add_constraint(
            deselector_minus.clone() * (next_ip.clone() - ip.clone() - E::F::one()),
        );
        // `mp` remains the same
        eval.add_constraint(deselector_minus.clone() * (next_mp.clone() - mp.clone()));
        // `mv` decreases by one
        eval.add_constraint(deselector_minus * (next_mv.clone() - mv.clone() + E::F::one()));

        // MemoryIncrement - +
        // `ip` increases by one
        eval.add_constraint(deselector_plus.clone() * (next_ip.clone() - ip.clone() - E::F::one())); // `mp` remains the same
        eval.add_constraint(deselector_plus.clone() * (next_mp.clone() - mp.clone()));
        // `mv` increases by one
        eval.add_constraint(deselector_plus * (next_mv.clone() - mv.clone() - E::F::one()));

        // Input - ,
        // `ip` increases by one
        eval.add_constraint(
            deselector_input.clone() * (next_ip.clone() - ip.clone() - E::F::one()),
        );
        // `mp` remains the same
        eval.add_constraint(deselector_input * (next_mp.clone() - mp.clone()));

        // Output - .
        // `ip` increases by one
        eval.add_constraint(deselector_output.clone() * (next_ip - ip.clone() - E::F::one()));
        // `mp` remains the same
        eval.add_constraint(deselector_output.clone() * (next_mp.clone() - mp.clone()));
        // `mv` remains the same
        eval.add_constraint(deselector_output * (next_mv.clone() - mv.clone()));

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
    use super::deselector_poly;
    use crate::components::{
        instruction::table::InstructionElements,
        io::table::IoElements,
        memory::table::MemoryElements,
        processor::{
            component::ProcessorEval,
            table::{interaction_trace_evaluation, ProcessorTable},
        },
    };
    use brainfuck_vm::{
        compiler::Compiler, instruction::InstructionType, test_helper::create_test_machine,
    };
    use num_traits::Zero;
    use stwo_prover::{
        constraint_framework::{
            assert_constraints, preprocessed_columns::gen_is_first, FrameworkEval,
        },
        core::{
            fields::m31::BaseField,
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

    #[test]
    fn deselector_jump_if_zero_valid() {
        let ci = InstructionType::JumpIfZero.to_base_field();
        let deselector_jump_if_zero = deselector_poly(&ci, &InstructionType::JumpIfZero);

        assert_ne!(deselector_jump_if_zero, BaseField::zero());
    }

    #[test]
    fn deselector_jump_if_zero_invalid() {
        let ci = InstructionType::JumpIfZero.to_base_field();
        let deselector_jump_if_zero = deselector_poly(&ci, &InstructionType::Plus);

        assert_eq!(deselector_jump_if_zero, BaseField::zero());
    }

    #[test]
    fn deselector_jump_if_not_zero_valid() {
        let ci = InstructionType::JumpIfNotZero.to_base_field();
        let deselector_jump_if_not_zero = deselector_poly(&ci, &InstructionType::JumpIfNotZero);

        assert_ne!(deselector_jump_if_not_zero, BaseField::zero());
    }

    #[test]
    fn deselector_jump_if_not_zero_invalid() {
        let ci = InstructionType::JumpIfNotZero.to_base_field();
        let deselector_jump_if_not_zero = deselector_poly(&ci, &InstructionType::Left);

        assert_eq!(deselector_jump_if_not_zero, BaseField::zero());
    }

    #[test]
    fn deselector_left_valid() {
        let ci = InstructionType::Left.to_base_field();
        let deselector_left = deselector_poly(&ci, &InstructionType::Left);

        assert_ne!(deselector_left, BaseField::zero());
    }

    #[test]
    fn deselector_left_invalid() {
        let ci = InstructionType::Left.to_base_field();
        let deselector_left = deselector_poly(&ci, &InstructionType::JumpIfZero);

        assert_eq!(deselector_left, BaseField::zero());
    }

    #[test]
    fn deselector_right_valid() {
        let ci = InstructionType::Right.to_base_field();
        let deselector_right = deselector_poly(&ci, &InstructionType::Right);

        assert_ne!(deselector_right, BaseField::zero());
    }

    #[test]
    fn deselector_right_invalid() {
        let ci = InstructionType::Right.to_base_field();
        let deselector_right = deselector_poly(&ci, &InstructionType::JumpIfZero);

        assert_eq!(deselector_right, BaseField::zero());
    }

    #[test]
    fn deselector_minus_valid() {
        let ci = InstructionType::Minus.to_base_field();
        let deselector_minus = deselector_poly(&ci, &InstructionType::Minus);

        assert_ne!(deselector_minus, BaseField::zero());
    }

    #[test]
    fn deselector_minus_invalid() {
        let ci = InstructionType::Minus.to_base_field();
        let deselector_minus = deselector_poly(&ci, &InstructionType::JumpIfZero);

        assert_eq!(deselector_minus, BaseField::zero());
    }

    #[test]
    fn deselector_plus_valid() {
        let ci = InstructionType::Plus.to_base_field();
        let deselector_plus = deselector_poly(&ci, &InstructionType::Plus);

        assert_ne!(deselector_plus, BaseField::zero());
    }

    #[test]
    fn deselector_plus_invalid() {
        let ci = InstructionType::Plus.to_base_field();
        let deselector_plus = deselector_poly(&ci, &InstructionType::JumpIfZero);

        assert_eq!(deselector_plus, BaseField::zero());
    }

    #[test]
    fn deselector_input_valid() {
        let ci = InstructionType::ReadChar.to_base_field();
        let deselector_input = deselector_poly(&ci, &InstructionType::ReadChar);

        assert_ne!(deselector_input, BaseField::zero());
    }

    #[test]
    fn deselector_input_invalid() {
        let ci = InstructionType::ReadChar.to_base_field();
        let deselector_input = deselector_poly(&ci, &InstructionType::JumpIfZero);

        assert_eq!(deselector_input, BaseField::zero());
    }

    #[test]
    fn deselector_output_valid() {
        let ci = InstructionType::PutChar.to_base_field();
        let deselector_output = deselector_poly(&ci, &InstructionType::PutChar);

        assert_ne!(deselector_output, BaseField::zero());
    }

    #[test]
    fn deselector_output_invalid() {
        let ci = InstructionType::PutChar.to_base_field();
        let deselector_output = deselector_poly(&ci, &InstructionType::JumpIfZero);

        assert_eq!(deselector_output, BaseField::zero());
    }
}
