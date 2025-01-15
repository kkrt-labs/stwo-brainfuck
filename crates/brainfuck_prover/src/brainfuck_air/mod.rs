use crate::components::{
    instruction::{
        self,
        component::{InstructionComponent, InstructionEval},
        table::{InstructionElements, InstructionTable},
    },
    memory::{
        self,
        component::{MemoryComponent, MemoryEval},
        table::{MemoryElements, MemoryTable},
    },
    processor::{
        self,
        component::{ProcessorComponent, ProcessorEval},
        instructions::{
            end_of_execution::{
                component::{EndOfExecutionComponent, EndOfExecutionEval},
                table::EndOfExecInstructionTable,
            },
            input_component::{InputInstructionComponent, InputInstructionEval},
            jump::{
                jump_if_not_zero_component::{JumpIfNotZeroComponent, JumpIfNotZeroEval},
                jump_if_zero_component::{JumpIfZeroComponent, JumpIfZeroEval},
                table::{JumpIfNotZeroTable, JumpIfZeroTable},
            },
            left_component::{LeftInstructionComponent, LeftInstructionEval},
            minus_component::{MinusInstructionComponent, MinusInstructionEval},
            output_component::{OutputInstructionComponent, OutputInstructionEval},
            plus_component::{PlusInstructionComponent, PlusInstructionEval},
            right_component::{RightInstructionComponent, RightInstructionEval},
            table::{
                InputInstructionTable, LeftInstructionTable, MinusInstructionTable,
                OutputInstructionTable, PlusInstructionTable, RightInstructionTable,
            },
        },
        table::{ProcessorElements, ProcessorTable},
    },
    program::{
        self,
        component::{ProgramComponent, ProgramEval},
        table::ProgramTable,
    },
    EndOfExecutionClaim, InstructionClaim, InteractionClaim, JumpClaim, MemoryClaim,
    ProcessorClaim, ProcessorInstructionClaim, ProgramClaim,
};
use brainfuck_vm::machine::Machine;
use num_traits::Zero;
use serde::{Deserialize, Serialize};
use stwo_prover::{
    constraint_framework::{
        preprocessed_columns::{gen_is_first, PreprocessedColumn},
        TraceLocationAllocator, INTERACTION_TRACE_IDX, ORIGINAL_TRACE_IDX, PREPROCESSED_TRACE_IDX,
    },
    core::{
        air::{Component, ComponentProver},
        backend::simd::{qm31::PackedSecureField, SimdBackend},
        channel::{Blake2sChannel, Channel},
        pcs::{CommitmentSchemeProver, CommitmentSchemeVerifier, PcsConfig, TreeVec},
        poly::circle::{CanonicCoset, PolyOps},
        prover::{self, verify, ProvingError, StarkProof, VerificationError},
        vcs::{
            blake2_merkle::{Blake2sMerkleChannel, Blake2sMerkleHasher},
            ops::MerkleHasher,
        },
    },
};

/// The STARK proof of the execution of a given Brainfuck program.
///
/// It includes the proof as well as the claims during the various phases of the proof generation.
#[derive(Serialize, Deserialize, Debug)]
pub struct BrainfuckProof<H: MerkleHasher> {
    pub claim: BrainfuckClaim,
    pub interaction_claim: BrainfuckInteractionClaim,
    pub proof: StarkProof<H>,
}

/// A claim over the log sizes for each component of the system.
///
/// A component is made of three types of trace:
/// - Preprocessed Trace (Phase 0)
/// - Main Trace (Phase 1)
/// - Interaction Trace (Phase 2)
#[derive(Serialize, Deserialize, Debug)]
pub struct BrainfuckClaim {
    pub memory: MemoryClaim,
    pub instruction: InstructionClaim,
    pub program: ProgramClaim,
    pub processor: ProcessorClaim,
    pub jump_if_not_zero: JumpClaim,
    pub jump_if_zero: JumpClaim,
    pub input_instruction: ProcessorInstructionClaim,
    pub left_instruction: ProcessorInstructionClaim,
    pub minus_instruction: ProcessorInstructionClaim,
    pub output_instruction: ProcessorInstructionClaim,
    pub plus_instruction: ProcessorInstructionClaim,
    pub right_instruction: ProcessorInstructionClaim,
    pub end_of_execution: EndOfExecutionClaim,
}

impl BrainfuckClaim {
    pub fn mix_into(&self, channel: &mut impl Channel) {
        self.memory.mix_into(channel);
        self.instruction.mix_into(channel);
        self.program.mix_into(channel);
        self.processor.mix_into(channel);
        self.jump_if_not_zero.mix_into(channel);
        self.jump_if_zero.mix_into(channel);
        self.input_instruction.mix_into(channel);
        self.left_instruction.mix_into(channel);
        self.minus_instruction.mix_into(channel);
        self.output_instruction.mix_into(channel);
        self.plus_instruction.mix_into(channel);
        self.right_instruction.mix_into(channel);
        self.end_of_execution.mix_into(channel);
    }

    pub fn log_sizes(&self) -> TreeVec<Vec<u32>> {
        let mut log_sizes = TreeVec::concat_cols(
            [
                self.memory.log_sizes(),
                self.instruction.log_sizes(),
                self.program.log_sizes(),
                self.processor.log_sizes(),
                self.jump_if_not_zero.log_sizes(),
                self.jump_if_zero.log_sizes(),
                self.input_instruction.log_sizes(),
                self.left_instruction.log_sizes(),
                self.minus_instruction.log_sizes(),
                self.output_instruction.log_sizes(),
                self.plus_instruction.log_sizes(),
                self.right_instruction.log_sizes(),
                self.end_of_execution.log_sizes(),
            ]
            .into_iter(),
        );

        // We overwrite the preprocessed column claim to have all possible log sizes
        // in the merkle root for the verification.
        log_sizes[PREPROCESSED_TRACE_IDX] = IS_FIRST_LOG_SIZES.to_vec();

        log_sizes
    }
}

/// All the interaction elements required by the components during the interaction phase 2.
///
/// The elements are drawn from a Fiat-Shamir [`Channel`], currently using the BLAKE2 hash.
pub struct BrainfuckInteractionElements {
    pub memory_lookup_elements: MemoryElements,
    pub instruction_lookup_elements: InstructionElements,
    pub processor_lookup_elements: ProcessorElements,
}

impl BrainfuckInteractionElements {
    /// Draw all the interaction elements needed for
    /// all the components of the system.
    pub fn draw(channel: &mut impl Channel) -> Self {
        Self {
            memory_lookup_elements: MemoryElements::draw(channel),
            instruction_lookup_elements: InstructionElements::draw(channel),
            processor_lookup_elements: ProcessorElements::draw(channel),
        }
    }
}

/// A claim over the claimed sum of the interaction columns for each component of the system
///
/// Needed for the lookup protocol (logUp with AIR).
#[derive(Serialize, Deserialize, Debug)]
pub struct BrainfuckInteractionClaim {
    memory: InteractionClaim,
    instruction: InteractionClaim,
    program: InteractionClaim,
    processor: InteractionClaim,
    jump_if_not_zero: InteractionClaim,
    jump_if_zero: InteractionClaim,
    input_instruction: InteractionClaim,
    left_instruction: InteractionClaim,
    minus_instruction: InteractionClaim,
    output_instruction: InteractionClaim,
    plus_instruction: InteractionClaim,
    right_instruction: InteractionClaim,
    end_of_execution: InteractionClaim,
}

impl BrainfuckInteractionClaim {
    /// Mix the claimed sums of every components in the Fiat-Shamir [`Channel`].
    pub fn mix_into(&self, channel: &mut impl Channel) {
        self.memory.mix_into(channel);
        self.instruction.mix_into(channel);
        self.program.mix_into(channel);
        self.processor.mix_into(channel);
        self.jump_if_not_zero.mix_into(channel);
        self.jump_if_zero.mix_into(channel);
        self.input_instruction.mix_into(channel);
        self.left_instruction.mix_into(channel);
        self.minus_instruction.mix_into(channel);
        self.output_instruction.mix_into(channel);
        self.plus_instruction.mix_into(channel);
        self.right_instruction.mix_into(channel);
        self.end_of_execution.mix_into(channel);
    }
}

/// Verify that the claims (i.e. Statement) are valid.
pub fn lookup_sum_valid(interaction_claim: &BrainfuckInteractionClaim) -> bool {
    let mut sum = PackedSecureField::zero();

    sum += interaction_claim.memory.claimed_sum.into();
    sum += interaction_claim.instruction.claimed_sum.into();
    sum += interaction_claim.program.claimed_sum.into();

    sum += interaction_claim.processor.claimed_sum.into();

    sum += interaction_claim.jump_if_not_zero.claimed_sum.into();
    sum += interaction_claim.jump_if_zero.claimed_sum.into();
    sum += interaction_claim.input_instruction.claimed_sum.into();
    sum += interaction_claim.left_instruction.claimed_sum.into();
    sum += interaction_claim.minus_instruction.claimed_sum.into();
    sum += interaction_claim.output_instruction.claimed_sum.into();
    sum += interaction_claim.plus_instruction.claimed_sum.into();
    sum += interaction_claim.right_instruction.claimed_sum.into();
    sum += interaction_claim.end_of_execution.claimed_sum.into();

    sum.is_zero()
}

/// All the components that constitute the Brainfuck ZK-VM.
///
/// Components are used by the prover as a `ComponentProver`,
/// and by the verifier as a `Component`.
pub struct BrainfuckComponents {
    memory: MemoryComponent,
    instruction: InstructionComponent,
    program: ProgramComponent,
    processor: ProcessorComponent,
    jump_if_not_zero: JumpIfNotZeroComponent,
    jump_if_zero: JumpIfZeroComponent,
    input_instruction: InputInstructionComponent,
    left_instruction: LeftInstructionComponent,
    minus_instruction: MinusInstructionComponent,
    output_instruction: OutputInstructionComponent,
    plus_instruction: PlusInstructionComponent,
    right_instruction: RightInstructionComponent,
    end_of_execution: EndOfExecutionComponent,
}

#[allow(clippy::too_many_lines)]
impl BrainfuckComponents {
    /// Initializes all the Brainfuck components from the claims generated from the trace.
    pub fn new(
        claim: &BrainfuckClaim,
        interaction_elements: &BrainfuckInteractionElements,
        interaction_claim: &BrainfuckInteractionClaim,
    ) -> Self {
        let tree_span_provider = &mut TraceLocationAllocator::new_with_preproccessed_columns(
            &IS_FIRST_LOG_SIZES
                .iter()
                .copied()
                .map(PreprocessedColumn::IsFirst)
                .collect::<Vec<_>>(),
        );

        let memory = MemoryComponent::new(
            tree_span_provider,
            MemoryEval::new(&claim.memory, interaction_elements.memory_lookup_elements.clone()),
            (interaction_claim.memory.claimed_sum, None),
        );

        let instruction = InstructionComponent::new(
            tree_span_provider,
            InstructionEval::new(
                &claim.instruction,
                interaction_elements.instruction_lookup_elements.clone(),
            ),
            (interaction_claim.instruction.claimed_sum, None),
        );

        let program = ProgramComponent::new(
            tree_span_provider,
            ProgramEval::new(
                &claim.program,
                interaction_elements.instruction_lookup_elements.clone(),
            ),
            (interaction_claim.program.claimed_sum, None),
        );

        let processor = ProcessorComponent::new(
            tree_span_provider,
            ProcessorEval::new(
                &claim.processor,
                interaction_elements.memory_lookup_elements.clone(),
                interaction_elements.instruction_lookup_elements.clone(),
                interaction_elements.processor_lookup_elements.clone(),
            ),
            (interaction_claim.processor.claimed_sum, None),
        );

        let jump_if_not_zero = JumpIfNotZeroComponent::new(
            tree_span_provider,
            JumpIfNotZeroEval::new(
                &claim.jump_if_not_zero,
                interaction_elements.processor_lookup_elements.clone(),
            ),
            (interaction_claim.jump_if_not_zero.claimed_sum, None),
        );

        let jump_if_zero = JumpIfZeroComponent::new(
            tree_span_provider,
            JumpIfZeroEval::new(
                &claim.jump_if_zero,
                interaction_elements.processor_lookup_elements.clone(),
            ),
            (interaction_claim.jump_if_zero.claimed_sum, None),
        );

        let input_instruction = InputInstructionComponent::new(
            tree_span_provider,
            InputInstructionEval::new(
                &claim.input_instruction,
                interaction_elements.processor_lookup_elements.clone(),
            ),
            (interaction_claim.input_instruction.claimed_sum, None),
        );

        let left_instruction = LeftInstructionComponent::new(
            tree_span_provider,
            LeftInstructionEval::new(
                &claim.left_instruction,
                interaction_elements.processor_lookup_elements.clone(),
            ),
            (interaction_claim.left_instruction.claimed_sum, None),
        );

        let minus_instruction = MinusInstructionComponent::new(
            tree_span_provider,
            MinusInstructionEval::new(
                &claim.minus_instruction,
                interaction_elements.processor_lookup_elements.clone(),
            ),
            (interaction_claim.minus_instruction.claimed_sum, None),
        );

        let output_instruction = OutputInstructionComponent::new(
            tree_span_provider,
            OutputInstructionEval::new(
                &claim.output_instruction,
                interaction_elements.processor_lookup_elements.clone(),
            ),
            (interaction_claim.output_instruction.claimed_sum, None),
        );

        let plus_instruction = PlusInstructionComponent::new(
            tree_span_provider,
            PlusInstructionEval::new(
                &claim.plus_instruction,
                interaction_elements.processor_lookup_elements.clone(),
            ),
            (interaction_claim.plus_instruction.claimed_sum, None),
        );

        let right_instruction = RightInstructionComponent::new(
            tree_span_provider,
            RightInstructionEval::new(
                &claim.right_instruction,
                interaction_elements.processor_lookup_elements.clone(),
            ),
            (interaction_claim.right_instruction.claimed_sum, None),
        );

        let end_of_execution = EndOfExecutionComponent::new(
            tree_span_provider,
            EndOfExecutionEval::new(
                &claim.end_of_execution,
                interaction_elements.processor_lookup_elements.clone(),
            ),
            (interaction_claim.end_of_execution.claimed_sum, None),
        );

        Self {
            memory,
            instruction,
            program,
            processor,
            jump_if_not_zero,
            jump_if_zero,
            input_instruction,
            left_instruction,
            minus_instruction,
            output_instruction,
            plus_instruction,
            right_instruction,
            end_of_execution,
        }
    }

    /// Returns the `ComponentProver` of each components, used by the prover.
    pub fn provers(&self) -> Vec<&dyn ComponentProver<SimdBackend>> {
        vec![
            &self.memory,
            &self.instruction,
            &self.program,
            &self.processor,
            &self.jump_if_not_zero,
            &self.jump_if_zero,
            &self.input_instruction,
            &self.left_instruction,
            &self.minus_instruction,
            &self.output_instruction,
            &self.plus_instruction,
            &self.right_instruction,
            &self.end_of_execution,
        ]
    }

    /// Returns the `Component` of each components, used by the verifier.
    pub fn components(&self) -> Vec<&dyn Component> {
        self.provers().into_iter().map(|component| component as &dyn Component).collect()
    }
}

/// `LOG_MAX_ROWS = ilog2(MAX_ROWS)`
///
/// Means that the ZK-VM does not accept programs inducing a component with more than 2^23 steps (8M
/// steps).
#[cfg(not(test))]
const LOG_MAX_ROWS: u32 = 23;

#[cfg(test)]
/// Means that the ZK-VM does not accept programs inducing a component with more than 2^23 steps (8M
/// steps).
const LOG_MAX_ROWS: u32 = 20;

/// Log sizes of the preprocessed columns
/// used for enforcing boundary constraints.
///
/// Preprocessed columns are generated ahead of time,
/// so at this moment we don't know the log size
/// of the main and interaction traces.
///
/// Therefore, we generate all log sizes that we
/// want to support, so that the verifier can be
/// provided a merkle root it can trust, for a claim
/// of any dynamic size.
///
/// Ideally, we should cover all possible log sizes, between
/// 1 and `LOG_MAX_ROW`
#[cfg(not(test))]
const IS_FIRST_LOG_SIZES: [u32; 21] =
    [24, 23, 22, 21, 20, 19, 18, 17, 16, 15, 14, 13, 12, 11, 10, 9, 8, 7, 6, 5, 4];

#[cfg(test)]
const IS_FIRST_LOG_SIZES: [u32; 12] = [15, 14, 13, 12, 11, 10, 9, 8, 7, 6, 5, 4];

/// Generate a STARK proof of the given Brainfuck program execution.
///
/// # Arguments
/// * `inputs` - The Brainfuck VM state to be proven (i.e. after the program execution).
#[allow(clippy::too_many_lines)]
pub fn prove_brainfuck(
    inputs: &Machine,
) -> Result<BrainfuckProof<Blake2sMerkleHasher>, ProvingError> {
    // ┌──────────────────────────┐
    // │     Protocol Setup       │
    // └──────────────────────────┘

    tracing::info!("Protocol Setup");
    let config = PcsConfig::default();
    let twiddles = SimdBackend::precompute_twiddles(
        CanonicCoset::new(LOG_MAX_ROWS + config.fri_config.log_blowup_factor + 2)
            .circle_domain()
            .half_coset,
    );
    let channel = &mut Blake2sChannel::default();
    let mut commitment_scheme =
        CommitmentSchemeProver::<_, Blake2sMerkleChannel>::new(config, &twiddles);

    // ┌───────────────────────────────────────────────┐
    // │   Interaction Phase 0 - Preprocessed Trace    │
    // └───────────────────────────────────────────────┘

    tracing::info!("Preprocessed Trace");
    // Generate all preprocessed columns
    let mut tree_builder = commitment_scheme.tree_builder();

    tree_builder.extend_evals(IS_FIRST_LOG_SIZES.iter().copied().map(gen_is_first::<SimdBackend>));

    // Commit the preprocessed trace
    tree_builder.commit(channel);

    // ┌───────────────────────────────────────┐
    // │    Interaction Phase 1 - Main Trace   │
    // └───────────────────────────────────────┘

    tracing::info!("Main Trace");
    let mut tree_builder = commitment_scheme.tree_builder();
    let vm_trace = inputs.trace();

    // Get the component's trace from the execution trace, and do the trace evaluation.
    let (memory_trace, memory_claim) = MemoryTable::from(&vm_trace).trace_evaluation().unwrap();

    let (instruction_trace, instruction_claim) =
        InstructionTable::from((&vm_trace, inputs.program())).trace_evaluation().unwrap();

    let (program_trace, program_claim) =
        ProgramTable::from(inputs.program()).trace_evaluation().unwrap();

    let (jump_if_not_zero_trace, jump_if_not_zero_claim) =
        JumpIfNotZeroTable::from(&vm_trace).trace_evaluation();

    let (jump_if_zero_trace, jump_if_zero_claim) =
        JumpIfZeroTable::from(&vm_trace).trace_evaluation();

    let (input_instruction_trace, input_instruction_claim) =
        InputInstructionTable::from(&vm_trace).trace_evaluation();

    let (left_instruction_trace, left_instruction_claim) =
        LeftInstructionTable::from(&vm_trace).trace_evaluation();

    let (minus_instruction_trace, minus_instruction_claim) =
        MinusInstructionTable::from(&vm_trace).trace_evaluation();

    let (output_instruction_trace, output_instruction_claim) =
        OutputInstructionTable::from(&vm_trace).trace_evaluation();

    let (plus_instruction_trace, plus_instruction_claim) =
        PlusInstructionTable::from(&vm_trace).trace_evaluation();

    let (right_instruction_trace, right_instruction_claim) =
        RightInstructionTable::from(&vm_trace).trace_evaluation();

    let (end_of_execution_trace, end_of_execution_claim) =
        EndOfExecInstructionTable::from(&vm_trace).trace_evaluation().unwrap();

    let (processor_trace, processor_claim) =
        ProcessorTable::from(&vm_trace).trace_evaluation().unwrap();

    // Add the components' trace evaluation to the commit tree.
    tree_builder.extend_evals(memory_trace.clone());
    tree_builder.extend_evals(instruction_trace.clone());
    tree_builder.extend_evals(program_trace.clone());
    tree_builder.extend_evals(processor_trace.clone());
    tree_builder.extend_evals(jump_if_not_zero_trace.clone());
    tree_builder.extend_evals(jump_if_zero_trace.clone());
    tree_builder.extend_evals(input_instruction_trace.clone());
    tree_builder.extend_evals(left_instruction_trace.clone());
    tree_builder.extend_evals(minus_instruction_trace.clone());
    tree_builder.extend_evals(output_instruction_trace.clone());
    tree_builder.extend_evals(plus_instruction_trace.clone());
    tree_builder.extend_evals(right_instruction_trace.clone());
    tree_builder.extend_evals(end_of_execution_trace.clone());

    let claim = BrainfuckClaim {
        memory: memory_claim,
        instruction: instruction_claim,
        program: program_claim,
        processor: processor_claim,
        jump_if_not_zero: jump_if_not_zero_claim,
        jump_if_zero: jump_if_zero_claim,
        input_instruction: input_instruction_claim,
        left_instruction: left_instruction_claim,
        minus_instruction: minus_instruction_claim,
        output_instruction: output_instruction_claim,
        plus_instruction: plus_instruction_claim,
        right_instruction: right_instruction_claim,
        end_of_execution: end_of_execution_claim,
    };

    // Mix the claim into the Fiat-Shamir channel.
    claim.mix_into(channel);
    // Commit the main trace.
    tree_builder.commit(channel);

    // ┌───────────────────────────────────────────────┐
    // │    Interaction Phase 2 - Interaction Trace    │
    // └───────────────────────────────────────────────┘

    tracing::info!("Interaction Trace");
    // Draw interaction elements
    let interaction_elements = BrainfuckInteractionElements::draw(channel);

    // Generate the interaction trace from the main trace, and compute the logUp sum.
    let mut tree_builder = commitment_scheme.tree_builder();

    let (memory_interaction_trace_eval, memory_interaction_claim) =
        memory::table::interaction_trace_evaluation(
            &memory_trace,
            &interaction_elements.memory_lookup_elements,
        )
        .unwrap();

    let (instruction_interaction_trace_eval, instruction_interaction_claim) =
        instruction::table::interaction_trace_evaluation(
            &instruction_trace,
            &interaction_elements.instruction_lookup_elements,
        )
        .unwrap();

    let (program_interaction_trace_eval, program_interaction_claim) =
        program::table::interaction_trace_evaluation(
            &program_trace,
            &interaction_elements.instruction_lookup_elements,
        )
        .unwrap();

    let (processor_interaction_trace_eval, processor_interaction_claim) =
        processor::table::interaction_trace_evaluation(
            &processor_trace,
            &interaction_elements.instruction_lookup_elements,
            &interaction_elements.memory_lookup_elements,
            &interaction_elements.processor_lookup_elements,
        )
        .unwrap();

    let (jump_if_not_zero_interaction_trace_eval, jump_if_not_zero_interaction_claim) =
        processor::instructions::jump::table::interaction_trace_evaluation(
            &jump_if_not_zero_trace,
            &interaction_elements.processor_lookup_elements,
        )
        .unwrap();

    let (jump_if_zero_interaction_trace_eval, jump_if_zero_interaction_claim) =
        processor::instructions::jump::table::interaction_trace_evaluation(
            &jump_if_zero_trace,
            &interaction_elements.processor_lookup_elements,
        )
        .unwrap();

    let (input_instruction_interaction_trace_eval, input_instruction_interaction_claim) =
        processor::instructions::table::interaction_trace_evaluation(
            &input_instruction_trace,
            &interaction_elements.processor_lookup_elements,
        )
        .unwrap();

    let (left_instruction_interaction_trace_eval, left_instruction_interaction_claim) =
        processor::instructions::table::interaction_trace_evaluation(
            &left_instruction_trace,
            &interaction_elements.processor_lookup_elements,
        )
        .unwrap();

    let (minus_instruction_interaction_trace_eval, minus_instruction_interaction_claim) =
        processor::instructions::table::interaction_trace_evaluation(
            &minus_instruction_trace,
            &interaction_elements.processor_lookup_elements,
        )
        .unwrap();

    let (output_instruction_interaction_trace_eval, output_instruction_interaction_claim) =
        processor::instructions::table::interaction_trace_evaluation(
            &output_instruction_trace,
            &interaction_elements.processor_lookup_elements,
        )
        .unwrap();

    let (plus_instruction_interaction_trace_eval, plus_instruction_interaction_claim) =
        processor::instructions::table::interaction_trace_evaluation(
            &plus_instruction_trace,
            &interaction_elements.processor_lookup_elements,
        )
        .unwrap();

    let (right_instruction_interaction_trace_eval, right_instruction_interaction_claim) =
        processor::instructions::table::interaction_trace_evaluation(
            &right_instruction_trace,
            &interaction_elements.processor_lookup_elements,
        )
        .unwrap();

    let (end_of_execution_interaction_trace_eval, end_of_execution_interaction_claim) =
        processor::instructions::end_of_execution::table::interaction_trace_evaluation(
            &end_of_execution_trace,
            &interaction_elements.processor_lookup_elements,
        )
        .unwrap();

    // Add the components' interaction trace evaluation to the commit tree.
    tree_builder.extend_evals(memory_interaction_trace_eval);
    tree_builder.extend_evals(instruction_interaction_trace_eval);
    tree_builder.extend_evals(program_interaction_trace_eval);
    tree_builder.extend_evals(processor_interaction_trace_eval);
    tree_builder.extend_evals(jump_if_not_zero_interaction_trace_eval);
    tree_builder.extend_evals(jump_if_zero_interaction_trace_eval);
    tree_builder.extend_evals(input_instruction_interaction_trace_eval);
    tree_builder.extend_evals(left_instruction_interaction_trace_eval);
    tree_builder.extend_evals(minus_instruction_interaction_trace_eval);
    tree_builder.extend_evals(output_instruction_interaction_trace_eval);
    tree_builder.extend_evals(plus_instruction_interaction_trace_eval);
    tree_builder.extend_evals(right_instruction_interaction_trace_eval);
    tree_builder.extend_evals(end_of_execution_interaction_trace_eval);

    let interaction_claim = BrainfuckInteractionClaim {
        memory: memory_interaction_claim,
        instruction: instruction_interaction_claim,
        program: program_interaction_claim,
        processor: processor_interaction_claim,
        jump_if_not_zero: jump_if_not_zero_interaction_claim,
        jump_if_zero: jump_if_zero_interaction_claim,
        input_instruction: input_instruction_interaction_claim,
        left_instruction: left_instruction_interaction_claim,
        minus_instruction: minus_instruction_interaction_claim,
        output_instruction: output_instruction_interaction_claim,
        plus_instruction: plus_instruction_interaction_claim,
        right_instruction: right_instruction_interaction_claim,
        end_of_execution: end_of_execution_interaction_claim,
    };

    // Mix the interaction claim into the Fiat-Shamir channel.
    interaction_claim.mix_into(channel);
    // Commit the interaction trace.
    tree_builder.commit(channel);

    // ┌──────────────────────────┐
    // │     Proof Generation     │
    // └──────────────────────────┘
    tracing::info!("Proof Generation");
    let component_builder =
        BrainfuckComponents::new(&claim, &interaction_elements, &interaction_claim);
    let components = component_builder.provers();
    let proof = prover::prove::<SimdBackend, _>(&components, channel, commitment_scheme)?;

    Ok(BrainfuckProof { claim, interaction_claim, proof })
}

/// Verify a given STARK proof of a Brainfuck program execution with corresponding claim.
pub fn verify_brainfuck(
    BrainfuckProof { claim, interaction_claim, proof }: BrainfuckProof<Blake2sMerkleHasher>,
) -> Result<(), VerificationError> {
    // ┌──────────────────────────┐
    // │     Protocol Setup       │
    // └──────────────────────────┘
    let config = PcsConfig::default();
    let channel = &mut Blake2sChannel::default();
    let commitment_scheme_verifier =
        &mut CommitmentSchemeVerifier::<Blake2sMerkleChannel>::new(config);
    let log_sizes = &claim.log_sizes();

    // ┌───────────────────────────────────────────────┐
    // │   Interaction Phase 0 - Preprocessed Trace    │
    // └───────────────────────────────────────────────┘

    commitment_scheme_verifier.commit(
        proof.commitments[PREPROCESSED_TRACE_IDX],
        &log_sizes[PREPROCESSED_TRACE_IDX],
        channel,
    );

    // ┌───────────────────────────────────────┐
    // │    Interaction Phase 1 - Main Trace   │
    // └───────────────────────────────────────┘
    claim.mix_into(channel);
    commitment_scheme_verifier.commit(
        proof.commitments[ORIGINAL_TRACE_IDX],
        &log_sizes[ORIGINAL_TRACE_IDX],
        channel,
    );

    // ┌───────────────────────────────────────────────┐
    // │    Interaction Phase 2 - Interaction Trace    │
    // └───────────────────────────────────────────────┘

    let interaction_elements = BrainfuckInteractionElements::draw(channel);

    // Check that the lookup sum is valid, otherwise throw
    if !lookup_sum_valid(&interaction_claim) {
        return Err(VerificationError::InvalidLookup("Invalid LogUp sum".to_string()));
    };

    interaction_claim.mix_into(channel);
    commitment_scheme_verifier.commit(
        proof.commitments[INTERACTION_TRACE_IDX],
        &log_sizes[INTERACTION_TRACE_IDX],
        channel,
    );

    // ┌──────────────────────────┐
    // │    Proof Verification    │
    // └──────────────────────────┘

    let component_builder =
        BrainfuckComponents::new(&claim, &interaction_elements, &interaction_claim);
    let components = component_builder.components();

    verify(&components, channel, commitment_scheme_verifier, proof)
}

#[cfg(test)]
mod tests {
    use super::{prove_brainfuck, verify_brainfuck};
    use brainfuck_vm::{compiler::Compiler, test_helper::create_test_machine};

    #[test]
    fn test_proof() {
        // Get an execution trace from a valid Brainfuck program
        let code = "+++>,<[>+.<-]";
        let mut compiler = Compiler::new(code);
        let instructions = compiler.compile();
        let (mut machine, _) = create_test_machine(&instructions, &[1]);
        let () = machine.execute().expect("Failed to execute machine");

        let brainfuck_proof = prove_brainfuck(&machine).unwrap();

        verify_brainfuck(brainfuck_proof).unwrap();
    }

    #[test]
    fn test_proof_hello_world() {
        // Get an execution trace from a valid Brainfuck program
        let code = "++++++++++[>+++++++>++++++++++>+++>+<<<<-]>++.>+.+++++++..+++.>++.<<+++++++++++++++.>.+++.------.--------.>+.>.";
        let mut compiler = Compiler::new(code);
        let instructions = compiler.compile();
        let (mut machine, _) = create_test_machine(&instructions, &[]);
        let () = machine.execute().expect("Failed to execute machine");

        let brainfuck_proof = prove_brainfuck(&machine).unwrap();

        verify_brainfuck(brainfuck_proof).unwrap();
    }

    #[test]
    fn test_proof_no_input() {
        // Get an execution trace from a valid Brainfuck program
        let code = "+++><[>+<-]";
        let mut compiler = Compiler::new(code);
        let instructions = compiler.compile();
        let (mut machine, _) = create_test_machine(&instructions, &[]);
        let () = machine.execute().expect("Failed to execute machine");

        let brainfuck_proof = prove_brainfuck(&machine).unwrap();

        verify_brainfuck(brainfuck_proof).unwrap();
    }

    #[test]
    fn test_proof_jump_middle_of_program() {
        // Get an execution trace from a valid Brainfuck program
        let code = "++[-]+.";
        let mut compiler = Compiler::new(code);
        let instructions = compiler.compile();
        let (mut machine, _) = create_test_machine(&instructions, &[]);
        let () = machine.execute().expect("Failed to execute machine");

        let brainfuck_proof = prove_brainfuck(&machine).unwrap();

        verify_brainfuck(brainfuck_proof).unwrap();
    }
}
