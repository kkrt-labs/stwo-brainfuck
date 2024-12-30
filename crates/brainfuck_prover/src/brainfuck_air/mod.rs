use crate::components::{
    instruction::{
        self,
        component::{InstructionComponent, InstructionEval},
        table::{InstructionElements, InstructionTable},
    },
    io::{
        self,
        component::{InputComponent, InputEval, OutputComponent, OutputEval},
        table::{InputTable, IoElements, OutputTable},
    },
    memory::{
        self,
        component::{MemoryComponent, MemoryEval},
        table::{MemoryElements, MemoryTable},
    },
    processor::{
        self,
        component::{ProcessorComponent, ProcessorEval},
        table::ProcessorTable,
    },
    InstructionClaim, IoClaim, MemoryClaim, ProcessorClaim,
};
use brainfuck_vm::machine::Machine;
use stwo_prover::{
    constraint_framework::{
        preprocessed_columns::{gen_is_first, PreprocessedColumn},
        TraceLocationAllocator, INTERACTION_TRACE_IDX, ORIGINAL_TRACE_IDX, PREPROCESSED_TRACE_IDX,
    },
    core::{
        air::{Component, ComponentProver},
        backend::simd::SimdBackend,
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
pub struct BrainfuckProof<H: MerkleHasher> {
    pub claim: BrainfuckClaim,
    pub interaction_claim: BrainfuckInteractionClaim,
    pub proof: StarkProof<H>,
}

/// All the claims from the first phase (interaction phase 0).
///
/// It includes the common claim values such as the initial and final states
/// and the claim of each component.
pub struct BrainfuckClaim {
    pub input: IoClaim,
    pub output: IoClaim,
    pub memory: MemoryClaim,
    pub instruction: InstructionClaim,
    pub processor: ProcessorClaim,
}

impl BrainfuckClaim {
    pub fn mix_into(&self, channel: &mut impl Channel) {
        self.input.mix_into(channel);
        self.output.mix_into(channel);
        self.memory.mix_into(channel);
        self.instruction.mix_into(channel);
        self.processor.mix_into(channel);
    }

    pub fn log_sizes(&self) -> TreeVec<Vec<u32>> {
        let mut log_sizes = TreeVec::concat_cols(
            [
                self.input.log_sizes(),
                self.output.log_sizes(),
                self.memory.log_sizes(),
                self.instruction.log_sizes(),
                self.processor.log_sizes(),
            ]
            .into_iter(),
        );

        // We overwrite the preprocessed column claim to have all log sizes
        // in the merkle root for the verification.
        log_sizes[PREPROCESSED_TRACE_IDX] = IS_FIRST_LOG_SIZES.to_vec();

        log_sizes
    }
}

/// All the interaction elements (drawn from the channel)
/// required by the various components during the interaction phase.
pub struct BrainfuckInteractionElements {
    pub input_lookup_elements: IoElements,
    pub output_lookup_elements: IoElements,
    pub memory_lookup_elements: MemoryElements,
    pub instruction_lookup_elements: InstructionElements,
}

impl BrainfuckInteractionElements {
    /// Draw all the interaction elements needed for
    /// all the components of the Brainfuck ZK-VM.
    pub fn draw(channel: &mut impl Channel) -> Self {
        Self {
            input_lookup_elements: IoElements::draw(channel),
            output_lookup_elements: IoElements::draw(channel),
            memory_lookup_elements: MemoryElements::draw(channel),
            instruction_lookup_elements: InstructionElements::draw(channel),
        }
    }
}

/// All the claims from the second phase (interaction phase 2).
///
/// Mainly the claims on global relations (lookup, permutation, evaluation).
pub struct BrainfuckInteractionClaim {
    input: io::component::InteractionClaim,
    output: io::component::InteractionClaim,
    memory: memory::component::InteractionClaim,
    instruction: instruction::component::InteractionClaim,
    processor: processor::component::InteractionClaim,
}

impl BrainfuckInteractionClaim {
    /// Mix the claimed sums of every components in the Fiat-Shamir [`Channel`].
    pub fn mix_into(&self, channel: &mut impl Channel) {
        self.input.mix_into(channel);
        self.output.mix_into(channel);
        self.memory.mix_into(channel);
        self.instruction.mix_into(channel);
        self.processor.mix_into(channel);
    }
}

/// Verify that the claims (i.e. Statement) are valid.
pub fn lookup_sum_valid(
    _claim: &BrainfuckClaim,
    _interaction_elements: &BrainfuckInteractionElements,
    _interaction_claim: &BrainfuckInteractionClaim,
) -> bool {
    todo!();
}

/// All the components that constitute the Brainfuck ZK-VM.
///
/// Components are used by the prover as a `ComponentProver`,
/// and by the verifier as a `Component`.
pub struct BrainfuckComponents {
    input: InputComponent,
    output: OutputComponent,
    memory: MemoryComponent,
    instruction: InstructionComponent,
    processor: ProcessorComponent,
}

impl BrainfuckComponents {
    /// Initializes all the Brainfuck components from the claims generated from the trace.
    pub fn new(
        claim: &BrainfuckClaim,
        interaction_elements: &BrainfuckInteractionElements,
        interaction_claim: &BrainfuckInteractionClaim,
    ) -> Self {
        let tree_span_provider = &mut TraceLocationAllocator::new_with_preproccessed_columnds(
            &IS_FIRST_LOG_SIZES
                .iter()
                .copied()
                .map(PreprocessedColumn::IsFirst)
                .collect::<Vec<_>>(),
        );

        let input = InputComponent::new(
            tree_span_provider,
            InputEval::new(&claim.input, interaction_elements.input_lookup_elements.clone()),
            (interaction_claim.input.claimed_sum, None),
        );
        let output = OutputComponent::new(
            tree_span_provider,
            OutputEval::new(&claim.output, interaction_elements.output_lookup_elements.clone()),
            (interaction_claim.output.claimed_sum, None),
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
        let processor = ProcessorComponent::new(
            tree_span_provider,
            ProcessorEval::new(
                &claim.processor,
                interaction_elements.input_lookup_elements.clone(),
                interaction_elements.output_lookup_elements.clone(),
                interaction_elements.memory_lookup_elements.clone(),
                interaction_elements.instruction_lookup_elements.clone(),
            ),
            (interaction_claim.processor.claimed_sum, None),
        );

        Self { input, output, memory, instruction, processor }
    }

    /// Returns the `ComponentProver` of each components, used by the prover.
    pub fn provers(&self) -> Vec<&dyn ComponentProver<SimdBackend>> {
        vec![&self.input, &self.output, &self.memory, &self.instruction, &self.processor]
    }

    /// Returns the `Component` of each components, used by the verifier.
    pub fn components(&self) -> Vec<&dyn Component> {
        self.provers().into_iter().map(|component| component as &dyn Component).collect()
    }
}

/// `LOG_MAX_ROWS = ilog2(MAX_ROWS)`
///
/// Means that the ZK-VM does not accept programs with more than 2^20 steps (1M steps).
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
const IS_FIRST_LOG_SIZES: [u32; 9] = [15, 13, 10, 9, 8, 7, 6, 5, 4];

/// Generate a STARK proof of the given Brainfuck program execution.
///
/// # Arguments
/// * `inputs` - The [`Machine`] struct after the program execution
/// The inputs contains the program, the memory, the I/O and the trace.
pub fn prove_brainfuck(
    inputs: &Machine,
) -> Result<BrainfuckProof<Blake2sMerkleHasher>, ProvingError> {
    // ┌──────────────────────────┐
    // │     Protocol Setup       │
    // └──────────────────────────┘

    let config = PcsConfig::default();
    let twiddles = SimdBackend::precompute_twiddles(
        CanonicCoset::new(LOG_MAX_ROWS + config.fri_config.log_blowup_factor + 2)
            .circle_domain()
            .half_coset,
    );
    let channel = &mut Blake2sChannel::default();
    let commitment_scheme =
        &mut CommitmentSchemeProver::<_, Blake2sMerkleChannel>::new(config, &twiddles);

    // ┌───────────────────────────────────────────────┐
    // │   Interaction Phase 0 - Preprocessed Trace    │
    // └───────────────────────────────────────────────┘

    // Generate all preprocessed columns
    let mut tree_builder = commitment_scheme.tree_builder();

    tree_builder.extend_evals(IS_FIRST_LOG_SIZES.iter().copied().map(gen_is_first::<SimdBackend>));

    // Commit the preprocessed trace
    tree_builder.commit(channel);

    // ┌───────────────────────────────────────┐
    // │    Interaction Phase 1 - Main Trace   │
    // └───────────────────────────────────────┘

    let mut tree_builder = commitment_scheme.tree_builder();

    let vm_trace = inputs.trace();
    let (input_trace, input_claim) = InputTable::from(&vm_trace).trace_evaluation();
    let (output_trace, output_claim) = OutputTable::from(&vm_trace).trace_evaluation();
    let (memory_trace, memory_claim) = MemoryTable::from(&vm_trace).trace_evaluation().unwrap();
    let (instruction_trace, instruction_claim) =
        InstructionTable::from((&vm_trace, inputs.program())).trace_evaluation().unwrap();
    let (processor_trace, processor_claim) =
        ProcessorTable::from(vm_trace).trace_evaluation().unwrap();

    tree_builder.extend_evals(input_trace.clone());
    tree_builder.extend_evals(output_trace.clone());
    tree_builder.extend_evals(memory_trace.clone());
    tree_builder.extend_evals(instruction_trace.clone());
    tree_builder.extend_evals(processor_trace.clone());

    let claim = BrainfuckClaim {
        input: input_claim,
        output: output_claim,
        memory: memory_claim,
        instruction: instruction_claim,
        processor: processor_claim,
    };

    // Mix the claim into the Fiat-Shamir channel.
    claim.mix_into(channel);
    // Commit the main trace.
    tree_builder.commit(channel);

    // ┌───────────────────────────────────────────────┐
    // │    Interaction Phase 2 - Interaction Trace    │
    // └───────────────────────────────────────────────┘

    // Draw interaction elements
    let interaction_elements = BrainfuckInteractionElements::draw(channel);

    // Generate the interaction trace and the BrainfuckInteractionClaim
    let mut tree_builder = commitment_scheme.tree_builder();

    let (input_interaction_trace_eval, input_interaction_claim) =
        io::table::interaction_trace_evaluation(
            &input_trace,
            &interaction_elements.input_lookup_elements,
        )
        .unwrap();

    let (output_interaction_trace_eval, output_interaction_claim) =
        io::table::interaction_trace_evaluation(
            &output_trace,
            &interaction_elements.output_lookup_elements,
        )
        .unwrap();

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

    let (processor_interaction_trace_eval, processor_interaction_claim) =
        processor::table::interaction_trace_evaluation(
            &processor_trace,
            &interaction_elements.input_lookup_elements,
            &interaction_elements.output_lookup_elements,
            &interaction_elements.instruction_lookup_elements,
            &interaction_elements.memory_lookup_elements,
        )
        .unwrap();

    tree_builder.extend_evals(input_interaction_trace_eval);
    tree_builder.extend_evals(output_interaction_trace_eval);
    tree_builder.extend_evals(memory_interaction_trace_eval);
    tree_builder.extend_evals(instruction_interaction_trace_eval);
    tree_builder.extend_evals(processor_interaction_trace_eval);

    let interaction_claim = BrainfuckInteractionClaim {
        input: input_interaction_claim,
        output: output_interaction_claim,
        memory: memory_interaction_claim,
        instruction: instruction_interaction_claim,
        processor: processor_interaction_claim,
    };

    // Mix the interaction claim into the Fiat-Shamir channel.
    interaction_claim.mix_into(channel);
    // Commit the interaction trace.
    tree_builder.commit(channel);

    // ┌──────────────────────────┐
    // │     Proof Generation     │
    // └──────────────────────────┘
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
    // TODO: Implement lookup_sum_valid once the processor component has been implemented.
    // if !lookup_sum_valid(&claim, &interaction_elements, &interaction_claim) {
    //     return Err(VerificationError::InvalidLookup("Invalid LogUp sum".to_string()));
    // };
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
    use brainfuck_vm::{compiler::Compiler, test_helper::create_test_machine};

    use super::{prove_brainfuck, verify_brainfuck};

    #[test]
    fn test_proof_cpu() {
        // Get an execution trace from a valid Brainfuck program
        let code = "+>,.";
        let mut compiler = Compiler::new(code);
        let instructions = compiler.compile();
        let (mut machine, _) = create_test_machine(&instructions, &[1]);
        let () = machine.execute().expect("Failed to execute machine");

        let brainfuck_proof = prove_brainfuck(&machine).unwrap();

        verify_brainfuck(brainfuck_proof).unwrap();
    }

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
    fn test_proof_no_input() {
        // Get an execution trace from a valid Brainfuck program
        let code = "+++><[>+<-]";
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
}
