use stwo_prover::core::{
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
pub struct BrainfuckClaim;

impl BrainfuckClaim {
    pub fn mix_into(&self, _channel: &mut impl Channel) {
        todo!();
    }

    pub fn log_sizes(&self) -> TreeVec<Vec<u32>> {
        todo!();
    }
}

/// All the interaction elements (drawn from the channel)
/// required by the various components during the interaction phase.
pub struct BrainfuckInteractionElements;

impl BrainfuckInteractionElements {
    pub fn draw(_channel: &mut impl Channel) -> Self {
        todo!();
    }
}

/// All the claims from the second phase (interaction phase 1).
///
/// Mainly the claims on global relations (lookup, permutation, evaluation).
pub struct BrainfuckInteractionClaim;

impl BrainfuckInteractionClaim {
    pub fn mix_into(&self, _channel: &mut impl Channel) {
        todo!();
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
pub struct BrainfuckComponents;

impl BrainfuckComponents {
    /// Initializes all the Brainfuck components from the claims generated from the trace.
    pub fn new(
        _claim: &BrainfuckClaim,
        _interaction_elements: &BrainfuckInteractionElements,
        _interaction_claim: &BrainfuckInteractionClaim,
    ) -> Self {
        todo!();
    }

    /// Returns the `ComponentProver` of each components, used by the prover.
    pub fn provers(&self) -> Vec<&dyn ComponentProver<SimdBackend>> {
        todo!();
    }

    /// Returns the `Component` of each components, used by the verifier.
    pub fn components(&self) -> Vec<&dyn Component> {
        todo!();
    }
}

/// `LOG_MAX_ROWS = log2(MAX_ROWS)` ?
///
/// Means that the ZK-VM does not accept programs with more than 2^20 steps (1M steps).
const LOG_MAX_ROWS: u32 = 20;

pub fn prove_brainfuck() -> Result<BrainfuckProof<Blake2sMerkleHasher>, ProvingError> {
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
    let tree_builder = commitment_scheme.tree_builder();

    // ┌──────────────────────────┐
    // │   Interaction Phase 0    │
    // └──────────────────────────┘

    // Generate BrainfuckClaim (from the execution trace provided by brainfuck_vm)

    // Commit to the claim and the trace.
    let claim = BrainfuckClaim {};
    claim.mix_into(channel);
    tree_builder.commit(channel);

    // ┌──────────────────────────┐
    // │   Interaction Phase 1    │
    // └──────────────────────────┘

    // Draw interaction elements
    let interaction_elements = BrainfuckInteractionElements::draw(channel);

    // Generate the interaction trace and the BrainfuckInteractionClaim
    let tree_builder = commitment_scheme.tree_builder();

    let interaction_claim = BrainfuckInteractionClaim {};
    interaction_claim.mix_into(channel);
    tree_builder.commit(channel);

    // ┌──────────────────────────┐
    // │   Interaction Phase 2    │
    // └──────────────────────────┘

    // Generate constant columns (e.g. is_first)
    let tree_builder = commitment_scheme.tree_builder();
    tree_builder.commit(channel);

    // ┌──────────────────────────┐
    // │     Proof Generation     │
    // └──────────────────────────┘
    let component_builder =
        BrainfuckComponents::new(&claim, &interaction_elements, &interaction_claim);
    let components = component_builder.provers();
    let _proof = prover::prove::<SimdBackend, _>(&components, channel, commitment_scheme)?;

    // Ok(BrainfuckProof { claim, interaction_claim, proof })
    todo!();
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
    let sizes = &claim.log_sizes();

    // ┌──────────────────────────┐
    // │   Interaction Phase 0    │
    // └──────────────────────────┘
    claim.mix_into(channel);
    commitment_scheme_verifier.commit(proof.commitments[0], &sizes[0], channel);

    // ┌──────────────────────────┐
    // │   Interaction Phase 1    │
    // └──────────────────────────┘
    let interaction_elements = BrainfuckInteractionElements::draw(channel);
    // Check that the lookup sum is valid, otherwise throw
    // TODO: panic! should be replaced by custom error
    if !lookup_sum_valid(&claim, &interaction_elements, &interaction_claim) {
        panic!();
    }
    interaction_claim.mix_into(channel);
    commitment_scheme_verifier.commit(proof.commitments[1], &sizes[1], channel);

    // ┌──────────────────────────┐
    // │   Interaction Phase 2    │
    // └──────────────────────────┘
    commitment_scheme_verifier.commit(proof.commitments[2], &sizes[2], channel);

    // ┌──────────────────────────┐
    // │    Proof Verification    │
    // └──────────────────────────┘

    let component_builder =
        BrainfuckComponents::new(&claim, &interaction_elements, &interaction_claim);
    let components = component_builder.components();

    verify(&components, channel, commitment_scheme_verifier, proof)
}
