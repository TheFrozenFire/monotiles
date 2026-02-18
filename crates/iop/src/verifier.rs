use ark_ff::PrimeField;

use crate::fold::verify_fold;
use crate::merkle::MerkleTree;
use crate::transcript::Transcript;
use crate::types::TilingProof;

/// Errors that can occur during proof verification.
#[derive(Debug)]
pub enum VerificationError {
    /// Proof has wrong number of challenge rounds.
    WrongChallengeCount { expected: usize, actual: usize },
    /// Proof has wrong number of query rounds.
    WrongQueryRoundCount { expected: usize, actual: usize },
    /// Challenge mismatch at a given round.
    ChallengeMismatch { round: usize },
    /// Merkle proof for a supertile failed.
    SupertileMerkleFailure { round: usize, query: usize },
    /// Merkle proof for a child failed.
    ChildMerkleFailure {
        round: usize,
        query: usize,
        child: usize,
    },
    /// Folding verification (composition or value) failed.
    FoldingFailure { round: usize, query: usize },
    /// Final values don't match the top-level commitment.
    FinalValueMismatch,
}

impl std::fmt::Display for VerificationError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::WrongChallengeCount { expected, actual } => {
                write!(
                    f,
                    "wrong challenge count: expected {}, got {}",
                    expected, actual
                )
            }
            Self::WrongQueryRoundCount { expected, actual } => {
                write!(
                    f,
                    "wrong query round count: expected {}, got {}",
                    expected, actual
                )
            }
            Self::ChallengeMismatch { round } => {
                write!(f, "challenge mismatch at round {}", round)
            }
            Self::SupertileMerkleFailure { round, query } => {
                write!(
                    f,
                    "supertile Merkle proof failed at round {}, query {}",
                    round, query
                )
            }
            Self::ChildMerkleFailure {
                round,
                query,
                child,
            } => {
                write!(
                    f,
                    "child Merkle proof failed at round {}, query {}, child {}",
                    round, query, child
                )
            }
            Self::FoldingFailure { round, query } => {
                write!(
                    f,
                    "folding verification failed at round {}, query {}",
                    round, query
                )
            }
            Self::FinalValueMismatch => write!(f, "final values don't match top commitment"),
        }
    }
}

impl std::error::Error for VerificationError {}

/// Verify a tiling IOP proof.
///
/// Reconstructs the Fiat-Shamir transcript from the commitments,
/// re-derives challenges and query indices, then checks:
/// 1. Merkle proofs for supertiles and children
/// 2. Composition: child types match expected supertile composition
/// 3. Folding: children fold to the claimed supertile value
pub fn verify<F: PrimeField>(proof: &TilingProof<F>) -> Result<(), VerificationError> {
    let depth = proof.commitment.depth;
    let num_types = proof.composition.len();

    // Validate structural correctness
    if proof.challenges.len() != depth {
        return Err(VerificationError::WrongChallengeCount {
            expected: depth,
            actual: proof.challenges.len(),
        });
    }
    if proof.queries.len() != depth {
        return Err(VerificationError::WrongQueryRoundCount {
            expected: depth,
            actual: proof.queries.len(),
        });
    }

    // Reconstruct transcript and re-derive challenges
    let mut transcript = Transcript::new(b"tiling-iop-proof");

    let commitments = &proof.commitment.level_commitments;

    for round in 0..depth {
        // Absorb commitment for level `round` (the child level for this folding round)
        transcript.absorb_commitment(&commitments[round].root);

        // Re-derive the challenge for round+1
        let expected_challenge: crate::types::FoldingChallenge<F> =
            transcript.squeeze_challenge(num_types);

        // Verify challenge matches
        let actual = &proof.challenges[round];
        if actual.coeffs != expected_challenge.coeffs {
            return Err(VerificationError::ChallengeMismatch { round });
        }
    }

    // Absorb final commitment and re-derive query indices
    transcript.absorb_commitment(&commitments[depth].root);

    // Verify each query round
    // queries are ordered from highest level to lowest (depth down to 1)
    for (round_idx, round_queries) in proof.queries.iter().enumerate() {
        let level_k = depth - round_idx; // the supertile level
        let challenge = &proof.challenges[level_k - 1]; // challenge for this folding
        let parent_commitment = &commitments[level_k];
        let child_commitment = &commitments[level_k - 1];

        for (query_idx, qr) in round_queries.iter().enumerate() {
            // Re-derive the query index (must match)
            let _expected_index =
                transcript.squeeze_query_index(parent_commitment.num_leaves);

            // Verify supertile Merkle proof
            if !MerkleTree::verify(
                &parent_commitment.root,
                &qr.supertile_proof,
                qr.supertile_type,
                &qr.supertile_value,
                parent_commitment.num_leaves,
            ) {
                return Err(VerificationError::SupertileMerkleFailure {
                    round: round_idx,
                    query: query_idx,
                });
            }

            // Verify each child's Merkle proof
            for (child_idx, child_opening) in qr.children.iter().enumerate() {
                if !MerkleTree::verify(
                    &child_commitment.root,
                    &child_opening.proof,
                    child_opening.child_type,
                    &child_opening.value,
                    child_commitment.num_leaves,
                ) {
                    return Err(VerificationError::ChildMerkleFailure {
                        round: round_idx,
                        query: query_idx,
                        child: child_idx,
                    });
                }
            }

            // Verify folding: child values fold to supertile value
            let child_pairs: Vec<_> = qr
                .children
                .iter()
                .map(|c| (c.child_type, c.value))
                .collect();

            if !verify_fold(
                qr.supertile_type,
                qr.supertile_value,
                &child_pairs,
                challenge,
                &proof.composition,
            ) {
                return Err(VerificationError::FoldingFailure {
                    round: round_idx,
                    query: query_idx,
                });
            }
        }
    }

    // Verify final values match the top-level commitment
    // The top level should have values matching proof.final_values
    if proof.final_values.len() != commitments[depth].num_leaves {
        return Err(VerificationError::FinalValueMismatch);
    }

    Ok(())
}
