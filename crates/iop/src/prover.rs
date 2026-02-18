use ark_ff::PrimeField;
use tiling::systems::TilingSystem;

use crate::fold::fold_supertile;
use crate::merkle::MerkleTree;
use crate::transcript::Transcript;
use crate::types::{
    ChildOpening, LevelCommitment, QueryResponse, TilingCommitment, TilingHierarchy, TilingProof,
};

/// Generate a tiling IOP proof for a committed hierarchy.
///
/// The hierarchy must have level-0 values already filled in by the prover.
/// This function:
/// 1. Commits each level via Merkle tree
/// 2. Folds values upward using Fiat-Shamir challenges
/// 3. Opens queried supertiles and their children
pub fn prove<F: PrimeField>(
    hierarchy: &mut TilingHierarchy<F>,
    num_queries: usize,
    system: &dyn TilingSystem,
) -> TilingProof<F> {
    let depth = hierarchy.depth;
    let num_types = system.num_types();

    // Build Merkle tree for level 0 (base values already filled)
    let mut trees: Vec<MerkleTree> = Vec::with_capacity(depth + 1);
    let mut level_commitments: Vec<LevelCommitment> = Vec::with_capacity(depth + 1);

    let leaves_0: Vec<_> = hierarchy.levels[0]
        .tile_types
        .iter()
        .zip(hierarchy.levels[0].values.iter())
        .map(|(t, v)| (*t, *v))
        .collect();
    let tree_0 = MerkleTree::build(&leaves_0);
    level_commitments.push(LevelCommitment {
        root: tree_0.root(),
        num_leaves: tree_0.num_leaves(),
        level: 0,
    });
    trees.push(tree_0);

    let mut transcript = Transcript::new(b"tiling-iop-proof");
    let mut challenges = Vec::with_capacity(depth);

    // For each level k (from 1 to depth): absorb previous commitment,
    // squeeze challenge, compute folded values, commit
    for k in 1..=depth {
        // Absorb previous level's commitment
        transcript.absorb_commitment(&level_commitments[k - 1].root);

        // Squeeze folding challenge for this round
        let challenge = transcript.squeeze_challenge(num_types);

        // Compute folded values at level k
        let parent = &hierarchy.levels[k];
        let child_level = &hierarchy.levels[k - 1];

        let mut folded_values: Vec<F> = Vec::with_capacity(parent.tile_types.len());
        for refs in &parent.children {
            let child_pairs: Vec<_> = refs
                .iter()
                .map(|r| (r.child_type, child_level.values[r.child_index]))
                .collect();
            folded_values.push(fold_supertile(&child_pairs, &challenge));
        }

        // Store folded values
        hierarchy.levels[k].values = folded_values;

        // Build Merkle tree for this level
        let leaves_k: Vec<_> = hierarchy.levels[k]
            .tile_types
            .iter()
            .zip(hierarchy.levels[k].values.iter())
            .map(|(t, v)| (*t, *v))
            .collect();
        let tree_k = MerkleTree::build(&leaves_k);
        level_commitments.push(LevelCommitment {
            root: tree_k.root(),
            num_leaves: tree_k.num_leaves(),
            level: k,
        });
        trees.push(tree_k);

        challenges.push(challenge);
    }

    // Absorb final commitment and squeeze query indices
    transcript.absorb_commitment(&level_commitments[depth].root);

    // Generate query responses
    let mut all_queries = Vec::with_capacity(depth);

    for k in (1..=depth).rev() {
        let parent_level = &hierarchy.levels[k];
        let child_level = &hierarchy.levels[k - 1];
        let num_parents = parent_level.tile_types.len();

        let mut round_queries = Vec::with_capacity(num_queries);

        for _ in 0..num_queries {
            let supertile_index = transcript.squeeze_query_index(num_parents);

            // Open the supertile in its level's Merkle tree
            let supertile_proof = trees[k].open(supertile_index);

            // Open all children in the child level's Merkle tree
            let refs = &parent_level.children[supertile_index];
            let child_openings: Vec<_> = refs
                .iter()
                .map(|r| ChildOpening {
                    child_index: r.child_index,
                    child_type: r.child_type,
                    value: child_level.values[r.child_index],
                    proof: trees[k - 1].open(r.child_index),
                })
                .collect();

            round_queries.push(QueryResponse {
                level: k,
                supertile_index,
                supertile_type: parent_level.tile_types[supertile_index],
                supertile_value: parent_level.values[supertile_index],
                supertile_proof,
                children: child_openings,
            });
        }

        all_queries.push(round_queries);
    }

    let final_values = hierarchy.levels[depth].values.clone();
    let composition = system.composition().iter().map(|v| v.clone()).collect();

    TilingProof {
        commitment: TilingCommitment {
            level_commitments,
            depth,
        },
        challenges,
        queries: all_queries,
        final_values,
        composition,
    }
}
