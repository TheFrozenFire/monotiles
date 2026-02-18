use ark_bls12_381::Fr;
use ark_ff::{AdditiveGroup, Field};
use iop::types::TilingHierarchy;

use iop::hierarchy::build_hierarchy_system;
use iop::merkle::MerkleTree;
use iop::prover::prove;
use iop::transcript::Transcript;
use iop::types::FoldingChallenge;
use iop::verifier::verify;
use tiling::systems::hat::HatSystem;
use tiling::systems::spectre::SpectreSystem;
use tiling::systems::TilingSystem;

/// Fill level-0 with random-looking deterministic values.
fn fill_base_values(hierarchy: &mut iop::types::TilingHierarchy<Fr>) {
    let n = hierarchy.levels[0].values.len();
    for i in 0..n {
        hierarchy.levels[0].values[i] = Fr::from((i as u64 + 1) * 7 + 13);
    }
}

#[test]
fn honest_prover_accepted() {
    let hat = HatSystem::new();
    let mut hierarchy = build_hierarchy_system::<Fr>(&hat, 0, 3);
    fill_base_values(&mut hierarchy);
    let proof = prove(&mut hierarchy, 8, &hat);
    assert!(verify(&proof).is_ok(), "honest proof should verify");
}

#[test]
fn honest_prover_depth_1() {
    let hat = HatSystem::new();
    let mut hierarchy = build_hierarchy_system::<Fr>(&hat, 0, 1);
    fill_base_values(&mut hierarchy);
    let proof = prove(&mut hierarchy, 4, &hat);
    assert!(verify(&proof).is_ok());
}

#[test]
fn honest_prover_depth_4() {
    let hat = HatSystem::new();
    let mut hierarchy = build_hierarchy_system::<Fr>(&hat, 0, 4);
    fill_base_values(&mut hierarchy);
    let proof = prove(&mut hierarchy, 8, &hat);
    assert!(verify(&proof).is_ok());
}

#[test]
fn honest_prover_different_seeds() {
    let hat = HatSystem::new();
    for seed in 0..hat.num_types() {
        let mut hierarchy = build_hierarchy_system::<Fr>(&hat, seed, 2);
        fill_base_values(&mut hierarchy);
        let proof = prove(&mut hierarchy, 4, &hat);
        assert!(
            verify(&proof).is_ok(),
            "honest proof with seed {} should verify",
            hat.type_name(seed)
        );
    }
}

#[test]
fn tampered_value_rejected() {
    let hat = HatSystem::new();
    let mut hierarchy = build_hierarchy_system::<Fr>(&hat, 0, 3);
    fill_base_values(&mut hierarchy);
    let mut proof = prove(&mut hierarchy, 8, &hat);

    // Tamper with a child value in the first query of the first round
    if let Some(first_round) = proof.queries.first_mut() {
        if let Some(first_query) = first_round.first_mut() {
            if let Some(child) = first_query.children.first_mut() {
                child.value += Fr::from(1u64);
            }
        }
    }

    let result = verify(&proof);
    assert!(result.is_err(), "tampered proof should be rejected");
}

#[test]
fn wrong_composition_rejected() {
    let hat = HatSystem::new();
    let mut hierarchy = build_hierarchy_system::<Fr>(&hat, 0, 3);
    fill_base_values(&mut hierarchy);
    let mut proof = prove(&mut hierarchy, 8, &hat);

    // Change a child's type to break composition
    if let Some(first_round) = proof.queries.first_mut() {
        if let Some(first_query) = first_round.first_mut() {
            if let Some(child) = first_query.children.first_mut() {
                // Flip the type (cycle through 0..4)
                child.child_type = (child.child_type + 1) % hat.num_types();
            }
        }
    }

    let result = verify(&proof);
    assert!(result.is_err(), "wrong composition should be rejected");
}

#[test]
fn spectre_honest_prover_accepted() {
    let spectre = SpectreSystem::new();
    let mut hierarchy = build_hierarchy_system::<Fr>(&spectre, 0, 3);
    fill_base_values(&mut hierarchy);
    let proof = prove(&mut hierarchy, 8, &spectre);
    assert!(verify(&proof).is_ok(), "honest spectre proof should verify");
}

#[test]
fn hierarchy_counts_match_matrix() {
    use analysis::spectral::hat_substitution_matrix;

    let hat = HatSystem::new();
    let depth = 4;
    let hierarchy = build_hierarchy_system::<Fr>(&hat, 0, depth);
    let m = hat_substitution_matrix::<Fr>();

    // Seed vector: [1, 0, 0, 0] for H
    let seed_vec = vec![Fr::from(1u64), Fr::ZERO, Fr::ZERO, Fr::ZERO];

    for level in &hierarchy.levels {
        let k = level.level;
        // Hierarchy level k corresponds to (depth - k) substitutions from seed
        let substitution_level = depth - k;

        // Expected counts = seed_vec * M^k (row vector multiplication)
        let m_power = m.pow(substitution_level as u64);
        let expected: Vec<Fr> = (0..4)
            .map(|j| {
                (0..4)
                    .map(|i| seed_vec[i] * m_power[(i, j)])
                    .sum::<Fr>()
            })
            .collect();

        let mut actual = [Fr::ZERO; 4];
        for &t in &level.tile_types {
            actual[t] += Fr::ONE;
        }

        for j in 0..4 {
            assert_eq!(
                actual[j], expected[j],
                "type {} count mismatch at hierarchy level {} (substitution level {})",
                j, k, substitution_level
            );
        }
    }
}

#[test]
fn fiat_shamir_deterministic() {
    let root = [0x42u8; 32];

    let squeeze = || {
        let mut t = Transcript::new(b"determinism-test");
        t.absorb_commitment(&root);
        let c: FoldingChallenge<Fr> = t.squeeze_challenge(4);
        let idx = t.squeeze_query_index(100);
        (c, idx)
    };

    let (c1, i1) = squeeze();
    let (c2, i2) = squeeze();

    assert_eq!(c1.coeffs, c2.coeffs);
    assert_eq!(i1, i2);
}

#[test]
fn merkle_openings_verify() {
    let leaves: Vec<_> = (0..20)
        .map(|i| (i % 4, Fr::from((i * 17 + 3) as u64)))
        .collect();

    let tree = MerkleTree::build(&leaves);
    let root = tree.root();

    for i in 0..20 {
        let proof = tree.open(i);
        assert!(
            MerkleTree::verify(&root, &proof, leaves[i].0, &leaves[i].1, 20),
            "Merkle opening failed for leaf {}",
            i
        );
    }
}

/// Perform a sibling swap on the hierarchy: find the first parent at level `parent_level`
/// that has both a P'-type (type 2) and F'-type (type 3) child, then swap their labels
/// and move one F-type child from F' to P' so both compositions remain valid.
///
/// Returns true if a swap was found and applied.
fn apply_sibling_swap(hierarchy: &mut TilingHierarchy<Fr>, parent_level: usize) -> bool {
    let child_level = parent_level - 1;

    // Find a parent tile whose children include at least one P' (type 2) and one F' (type 3)
    let num_parents = hierarchy.levels[parent_level].tile_types.len();
    let mut swap_target: Option<(usize, usize)> = None; // (A_idx in child_level, B_idx in child_level)

    'outer: for parent_idx in 0..num_parents {
        let children = &hierarchy.levels[parent_level].children[parent_idx];
        let mut a_idx = None; // first P'-type child index
        let mut b_idx = None; // first F'-type child index

        for cr in children {
            if hierarchy.levels[child_level].tile_types[cr.child_index] == 2 && a_idx.is_none() {
                a_idx = Some(cr.child_index);
            }
            if hierarchy.levels[child_level].tile_types[cr.child_index] == 3 && b_idx.is_none() {
                b_idx = Some(cr.child_index);
            }
            if a_idx.is_some() && b_idx.is_some() {
                swap_target = Some((a_idx.unwrap(), b_idx.unwrap()));
                break 'outer;
            }
        }
    }

    let (a_idx, b_idx) = match swap_target {
        Some(t) => t,
        None => return false,
    };

    // Swap the type labels: A becomes F' (3), B becomes P' (2)
    hierarchy.levels[child_level].tile_types[a_idx] = 3;
    hierarchy.levels[child_level].tile_types[b_idx] = 2;

    // Move one F-type child (from grandchild level) from B's child list to A's child list.
    // Find the index of the first F-type (type 3) ChildRef in B's children.
    let grandchild_level = child_level - 1;
    let b_children = &hierarchy.levels[child_level].children[b_idx];
    let extra_f_pos = b_children
        .iter()
        .position(|cr| hierarchy.levels[grandchild_level].tile_types[cr.child_index] == 3);

    if let Some(pos) = extra_f_pos {
        let extra_cr = hierarchy.levels[child_level].children[b_idx].remove(pos);
        hierarchy.levels[child_level].children[a_idx].push(extra_cr);
    }
    // If grandchild level doesn't exist (child_level == 0), no child to move — swap still valid
    // because at level 0 there are no further children; composition is the tile itself.

    true
}

/// The IOP is blind to sibling swaps: a hierarchy produced by swapping a P'/F' sibling
/// pair (moving 1 F-type child between them) is a different valid hierarchy, and the IOP
/// accepts a fresh proof for it just as readily as it accepts the original.
///
/// This demonstrates that the IOP cannot enforce canonical hierarchy labeling:
/// two distinct hierarchies H and H' (differing only in sibling P'/F' label assignment)
/// both produce valid, accepted proofs.
#[test]
fn iop_accepts_sibling_swapped_hierarchy() {
    let hat = HatSystem::new();

    // Build and prove the original hierarchy H
    let mut hierarchy = build_hierarchy_system::<Fr>(&hat, 0, 3);
    fill_base_values(&mut hierarchy);
    let proof_original = prove(&mut hierarchy, 8, &hat);
    assert!(
        verify(&proof_original).is_ok(),
        "original hierarchy proof must verify"
    );

    // Construct H' by applying a sibling swap at level 2 (parent) → child swap at level 1
    let mut hierarchy_swapped = build_hierarchy_system::<Fr>(&hat, 0, 3);
    fill_base_values(&mut hierarchy_swapped);

    let swapped = apply_sibling_swap(&mut hierarchy_swapped, 2);
    assert!(swapped, "must find a sibling P'/F' pair to swap at level 2");

    // Verify H and H' differ at level 1 (they have different tile type assignments)
    let types_original: Vec<_> = hierarchy.levels[1].tile_types.clone();
    let types_swapped: Vec<_> = hierarchy_swapped.levels[1].tile_types.clone();
    assert_ne!(
        types_original, types_swapped,
        "swapped hierarchy must differ from original at the swapped level"
    );

    // Prove and verify H' — the IOP must accept it
    let proof_swapped = prove(&mut hierarchy_swapped, 8, &hat);
    assert!(
        verify(&proof_swapped).is_ok(),
        "swapped hierarchy proof should also verify: IOP is blind to sibling swaps"
    );
}
