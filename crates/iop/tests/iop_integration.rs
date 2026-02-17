use ark_bls12_381::Fr;
use ark_ff::{AdditiveGroup, Field};

use iop::hierarchy::build_hierarchy;
use iop::merkle::MerkleTree;
use iop::prover::prove;
use iop::transcript::Transcript;
use iop::types::FoldingChallenge;
use iop::verifier::verify;
use tiling::metatile::MetatileType;

/// Fill level-0 with random-looking deterministic values.
fn fill_base_values(hierarchy: &mut iop::types::TilingHierarchy<Fr>) {
    let n = hierarchy.levels[0].values.len();
    for i in 0..n {
        hierarchy.levels[0].values[i] = Fr::from((i as u64 + 1) * 7 + 13);
    }
}

#[test]
fn honest_prover_accepted() {
    let mut hierarchy = build_hierarchy::<Fr>(MetatileType::H, 3);
    fill_base_values(&mut hierarchy);
    let proof = prove(&mut hierarchy, 8);
    assert!(verify(&proof).is_ok(), "honest proof should verify");
}

#[test]
fn honest_prover_depth_1() {
    let mut hierarchy = build_hierarchy::<Fr>(MetatileType::H, 1);
    fill_base_values(&mut hierarchy);
    let proof = prove(&mut hierarchy, 4);
    assert!(verify(&proof).is_ok());
}

#[test]
fn honest_prover_depth_4() {
    let mut hierarchy = build_hierarchy::<Fr>(MetatileType::H, 4);
    fill_base_values(&mut hierarchy);
    let proof = prove(&mut hierarchy, 8);
    assert!(verify(&proof).is_ok());
}

#[test]
fn honest_prover_different_seeds() {
    for seed in MetatileType::all() {
        let mut hierarchy = build_hierarchy::<Fr>(seed, 2);
        fill_base_values(&mut hierarchy);
        let proof = prove(&mut hierarchy, 4);
        assert!(
            verify(&proof).is_ok(),
            "honest proof with seed {:?} should verify",
            seed
        );
    }
}

#[test]
fn tampered_value_rejected() {
    let mut hierarchy = build_hierarchy::<Fr>(MetatileType::H, 3);
    fill_base_values(&mut hierarchy);
    let mut proof = prove(&mut hierarchy, 8);

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
    let mut hierarchy = build_hierarchy::<Fr>(MetatileType::H, 3);
    fill_base_values(&mut hierarchy);
    let mut proof = prove(&mut hierarchy, 8);

    // Change a child's type to break composition
    if let Some(first_round) = proof.queries.first_mut() {
        if let Some(first_query) = first_round.first_mut() {
            if let Some(child) = first_query.children.first_mut() {
                // Flip the type
                child.child_type = match child.child_type {
                    MetatileType::H => MetatileType::T,
                    MetatileType::T => MetatileType::H,
                    MetatileType::P => MetatileType::F,
                    MetatileType::F => MetatileType::P,
                };
            }
        }
    }

    let result = verify(&proof);
    assert!(result.is_err(), "wrong composition should be rejected");
}

#[test]
fn hierarchy_counts_match_matrix() {
    use analysis::spectral::hat_substitution_matrix;

    let depth = 4;
    let hierarchy = build_hierarchy::<Fr>(MetatileType::H, depth);
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
        for t in &level.tile_types {
            actual[t.index()] += Fr::ONE;
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
        let c: FoldingChallenge<Fr> = t.squeeze_challenge();
        let idx = t.squeeze_query_index(100);
        (c, idx)
    };

    let (c1, i1) = squeeze();
    let (c2, i2) = squeeze();

    assert_eq!(c1.r_h, c2.r_h);
    assert_eq!(c1.r_t, c2.r_t);
    assert_eq!(c1.r_p, c2.r_p);
    assert_eq!(c1.r_f, c2.r_f);
    assert_eq!(i1, i2);
}

#[test]
fn merkle_openings_verify() {
    let leaves: Vec<_> = (0..20)
        .map(|i| {
            let t = MetatileType::all()[i % 4];
            (t, Fr::from((i * 17 + 3) as u64))
        })
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
