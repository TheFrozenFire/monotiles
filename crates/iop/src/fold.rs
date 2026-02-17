use ark_ff::Field;
use tiling::metatile::{supertile_composition, MetatileType};

use crate::types::FoldingChallenge;

/// Fold children's values into a supertile value using type-stratified random challenges.
///
/// For each child, multiplies its value by the challenge coefficient for its type,
/// then sums all contributions.
pub fn fold_supertile<F: Field>(
    children: &[(MetatileType, F)],
    challenge: &FoldingChallenge<F>,
) -> F {
    children
        .iter()
        .map(|(t, v)| challenge.for_type(*t) * *v)
        .sum()
}

/// Verify that a supertile's folded value is consistent with its children.
///
/// Checks two things:
/// 1. Composition: the child type counts match the expected supertile composition
/// 2. Folding: fold(children, challenge) == supertile_value
pub fn verify_fold<F: Field>(
    supertile_type: MetatileType,
    supertile_value: F,
    children: &[(MetatileType, F)],
    challenge: &FoldingChallenge<F>,
) -> bool {
    // Check composition
    let expected = supertile_composition();
    let expected_counts = expected[supertile_type.index()];

    let mut actual_counts = [0usize; 4];
    for (t, _) in children {
        actual_counts[t.index()] += 1;
    }

    if actual_counts != expected_counts {
        return false;
    }

    // Check folding
    let computed = fold_supertile(children, challenge);
    computed == supertile_value
}

#[cfg(test)]
mod tests {
    use super::*;
    use ark_bls12_381::Fr;

    fn test_challenge() -> FoldingChallenge<Fr> {
        FoldingChallenge {
            r_h: Fr::from(2u64),
            r_t: Fr::from(3u64),
            r_p: Fr::from(5u64),
            r_f: Fr::from(7u64),
        }
    }

    #[test]
    fn fold_single_child() {
        let challenge = test_challenge();
        let children = vec![(MetatileType::H, Fr::from(10u64))];
        let result = fold_supertile(&children, &challenge);
        // r_h * 10 = 2 * 10 = 20
        assert_eq!(result, Fr::from(20u64));
    }

    #[test]
    fn fold_t_supertile() {
        // T' has exactly 1 H child
        let challenge = test_challenge();
        let children = vec![(MetatileType::H, Fr::from(10u64))];

        let folded = fold_supertile(&children, &challenge);
        assert!(verify_fold(MetatileType::T, folded, &children, &challenge));
    }

    #[test]
    fn verify_fold_wrong_value_rejected() {
        let challenge = test_challenge();
        let children = vec![(MetatileType::H, Fr::from(10u64))];
        let folded = fold_supertile(&children, &challenge);
        let wrong = folded + Fr::from(1u64);

        assert!(!verify_fold(MetatileType::T, wrong, &children, &challenge));
    }

    #[test]
    fn verify_fold_wrong_composition_rejected() {
        let challenge = test_challenge();
        // H' needs 3H + 1T + 3P + 3F, but we provide only 1H
        let children = vec![(MetatileType::H, Fr::from(10u64))];
        let folded = fold_supertile(&children, &challenge);

        assert!(!verify_fold(MetatileType::H, folded, &children, &challenge));
    }

    #[test]
    fn fold_h_supertile_composition() {
        let challenge = test_challenge();
        // H' = 3H + 1T + 3P + 3F (10 children)
        let children: Vec<(MetatileType, Fr)> = vec![
            (MetatileType::H, Fr::from(1u64)),
            (MetatileType::H, Fr::from(2u64)),
            (MetatileType::H, Fr::from(3u64)),
            (MetatileType::T, Fr::from(4u64)),
            (MetatileType::P, Fr::from(5u64)),
            (MetatileType::P, Fr::from(6u64)),
            (MetatileType::P, Fr::from(7u64)),
            (MetatileType::F, Fr::from(8u64)),
            (MetatileType::F, Fr::from(9u64)),
            (MetatileType::F, Fr::from(10u64)),
        ];

        let folded = fold_supertile(&children, &challenge);
        // 2*(1+2+3) + 3*4 + 5*(5+6+7) + 7*(8+9+10)
        // = 12 + 12 + 90 + 189 = 303
        assert_eq!(folded, Fr::from(303u64));
        assert!(verify_fold(MetatileType::H, folded, &children, &challenge));
    }
}
