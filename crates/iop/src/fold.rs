use ark_ff::Field;

use crate::types::FoldingChallenge;

/// Fold children's values into a supertile value using type-stratified random challenges.
///
/// For each child, multiplies its value by the challenge coefficient for its type,
/// then sums all contributions.
pub fn fold_supertile<F: Field>(
    children: &[(usize, F)],
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
    supertile_type: usize,
    supertile_value: F,
    children: &[(usize, F)],
    challenge: &FoldingChallenge<F>,
    composition: &[Vec<usize>],
) -> bool {
    // Check composition
    let expected_counts = &composition[supertile_type];
    let num_types = composition.len();

    let mut actual_counts = vec![0usize; num_types];
    for (t, _) in children {
        actual_counts[*t] += 1;
    }

    if &actual_counts != expected_counts {
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
            coeffs: vec![
                Fr::from(2u64), // H (type 0)
                Fr::from(3u64), // T (type 1)
                Fr::from(5u64), // P (type 2)
                Fr::from(7u64), // F (type 3)
            ],
        }
    }

    // Hat system composition: H'=[3,1,3,3], T'=[1,0,0,0], P'=[2,0,1,2], F'=[2,0,1,3]
    fn hat_composition() -> Vec<Vec<usize>> {
        vec![
            vec![3, 1, 3, 3],
            vec![1, 0, 0, 0],
            vec![2, 0, 1, 2],
            vec![2, 0, 1, 3],
        ]
    }

    #[test]
    fn fold_single_child() {
        let challenge = test_challenge();
        let children = vec![(0usize, Fr::from(10u64))];
        let result = fold_supertile(&children, &challenge);
        // r_h * 10 = 2 * 10 = 20
        assert_eq!(result, Fr::from(20u64));
    }

    #[test]
    fn fold_t_supertile() {
        // T' has exactly 1 H child
        let challenge = test_challenge();
        let children = vec![(0usize, Fr::from(10u64))];

        let folded = fold_supertile(&children, &challenge);
        assert!(verify_fold(1usize, folded, &children, &challenge, &hat_composition()));
    }

    #[test]
    fn verify_fold_wrong_value_rejected() {
        let challenge = test_challenge();
        let children = vec![(0usize, Fr::from(10u64))];
        let folded = fold_supertile(&children, &challenge);
        let wrong = folded + Fr::from(1u64);

        assert!(!verify_fold(1usize, wrong, &children, &challenge, &hat_composition()));
    }

    #[test]
    fn verify_fold_wrong_composition_rejected() {
        let challenge = test_challenge();
        // H' needs 3H + 1T + 3P + 3F, but we provide only 1H
        let children = vec![(0usize, Fr::from(10u64))];
        let folded = fold_supertile(&children, &challenge);

        assert!(!verify_fold(0usize, folded, &children, &challenge, &hat_composition()));
    }

    #[test]
    fn fold_h_supertile_composition() {
        let challenge = test_challenge();
        // H' = 3H + 1T + 3P + 3F (10 children)
        let children: Vec<(usize, Fr)> = vec![
            (0, Fr::from(1u64)),
            (0, Fr::from(2u64)),
            (0, Fr::from(3u64)),
            (1, Fr::from(4u64)),
            (2, Fr::from(5u64)),
            (2, Fr::from(6u64)),
            (2, Fr::from(7u64)),
            (3, Fr::from(8u64)),
            (3, Fr::from(9u64)),
            (3, Fr::from(10u64)),
        ];

        let folded = fold_supertile(&children, &challenge);
        // 2*(1+2+3) + 3*4 + 5*(5+6+7) + 7*(8+9+10)
        // = 12 + 12 + 90 + 189 = 303
        assert_eq!(folded, Fr::from(303u64));
        assert!(verify_fold(0usize, folded, &children, &challenge, &hat_composition()));
    }
}
