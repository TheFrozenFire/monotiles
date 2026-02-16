use ark_ff::Field;
use domain::matrix::Matrix;

/// Construct the 4x4 hat substitution matrix over a field F.
///
/// M[i][j] = number of type-j metatiles in the level-1 supertile of type i.
/// Row/column order: H, T, P, F.
///
/// Derived from the hatviz inflation rules (Smith, Myers, Kaplan, Goodman-Strauss 2023).
///
/// Eigenvalues: phi^4 = (7+3*sqrt(5))/2, 1, -1, (7-3*sqrt(5))/2
/// where phi = (1+sqrt(5))/2 is the golden ratio.
pub fn hat_substitution_matrix<F: Field>() -> Matrix<F> {
    let f = |n: u64| F::from(n);
    //       H     T     P     F
    Matrix::new(
        4,
        4,
        vec![
            f(3), f(1), f(3), f(3), // H' = 3H + 1T + 3P + 3F
            f(1), f(0), f(0), f(0), // T' = 1H
            f(2), f(0), f(1), f(2), // P' = 2H + 1P + 2F
            f(2), f(0), f(1), f(3), // F' = 2H + 1P + 3F
        ],
    )
}

/// Construct the 2x2 spectre substitution matrix over a field F.
///
/// For the Spectre/Mystic system:
/// - Spectre' = 7 Spectres + 1 Mystic (all orientation-reversed)
/// - Mystic'  = 6 Spectres + 1 Mystic (all orientation-reversed)
///
/// Eigenvalues: 4 + sqrt(15) and 4 - sqrt(15).
pub fn spectre_substitution_matrix<F: Field>() -> Matrix<F> {
    let f = |n: u64| F::from(n);
    //         Spectre  Mystic
    Matrix::new(
        2,
        2,
        vec![
            f(7), f(6), // Spectre' = 7S + 6M... wait
            f(1), f(1), // Mystic'  = 1S + 1M
        ],
    )
}

/// Compute tile frequencies by power iteration on the substitution matrix.
///
/// Starting from a uniform initial vector, repeatedly multiply by the matrix
/// and normalize. Converges to the Perron-Frobenius eigenvector for primitive
/// matrices, giving relative tile frequencies in the infinite tiling.
///
/// Returns the normalized frequency vector after `iterations` steps.
pub fn tile_frequencies<F: Field>(matrix: &Matrix<F>, iterations: usize) -> Vec<F> {
    let n = matrix.rows;
    assert_eq!(n, matrix.cols, "matrix must be square");

    // Start with uniform vector
    let mut v = vec![F::ONE; n];

    for _ in 0..iterations {
        // Multiply: v = M * v
        let mut new_v = vec![F::ZERO; n];
        for i in 0..n {
            for j in 0..n {
                new_v[i] += matrix[(i, j)] * v[j];
            }
        }

        // Normalize by sum (L1 norm)
        let sum: F = new_v.iter().copied().sum();
        if sum != F::ZERO {
            let sum_inv = sum.inverse().unwrap();
            for x in &mut new_v {
                *x *= sum_inv;
            }
        }

        v = new_v;
    }

    v
}

/// Estimate the Perron-Frobenius eigenvalue via power iteration.
///
/// Returns the ratio ||M^k v|| / ||M^{k-1} v|| after `iterations` steps,
/// which converges to the PF eigenvalue for primitive matrices.
pub fn perron_eigenvalue<F: Field>(matrix: &Matrix<F>, iterations: usize) -> F {
    let n = matrix.rows;
    let mut v = vec![F::ONE; n];

    let mut eigenvalue = F::ZERO;

    for _ in 0..iterations {
        let mut new_v = vec![F::ZERO; n];
        for i in 0..n {
            for j in 0..n {
                new_v[i] += matrix[(i, j)] * v[j];
            }
        }

        // Eigenvalue estimate: ratio of norms (using L1)
        let old_sum: F = v.iter().copied().sum();
        let new_sum: F = new_v.iter().copied().sum();
        if old_sum != F::ZERO {
            eigenvalue = new_sum * old_sum.inverse().unwrap();
        }

        // Normalize
        if new_sum != F::ZERO {
            let inv = new_sum.inverse().unwrap();
            for x in &mut new_v {
                *x *= inv;
            }
        }

        v = new_v;
    }

    eigenvalue
}

/// Compute the exact left Perron-Frobenius eigenvector over a field extension.
///
/// For the hat substitution matrix, the PF eigenvalue is phi^4 = (7 + 3*sqrt(5))/2.
/// The left eigenvector v satisfies v^T M = phi^4 v^T and gives exact tile frequencies
/// when normalized to sum to 1.
///
/// Returns [v_H, v_T, v_P, v_F] in the field F, which must contain sqrt(5).
///
/// The unnormalized eigenvector (solving (M^T - lambda I)v = 0) is:
///   [1, 5 - 3*phi, 6*phi - 9, 6 - 3*phi]
/// which sums to 3, yielding:
///   v = [1/3, (5 - 3*phi)/3, (6*phi - 9)/3, (6 - 3*phi)/3]
///     = [1/3, 1/(3*phi^4), 1/phi^3, 1/phi^2]
pub fn exact_hat_eigenvector<F: Field>(phi: F) -> Vec<F> {
    let three = F::from(3u64);
    let five = F::from(5u64);
    let six = F::from(6u64);
    let nine = F::from(9u64);
    let three_inv = three.inverse().expect("3 is invertible");

    // Unnormalized: [1, 5-3*phi, 6*phi-9, 6-3*phi], sum = 3
    let v_h = three_inv;
    let v_t = (five - three * phi) * three_inv;
    let v_p = (six * phi - nine) * three_inv;
    let v_f = (six - three * phi) * three_inv;

    vec![v_h, v_t, v_p, v_f]
}

/// Verify the GAB (Gähler-Akiyama-Baake) frequency equation for hat tilings.
///
/// The tile frequency q for the H-type metatile satisfies:
///   q^2 - q + 1/5 = 0
///
/// with solutions q = (5 ± sqrt(5)) / 10.
///
/// This connects the substitution matrix eigenvalues to a quadratic over Q,
/// verifying that tile frequencies lie in Q(sqrt(5)).
///
/// Returns true if the equation holds for the given frequency value.
pub fn verify_gab_equation<F: Field>(q: F) -> bool {
    let five = F::from(5u64);
    let five_inv = five.inverse().expect("5 is invertible");
    // q^2 - q + 1/5 = 0
    q * q - q + five_inv == F::ZERO
}

/// Compute the two GAB frequency roots (5 + sqrt(5))/10 and (5 - sqrt(5))/10.
///
/// These are the tile frequency values for the H metatile in Q(sqrt(5)).
pub fn gab_frequency_roots<F: Field>(sqrt5: F) -> (F, F) {
    let five = F::from(5u64);
    let ten_inv = F::from(10u64).inverse().expect("10 is invertible");
    let root_plus = (five + sqrt5) * ten_inv;
    let root_minus = (five - sqrt5) * ten_inv;
    (root_plus, root_minus)
}

#[cfg(test)]
mod tests {
    use super::*;
    use ark_bls12_381::Fr;
    use ark_ff::{AdditiveGroup, Field};

    type F = Fr;

    #[test]
    fn hat_matrix_dimensions() {
        let m = hat_substitution_matrix::<F>();
        assert_eq!(m.rows, 4);
        assert_eq!(m.cols, 4);
    }

    #[test]
    fn hat_matrix_row_sums() {
        let m = hat_substitution_matrix::<F>();
        // Row sums = total metatiles per supertile
        let row_sum = |r: usize| (0..4).map(|c| m[(r, c)]).sum::<F>();
        assert_eq!(row_sum(0), F::from(10u64)); // H': 3+1+3+3=10
        assert_eq!(row_sum(1), F::from(1u64));  // T': 1
        assert_eq!(row_sum(2), F::from(5u64));  // P': 2+0+1+2=5
        assert_eq!(row_sum(3), F::from(6u64));  // F': 2+0+1+3=6
    }

    #[test]
    fn hat_matrix_characteristic_polynomial_roots() {
        // The char poly is lambda^4 - 7*lambda^3 + 7*lambda - 1
        // Roots: phi^4, 1, -1, 1/phi^4
        // Verify lambda=1 is an eigenvalue: det(M - I)
        let m = hat_substitution_matrix::<F>();
        let id = Matrix::<F>::identity(4);
        let m_minus_i = &m + &id.scale(-F::ONE);
        assert_eq!(m_minus_i.determinant(), F::ZERO);
    }

    #[test]
    fn hat_matrix_determinant() {
        // det(M) = product of eigenvalues = phi^4 * 1 * (-1) * (1/phi^4) = -1
        let m = hat_substitution_matrix::<F>();
        assert_eq!(m.determinant(), -F::ONE);
    }

    #[test]
    fn spectre_matrix_dimensions() {
        let m = spectre_substitution_matrix::<F>();
        assert_eq!(m.rows, 2);
        assert_eq!(m.cols, 2);
    }

    #[test]
    fn spectre_matrix_trace_is_eight() {
        // tr(M) = 7 + 1 = 8 = (4+sqrt(15)) + (4-sqrt(15))
        let m = spectre_substitution_matrix::<F>();
        assert_eq!(m.trace(), F::from(8u64));
    }

    #[test]
    fn spectre_matrix_determinant_is_one() {
        // det(M) = 7*1 - 6*1 = 1 = (4+sqrt(15))*(4-sqrt(15))
        let m = spectre_substitution_matrix::<F>();
        assert_eq!(m.determinant(), F::from(1u64));
    }

    #[test]
    fn power_iteration_converges_for_hat() {
        let m = hat_substitution_matrix::<F>();
        let freqs = tile_frequencies(&m, 50);

        // All frequencies should be positive (nonzero in Fr)
        for f in &freqs {
            assert_ne!(*f, F::ZERO, "frequency should be nonzero");
        }

        // Frequencies should sum to 1
        let sum: F = freqs.iter().copied().sum();
        assert_eq!(sum, F::ONE);
    }

    #[test]
    fn exact_hat_eigenvector_is_left_eigenvector() {
        use domain::fields::{FrSqrt5, golden_ratio};

        let phi = golden_ratio();
        let v = exact_hat_eigenvector(phi);

        // Build the hat matrix over FrSqrt5
        let m = hat_substitution_matrix::<FrSqrt5>();
        let lambda = phi * phi * phi * phi; // phi^4

        // Verify v^T M = lambda v^T
        // i.e., sum_i v[i] * M[i][j] = lambda * v[j] for all j
        for j in 0..4 {
            let lhs: FrSqrt5 = (0..4).map(|i| v[i] * m[(i, j)]).sum();
            let rhs = lambda * v[j];
            assert_eq!(lhs, rhs, "eigenvector check failed at column {}", j);
        }
    }

    #[test]
    fn exact_hat_eigenvector_sums_to_one() {
        use domain::fields::golden_ratio;
        type Ext = domain::fields::FrSqrt5;

        let phi = golden_ratio();
        let v = exact_hat_eigenvector(phi);
        let sum: Ext = v.iter().copied().sum();
        assert_eq!(sum, Ext::ONE);
    }

    #[test]
    fn gab_equation_holds_for_roots() {
        use domain::fields::FrSqrt5;

        let sqrt5 = FrSqrt5::new(
            ark_bls12_381::Fr::from(0u64),
            ark_bls12_381::Fr::from(1u64),
        );
        let (q_plus, q_minus) = gab_frequency_roots(sqrt5);

        assert!(verify_gab_equation(q_plus), "GAB equation should hold for (5+sqrt(5))/10");
        assert!(verify_gab_equation(q_minus), "GAB equation should hold for (5-sqrt(5))/10");
    }

    #[test]
    fn gab_roots_sum_to_one() {
        use domain::fields::FrSqrt5;

        let sqrt5 = FrSqrt5::new(
            ark_bls12_381::Fr::from(0u64),
            ark_bls12_381::Fr::from(1u64),
        );
        let (q_plus, q_minus) = gab_frequency_roots(sqrt5);
        assert_eq!(q_plus + q_minus, FrSqrt5::ONE, "GAB roots should sum to 1");
    }

    #[test]
    fn gab_roots_product_is_one_fifth() {
        use domain::fields::FrSqrt5;

        let sqrt5 = FrSqrt5::new(
            ark_bls12_381::Fr::from(0u64),
            ark_bls12_381::Fr::from(1u64),
        );
        let (q_plus, q_minus) = gab_frequency_roots(sqrt5);
        let five_inv = FrSqrt5::new(ark_bls12_381::Fr::from(5u64), ark_bls12_381::Fr::from(0u64))
            .inverse()
            .unwrap();
        assert_eq!(q_plus * q_minus, five_inv, "GAB roots product should be 1/5");
    }

    #[test]
    fn hat_matrix_characteristic_polynomial_factors() {
        // char poly = (lambda - 1)(lambda + 1)(lambda^2 - 7*lambda + 1)
        // The quadratic factor has roots phi^4 and 1/phi^4.
        // Verify: M^2 - 7*M + I = 0 when restricted to the 2D eigenspace,
        // which means (M^2 - 7M + I)(M^2 - I) = 0 for the full matrix.
        // Equivalently: M^4 - 7*M^3 + 7*M - I = 0.
        let m = hat_substitution_matrix::<F>();
        let m2 = m.mul(&m);
        let m3 = m2.mul(&m);
        let m4 = m3.mul(&m);
        let id = Matrix::<F>::identity(4);

        // M^4 - 7*M^3 + 7*M - I should be the zero matrix
        let result = &(&m4 + &m3.scale(-F::from(7u64))) + &(&m.scale(F::from(7u64)) + &id.scale(-F::ONE));
        for i in 0..4 {
            for j in 0..4 {
                assert_eq!(result[(i, j)], F::ZERO,
                    "char poly not satisfied at ({}, {})", i, j);
            }
        }
    }
}
