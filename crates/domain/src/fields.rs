use ark_bls12_381::Fr;
use ark_ff::{
    fields::models::fp2::{Fp2, Fp2Config},
    Field, MontFp,
};

// ---------------------------------------------------------------------------
// Fr(sqrt(5)) -- hat tiling eigenvalues, golden ratio phi = (1 + sqrt(5)) / 2
// ---------------------------------------------------------------------------

pub struct FrSqrt5Config;

impl Fp2Config for FrSqrt5Config {
    type Fp = Fr;

    /// 5 is a quadratic non-residue mod the BLS12-381 scalar field order.
    const NONRESIDUE: Fr = MontFp!("5");

    /// Frobenius coefficients: [1, NONRESIDUE^((r-1)/2)] = [1, -1]
    /// since 5 is a QNR, Euler's criterion gives 5^((r-1)/2) = -1.
    const FROBENIUS_COEFF_FP2_C1: &'static [Fr] = &[Fr::ONE, MontFp!("-1")];
}

/// Quadratic extension Fr[x]/(x^2 - 5). Elements are a + b*sqrt(5).
pub type FrSqrt5 = Fp2<FrSqrt5Config>;

// ---------------------------------------------------------------------------
// Fr(sqrt(15)) -- spectre tiling eigenvalues, scaling factor 4 + sqrt(15)
// ---------------------------------------------------------------------------

pub struct FrSqrt15Config;

impl Fp2Config for FrSqrt15Config {
    type Fp = Fr;

    /// 15 is a quadratic non-residue mod the BLS12-381 scalar field order.
    const NONRESIDUE: Fr = MontFp!("15");

    /// Frobenius coefficients: [1, -1] (same reasoning as FrSqrt5).
    const FROBENIUS_COEFF_FP2_C1: &'static [Fr] = &[Fr::ONE, MontFp!("-1")];
}

/// Quadratic extension Fr[x]/(x^2 - 15). Elements are a + b*sqrt(15).
pub type FrSqrt15 = Fp2<FrSqrt15Config>;

// ---------------------------------------------------------------------------
// Derived constants
// ---------------------------------------------------------------------------

/// The golden ratio phi = (1 + sqrt(5)) / 2 in Fr(sqrt(5)).
pub fn golden_ratio() -> FrSqrt5 {
    use ark_ff::Field;
    let two_inv = Fr::from(2u64).inverse().expect("2 is invertible in Fr");
    FrSqrt5::new(two_inv, two_inv)
}

/// phi^2 = phi + 1, which is also the hat inflation eigenvalue.
pub fn hat_inflation() -> FrSqrt5 {
    use ark_ff::Field;
    let two_inv = Fr::from(2u64).inverse().expect("2 is invertible in Fr");
    // phi^2 = (3 + sqrt(5)) / 2
    FrSqrt5::new(Fr::from(3u64) * two_inv, two_inv)
}

/// The spectre area scaling factor: 4 + sqrt(15) in Fr(sqrt(15)).
pub fn spectre_scaling() -> FrSqrt15 {
    FrSqrt15::new(Fr::from(4u64), Fr::from(1u64))
}

#[cfg(test)]
mod tests {
    use super::*;
    use ark_ff::Field;

    #[test]
    fn golden_ratio_squared_equals_phi_plus_one() {
        let phi = golden_ratio();
        let phi_sq = phi.square();
        let phi_plus_one = phi + FrSqrt5::new(Fr::from(1u64), Fr::from(0u64));
        assert_eq!(phi_sq, phi_plus_one);
    }

    #[test]
    fn hat_inflation_equals_phi_squared() {
        let phi = golden_ratio();
        let phi_sq = phi.square();
        let inflation = hat_inflation();
        assert_eq!(phi_sq, inflation);
    }

    #[test]
    fn sqrt5_squared_is_five() {
        let sqrt5 = FrSqrt5::new(Fr::from(0u64), Fr::from(1u64));
        let five = FrSqrt5::new(Fr::from(5u64), Fr::from(0u64));
        assert_eq!(sqrt5.square(), five);
    }

    #[test]
    fn sqrt15_squared_is_fifteen() {
        let sqrt15 = FrSqrt15::new(Fr::from(0u64), Fr::from(1u64));
        let fifteen = FrSqrt15::new(Fr::from(15u64), Fr::from(0u64));
        assert_eq!(sqrt15.square(), fifteen);
    }

    #[test]
    fn field_inverse_roundtrip_sqrt5() {
        let a = FrSqrt5::new(Fr::from(3u64), Fr::from(7u64));
        let a_inv = a.inverse().expect("nonzero element is invertible");
        assert_eq!(a * a_inv, FrSqrt5::ONE);
    }

    #[test]
    fn field_inverse_roundtrip_sqrt15() {
        let a = FrSqrt15::new(Fr::from(11u64), Fr::from(2u64));
        let a_inv = a.inverse().expect("nonzero element is invertible");
        assert_eq!(a * a_inv, FrSqrt15::ONE);
    }

    #[test]
    fn spectre_scaling_value() {
        let s = spectre_scaling();
        assert_eq!(s.c0, Fr::from(4u64));
        assert_eq!(s.c1, Fr::from(1u64));
    }
}
