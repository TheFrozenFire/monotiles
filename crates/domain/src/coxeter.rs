use ark_ff::PrimeField;

/// Generators of the Coxeter group Gamma.
///
/// Gamma = <alpha, beta, gamma | alpha^2, beta^2, gamma^2,
///          (alpha*beta)^6, (beta*gamma)^3, (alpha*gamma)^2>
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum Generator {
    Alpha,
    Beta,
    Gamma,
}

/// Element of the triangle Coxeter group Gamma = Z^2 ⋊ D_6.
///
/// Normal form: translation (tx, ty) in Z^2, rotation r in Z/6Z,
/// optional reflection. Encodes g = t_1^tx * t_2^ty * R_6^rotation * sigma^reflected.
///
/// The lattice Z^2 uses hexagonal coordinates with basis vectors at 60 degrees.
/// R_6 is rotation by pi/3 (60 degrees), sigma is a reflection.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub struct CoxeterElement {
    pub tx: i64,
    pub ty: i64,
    pub rotation: u8,
    pub reflected: bool,
}

impl CoxeterElement {
    pub fn new(tx: i64, ty: i64, rotation: u8, reflected: bool) -> Self {
        debug_assert!(rotation < 6);
        Self {
            tx,
            ty,
            rotation: rotation % 6,
            reflected,
        }
    }

    pub fn identity() -> Self {
        Self::new(0, 0, 0, false)
    }

    /// The three Coxeter generators in normal form.
    ///
    /// These satisfy all six Coxeter relations:
    /// alpha^2 = beta^2 = gamma^2 = id
    /// (alpha*beta)^6 = (beta*gamma)^3 = (alpha*gamma)^2 = id
    pub fn generator(g: Generator) -> Self {
        match g {
            Generator::Alpha => Self::new(0, 0, 0, true),
            Generator::Beta => Self::new(0, 0, 1, true),
            Generator::Gamma => Self::new(1, 0, 3, true),
        }
    }

    /// Compose two elements using the semidirect product rule.
    ///
    /// (v1, r1, s1) * (v2, r2, s2) = (v1 + phi(r1,s1)(v2), r1 + (-1)^s1 * r2, s1 xor s2)
    pub fn compose(&self, other: &Self) -> Self {
        let (av, bv) = self.act_on(other.tx, other.ty);
        let new_tx = self.tx + av;
        let new_ty = self.ty + bv;

        let new_rotation = if self.reflected {
            (self.rotation as i64 - other.rotation as i64).rem_euclid(6) as u8
        } else {
            (self.rotation + other.rotation) % 6
        };

        let new_reflected = self.reflected ^ other.reflected;

        Self::new(new_tx, new_ty, new_rotation, new_reflected)
    }

    /// Compute the inverse element.
    ///
    /// For (v, g): inverse is (-phi(g^-1)(v), g^-1)
    /// Rotation-reflection inverse: if reflected, (r, true)^-1 = (r, true);
    /// if not reflected, (r, false)^-1 = (6-r mod 6, false).
    pub fn inverse(&self) -> Self {
        let inv_rotation = if self.reflected {
            self.rotation
        } else {
            (6 - self.rotation) % 6
        };
        let inv_reflected = self.reflected;

        // Compute -phi(g^-1)(v)
        let inv_element = Self::new(0, 0, inv_rotation, inv_reflected);
        let (neg_ax, neg_ay) = inv_element.act_on(self.tx, self.ty);

        Self::new(-neg_ax, -neg_ay, inv_rotation, inv_reflected)
    }

    /// Reduce a word in generators to normal form.
    pub fn from_generators(word: &[Generator]) -> Self {
        word.iter()
            .fold(Self::identity(), |acc, g| acc.compose(&Self::generator(*g)))
    }

    /// Encode as field elements for ZK circuits: (tx, ty, rotation).
    /// Reflection is encoded as 0 or 1 in the rotation field's sign convention.
    pub fn to_field_elements<F: PrimeField>(&self) -> (F, F, F, F) {
        let tx = if self.tx >= 0 {
            F::from(self.tx as u64)
        } else {
            -F::from((-self.tx) as u64)
        };
        let ty = if self.ty >= 0 {
            F::from(self.ty as u64)
        } else {
            -F::from((-self.ty) as u64)
        };
        let rotation = F::from(self.rotation as u64);
        let reflected = if self.reflected { F::ONE } else { F::ZERO };
        (tx, ty, rotation, reflected)
    }

    /// Apply the rotation-reflection action phi(r, s) to a lattice vector.
    ///
    /// phi(r, s)(v) = R^r(sigma^s(v))
    /// where R is 60-degree rotation: (a,b) -> (-b, a+b)
    /// and sigma is reflection: (a,b) -> (a+b, -b)
    fn act_on(&self, a: i64, b: i64) -> (i64, i64) {
        // First apply reflection if needed
        let (a, b) = if self.reflected {
            (a + b, -b) // sigma
        } else {
            (a, b)
        };

        // Then apply R_6^rotation
        rotate(a, b, self.rotation)
    }
}

/// Apply R_6^r to lattice vector (a, b).
///
/// R_6 maps (a, b) -> (-b, a+b) (60-degree rotation in hexagonal coordinates).
fn rotate(a: i64, b: i64, r: u8) -> (i64, i64) {
    match r % 6 {
        0 => (a, b),
        1 => (-b, a + b),
        2 => (-a - b, a),
        3 => (-a, -b),
        4 => (b, -a - b),
        5 => (a + b, -a),
        _ => unreachable!(),
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn alpha() -> CoxeterElement {
        CoxeterElement::generator(Generator::Alpha)
    }
    fn beta() -> CoxeterElement {
        CoxeterElement::generator(Generator::Beta)
    }
    fn gamma() -> CoxeterElement {
        CoxeterElement::generator(Generator::Gamma)
    }
    fn id() -> CoxeterElement {
        CoxeterElement::identity()
    }

    fn pow(g: &CoxeterElement, n: u32) -> CoxeterElement {
        (0..n).fold(id(), |acc, _| acc.compose(g))
    }

    // -- Coxeter relations --

    #[test]
    fn alpha_squared_is_identity() {
        assert_eq!(alpha().compose(&alpha()), id());
    }

    #[test]
    fn beta_squared_is_identity() {
        assert_eq!(beta().compose(&beta()), id());
    }

    #[test]
    fn gamma_squared_is_identity() {
        assert_eq!(gamma().compose(&gamma()), id());
    }

    #[test]
    fn alpha_beta_order_six() {
        let ab = alpha().compose(&beta());
        assert_eq!(pow(&ab, 6), id());
        // Verify it's exactly order 6 (not a divisor)
        assert_ne!(pow(&ab, 1), id());
        assert_ne!(pow(&ab, 2), id());
        assert_ne!(pow(&ab, 3), id());
    }

    #[test]
    fn beta_gamma_order_three() {
        let bg = beta().compose(&gamma());
        assert_eq!(pow(&bg, 3), id());
        assert_ne!(pow(&bg, 1), id());
    }

    #[test]
    fn alpha_gamma_order_two() {
        let ag = alpha().compose(&gamma());
        assert_eq!(pow(&ag, 2), id());
        assert_ne!(pow(&ag, 1), id());
    }

    // -- Identity and inverse --

    #[test]
    fn identity_is_neutral() {
        let g = CoxeterElement::new(3, -2, 4, true);
        assert_eq!(id().compose(&g), g);
        assert_eq!(g.compose(&id()), g);
    }

    #[test]
    fn inverse_compose_is_identity() {
        let elements = [
            CoxeterElement::new(0, 0, 0, false),
            CoxeterElement::new(1, 0, 3, true),
            CoxeterElement::new(-2, 5, 4, false),
            CoxeterElement::new(3, -1, 2, true),
            CoxeterElement::new(0, 0, 1, true),
        ];
        for g in &elements {
            let g_inv = g.inverse();
            assert_eq!(g.compose(&g_inv), id(), "g * g^-1 != id for {:?}", g);
            assert_eq!(g_inv.compose(g), id(), "g^-1 * g != id for {:?}", g);
        }
    }

    // -- from_generators --

    #[test]
    fn from_generators_empty_is_identity() {
        assert_eq!(CoxeterElement::from_generators(&[]), id());
    }

    #[test]
    fn from_generators_single() {
        assert_eq!(
            CoxeterElement::from_generators(&[Generator::Alpha]),
            alpha()
        );
        assert_eq!(
            CoxeterElement::from_generators(&[Generator::Beta]),
            beta()
        );
        assert_eq!(
            CoxeterElement::from_generators(&[Generator::Gamma]),
            gamma()
        );
    }

    #[test]
    fn from_generators_composite() {
        let ab = CoxeterElement::from_generators(&[Generator::Alpha, Generator::Beta]);
        assert_eq!(ab, alpha().compose(&beta()));
    }

    // -- Associativity --

    #[test]
    fn composition_is_associative() {
        let a = CoxeterElement::new(1, -1, 3, true);
        let b = CoxeterElement::new(0, 2, 5, false);
        let c = CoxeterElement::new(-1, 0, 1, true);

        let ab_c = a.compose(&b).compose(&c);
        let a_bc = a.compose(&b.compose(&c));
        assert_eq!(ab_c, a_bc);
    }

    // -- Rotation helper --

    #[test]
    fn rotation_period_six() {
        let (a, b) = (3, -2);
        let (ra, rb) = rotate(a, b, 6);
        assert_eq!((ra, rb), (a, b));
    }
}
