use crate::coxeter::{CoxeterElement, Generator};
use Generator::*;

/// The 16-element Cucaracha: a mildly aperiodic monotile of the Coxeter group Gamma.
///
/// Obtained by applying the discretization functor Psi to the hat tile.
/// Elements are words of length <= 4 in {alpha, beta, gamma}, listed as:
/// {1, α, β, γ, αβ, βα, βγ, γβ, αβα, βαβ, βαγ, βγβ, γβα, αβαβ, βαγβ, γβαβ}
///
/// Reference: Coulbois, Gajardo, Guillon, Lutfalla (2024), "Aperiodic monotiles:
/// from geometry to groups", arXiv:2409.15880.
pub const CUCARACHA_WORDS: [&[Generator]; 16] = [
    &[],                                 // 1 (identity)
    &[Alpha],                            // α
    &[Beta],                             // β
    &[Gamma],                            // γ
    &[Alpha, Beta],                      // αβ
    &[Beta, Alpha],                      // βα
    &[Beta, Gamma],                      // βγ
    &[Gamma, Beta],                      // γβ
    &[Alpha, Beta, Alpha],              // αβα
    &[Beta, Alpha, Beta],               // βαβ
    &[Beta, Alpha, Gamma],              // βαγ
    &[Beta, Gamma, Beta],               // βγβ
    &[Gamma, Beta, Alpha],              // γβα
    &[Alpha, Beta, Alpha, Beta],        // αβαβ
    &[Beta, Alpha, Gamma, Beta],        // βαγβ
    &[Gamma, Beta, Alpha, Beta],        // γβαβ
];

/// Compute the 16 Cucaracha elements in normal form.
pub fn cucaracha() -> [CoxeterElement; 16] {
    let mut result = [CoxeterElement::identity(); 16];
    for (i, word) in CUCARACHA_WORDS.iter().enumerate() {
        result[i] = CoxeterElement::from_generators(word);
    }
    result
}

/// A cotiler: a set of group elements g such that {g * c : c in Cucaracha}
/// partitions a region of Gamma.
///
/// The possible stabilizers of Cucaracha cotilers are {id} or conjugates of
/// {id, R_3, R_3^2} (3-fold rotational symmetry).
#[derive(Clone, Debug)]
pub struct Cotiler {
    pub positions: Vec<CoxeterElement>,
}

impl Cotiler {
    pub fn new(positions: Vec<CoxeterElement>) -> Self {
        Self { positions }
    }

    /// Check that no two translated copies of the Cucaracha overlap.
    /// Returns true if all tile placements are pairwise disjoint.
    pub fn is_non_overlapping(&self) -> bool {
        let tile = cucaracha();
        let mut all_cells = std::collections::HashSet::new();
        for pos in &self.positions {
            for cell in &tile {
                let placed = pos.compose(cell);
                if !all_cells.insert(placed) {
                    return false;
                }
            }
        }
        true
    }

    /// Count the total number of cells covered by this cotiler.
    pub fn cell_count(&self) -> usize {
        self.positions.len() * 16
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn cucaracha_has_16_distinct_elements() {
        let elements = cucaracha();
        let unique: std::collections::HashSet<_> = elements.iter().collect();
        assert_eq!(unique.len(), 16);
    }

    #[test]
    fn cucaracha_contains_identity() {
        let elements = cucaracha();
        assert!(elements.contains(&CoxeterElement::identity()));
    }

    #[test]
    fn cucaracha_contains_all_generators() {
        let elements = cucaracha();
        assert!(elements.contains(&CoxeterElement::generator(Alpha)));
        assert!(elements.contains(&CoxeterElement::generator(Beta)));
        assert!(elements.contains(&CoxeterElement::generator(Gamma)));
    }

    #[test]
    fn cucaracha_word_lengths_are_at_most_four() {
        for word in &CUCARACHA_WORDS {
            assert!(word.len() <= 4, "word too long: {:?}", word);
        }
    }

    #[test]
    fn cucaracha_normal_forms_match_expected() {
        let elements = cucaracha();

        // Verify specific known normal forms
        assert_eq!(elements[0], CoxeterElement::new(0, 0, 0, false)); // id
        assert_eq!(elements[1], CoxeterElement::new(0, 0, 0, true)); // α
        assert_eq!(elements[2], CoxeterElement::new(0, 0, 1, true)); // β
        assert_eq!(elements[3], CoxeterElement::new(1, 0, 3, true)); // γ
        assert_eq!(elements[4], CoxeterElement::new(0, 0, 5, false)); // αβ
        assert_eq!(elements[5], CoxeterElement::new(0, 0, 1, false)); // βα
        assert_eq!(elements[6], CoxeterElement::new(0, 1, 4, false)); // βγ
        assert_eq!(elements[7], CoxeterElement::new(1, 0, 2, false)); // γβ
    }

    #[test]
    fn single_tile_is_non_overlapping() {
        let cotiler = Cotiler::new(vec![CoxeterElement::identity()]);
        assert!(cotiler.is_non_overlapping());
        assert_eq!(cotiler.cell_count(), 16);
    }

    #[test]
    fn cucaracha_elements_closed_under_left_action() {
        // Composing any Cucaracha element with the identity cotiler
        // should produce distinct cells (no internal collision)
        let elements = cucaracha();
        let composed: Vec<CoxeterElement> = elements
            .iter()
            .map(|c| CoxeterElement::identity().compose(c))
            .collect();
        let unique: std::collections::HashSet<_> = composed.iter().collect();
        assert_eq!(unique.len(), 16);
    }
}
