use super::TilingSystem;
use super::hat::HatSystem;

/// The hat-turtle tiling system: same combinatorial structure as hat,
/// parameterized by edge ratio a/b.
///
/// Hat (a/b = 1/sqrt(3)) and Turtle (a/b = sqrt(3)) are the two extremes.
/// All intermediate values produce valid aperiodic tilings with identical
/// substitution rules and composition matrices.
pub struct HatTurtleSystem {
    hat: HatSystem,
    pub edge_ratio: f64,
}

impl Default for HatTurtleSystem {
    fn default() -> Self {
        Self {
            hat: HatSystem::new(),
            edge_ratio: 1.0 / 3.0_f64.sqrt(), // Hat default
        }
    }
}

impl HatTurtleSystem {
    pub fn with_edge_ratio(edge_ratio: f64) -> Self {
        Self {
            hat: HatSystem::new(),
            edge_ratio,
        }
    }
}

impl TilingSystem for HatTurtleSystem {
    fn name(&self) -> &str {
        "hat-turtle"
    }
    fn num_types(&self) -> usize {
        self.hat.num_types()
    }
    fn type_name(&self, index: usize) -> &str {
        self.hat.type_name(index)
    }
    fn supertile_name(&self, index: usize) -> &str {
        self.hat.supertile_name(index)
    }

    fn num_inflation_children(&self) -> usize {
        self.hat.num_inflation_children()
    }
    fn inflation_child_type(&self, child: usize) -> usize {
        self.hat.inflation_child_type(child)
    }
    fn supertile_children(&self, type_index: usize) -> &[usize] {
        self.hat.supertile_children(type_index)
    }
    fn boundary_children(&self) -> &[usize] {
        self.hat.boundary_children()
    }

    fn composition(&self) -> &[Vec<usize>] {
        self.hat.composition()
    }
    fn inflation_adjacency(&self) -> &[Vec<usize>] {
        self.hat.inflation_adjacency()
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn hat_turtle_delegates_to_hat() {
        let ht = HatTurtleSystem::default();
        let hat = HatSystem::new();

        assert_eq!(ht.num_types(), hat.num_types());
        assert_eq!(ht.num_inflation_children(), hat.num_inflation_children());
        assert_eq!(ht.composition(), hat.composition());

        for i in 0..ht.num_types() {
            assert_eq!(ht.supertile_children(i), hat.supertile_children(i));
        }
    }

    #[test]
    fn hat_turtle_analysis_matches_hat() {
        use crate::oneway::analyze_system;

        let hat = HatSystem::new();
        let ht = HatTurtleSystem::default();

        let hat_result = analyze_system(&hat, 0, 3, 5);
        let ht_result = analyze_system(&ht, 0, 3, 5);

        assert_eq!(hat_result.tiles_per_level, ht_result.tiles_per_level);
        assert_eq!(
            hat_result.base_decomposition_count,
            ht_result.base_decomposition_count
        );
        assert_eq!(
            hat_result.local_deflate_unresolved,
            ht_result.local_deflate_unresolved
        );

        for (level, (h, t)) in hat_result
            .full_sibling
            .iter()
            .zip(ht_result.full_sibling.iter())
            .enumerate()
        {
            assert_eq!(
                h.undetermined, t.undetermined,
                "level {} undetermined mismatch",
                level
            );
            assert_eq!(
                h.radii_histogram, t.radii_histogram,
                "level {} histogram mismatch",
                level
            );
        }
    }

    #[test]
    fn hat_turtle_vulnerability_matches_hat() {
        use crate::vulnerability::analyze_system;

        let hat = HatSystem::new();
        let ht = HatTurtleSystem::default();

        let hat_v = analyze_system(&hat, 0, 2, 10);
        let ht_v = analyze_system(&ht, 0, 2, 10);

        assert_eq!(hat_v.swaps.len(), ht_v.swaps.len());
        assert_eq!(hat_v.criticality.len(), ht_v.criticality.len());
        assert_eq!(hat_v.determining_sets.len(), ht_v.determining_sets.len());
        assert_eq!(hat_v.base_tiles, ht_v.base_tiles);
    }
}
