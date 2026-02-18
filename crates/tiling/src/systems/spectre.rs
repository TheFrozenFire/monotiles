use super::TilingSystem;

const TYPE_NAMES: [&str; 2] = ["Spectre", "Mystic"];
const SUPERTILE_NAMES: [&str; 2] = ["Spectre'", "Mystic'"];

/// The spectre tiling system: 2 tile types (Spectre + Mystic), 15 inflation children.
///
/// Substitution rules from Smith, Myers, Kaplan, Goodman-Strauss (2023):
/// - Spectre' = 7 Spectres + 1 Mystic (8 children)
/// - Mystic'  = 6 Spectres + 1 Mystic (7 children)
///
/// Total inflation children: 15 (8 + 7), no boundary children.
/// Inflation reverses tile orientation at each level.
pub struct SpectreSystem {
    child_types: Vec<usize>,
    spectre_children: Vec<usize>,
    mystic_children: Vec<usize>,
    composition: Vec<Vec<usize>>,
    adjacency: Vec<Vec<usize>>,
}

impl SpectreSystem {
    pub fn new() -> Self {
        // Spectre supertile: children 0..7 (7 Spectres + 1 Mystic)
        // Child types: S S S S S S S M
        let spectre_children: Vec<usize> = (0..8).collect();
        let spectre_child_types = vec![0, 0, 0, 0, 0, 0, 0, 1]; // 7S + 1M

        // Mystic supertile: children 8..14 (6 Spectres + 1 Mystic)
        // Child types: S S S S S S M
        let mystic_children: Vec<usize> = (8..15).collect();
        let mystic_child_types = vec![0, 0, 0, 0, 0, 0, 1]; // 6S + 1M

        let mut child_types = spectre_child_types;
        child_types.extend(mystic_child_types);

        let composition = vec![
            vec![7, 1], // Spectre' = 7S + 1M
            vec![6, 1], // Mystic'  = 6S + 1M
        ];

        // Conservative adjacency: all children within each supertile are mutually adjacent.
        // (Exact geometric adjacency from the paper can be refined later.)
        let mut adjacency: Vec<Vec<usize>> = vec![Vec::new(); 15];
        for children in [&spectre_children, &mystic_children] {
            for &a in children {
                for &b in children {
                    if a != b {
                        adjacency[a].push(b);
                    }
                }
            }
        }

        Self {
            child_types,
            spectre_children,
            mystic_children,
            composition,
            adjacency,
        }
    }
}

impl TilingSystem for SpectreSystem {
    fn name(&self) -> &str {
        "spectre"
    }
    fn num_types(&self) -> usize {
        2
    }
    fn type_name(&self, index: usize) -> &str {
        TYPE_NAMES[index]
    }
    fn supertile_name(&self, index: usize) -> &str {
        SUPERTILE_NAMES[index]
    }

    fn num_inflation_children(&self) -> usize {
        15
    }
    fn inflation_child_type(&self, child: usize) -> usize {
        self.child_types[child]
    }
    fn supertile_children(&self, type_index: usize) -> &[usize] {
        match type_index {
            0 => &self.spectre_children,
            1 => &self.mystic_children,
            _ => panic!("invalid spectre type index: {}", type_index),
        }
    }
    fn boundary_children(&self) -> &[usize] {
        &[] // No boundary children in spectre system
    }

    fn composition(&self) -> &[Vec<usize>] {
        &self.composition
    }
    fn inflation_adjacency(&self) -> &[Vec<usize>] {
        &self.adjacency
    }

    fn reverses_orientation(&self) -> bool {
        true
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn spectre_system_basics() {
        let sys = SpectreSystem::new();
        assert_eq!(sys.name(), "spectre");
        assert_eq!(sys.num_types(), 2);
        assert_eq!(sys.num_inflation_children(), 15);
        assert!(sys.reverses_orientation());
    }

    #[test]
    fn spectre_composition() {
        let sys = SpectreSystem::new();
        let comp = sys.composition();
        assert_eq!(comp[0], vec![7, 1]); // Spectre'
        assert_eq!(comp[1], vec![6, 1]); // Mystic'
    }

    #[test]
    fn spectre_supertile_children() {
        let sys = SpectreSystem::new();
        assert_eq!(sys.supertile_children(0).len(), 8); // Spectre': 7S + 1M = 8
        assert_eq!(sys.supertile_children(1).len(), 7); // Mystic': 6S + 1M = 7
    }

    #[test]
    fn spectre_child_type_counts() {
        let sys = SpectreSystem::new();
        // Spectre supertile children: 7 spectres + 1 mystic
        let s_children = sys.supertile_children(0);
        let s_count = s_children
            .iter()
            .filter(|&&c| sys.inflation_child_type(c) == 0)
            .count();
        let m_count = s_children
            .iter()
            .filter(|&&c| sys.inflation_child_type(c) == 1)
            .count();
        assert_eq!(s_count, 7);
        assert_eq!(m_count, 1);

        // Mystic supertile children: 6 spectres + 1 mystic
        let m_children = sys.supertile_children(1);
        let s_count = m_children
            .iter()
            .filter(|&&c| sys.inflation_child_type(c) == 0)
            .count();
        let m_count = m_children
            .iter()
            .filter(|&&c| sys.inflation_child_type(c) == 1)
            .count();
        assert_eq!(s_count, 6);
        assert_eq!(m_count, 1);
    }

    #[test]
    fn spectre_no_boundary_children() {
        let sys = SpectreSystem::new();
        assert!(sys.boundary_children().is_empty());
    }

    #[test]
    fn spectre_hierarchy_type_counts_grow() {
        use crate::substitution::generate_counts_system;
        let sys = SpectreSystem::new();
        let counts = generate_counts_system(&sys, 0, 5);
        for i in 1..counts.len() {
            let total_prev: usize = counts[i - 1].iter().sum();
            let total_curr: usize = counts[i].iter().sum();
            assert!(total_curr > total_prev, "level {} didn't grow", i);
        }
    }

    #[test]
    fn spectre_decomposition_unique() {
        use crate::oneway::{build_hierarchy, count_decompositions};
        let sys = SpectreSystem::new();
        for depth in 1..=3 {
            let hierarchy = build_hierarchy(&sys, 0, depth);
            for level in 0..depth {
                let mut counts = vec![0usize; 2];
                for &t in &hierarchy.tile_types[level] {
                    counts[t] += 1;
                }
                assert_eq!(
                    count_decompositions(&sys, &counts),
                    1,
                    "spectre depth {} level {} should have unique decomposition",
                    depth, level
                );
            }
        }
    }

    #[test]
    fn spectre_full_sibling_determines_all() {
        use crate::oneway::{
            build_hierarchy, compute_determination_radii, full_sibling_adjacency,
        };
        let sys = SpectreSystem::new();
        let hierarchy = build_hierarchy(&sys, 0, 3);
        for level in 0..3 {
            let adj = full_sibling_adjacency(&hierarchy, level);
            let radii = compute_determination_radii(&hierarchy, &adj, level, 5);
            let undetermined = radii.iter().filter(|r| r.is_none()).count();
            assert_eq!(
                undetermined, 0,
                "spectre level {} should have all tiles determined",
                level
            );
        }
    }

    #[test]
    fn spectre_vulnerability_runs() {
        use crate::vulnerability::analyze_system;
        let sys = SpectreSystem::new();
        let analysis = analyze_system(&sys, 0, 2, 10);
        // Basic sanity checks
        assert!(analysis.base_tiles > 0);
        assert!(!analysis.determining_sets.is_empty());
    }
}
