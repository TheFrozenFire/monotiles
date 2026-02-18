use super::TilingSystem;
use crate::metatile::{
    InflationRule, BOUNDARY_CHILDREN, SUPERTILE_F_CHILDREN, SUPERTILE_H_CHILDREN,
    SUPERTILE_P_CHILDREN, SUPERTILE_T_CHILDREN,
};

pub use crate::metatile::MetatileType;

const TYPE_NAMES: [&str; 4] = ["H", "T", "P", "F"];
const SUPERTILE_NAMES: [&str; 4] = ["H'", "T'", "P'", "F'"];

/// The hat tiling system: 4 metatile types (H/T/P/F), 29 inflation children.
pub struct HatSystem {
    child_types: Vec<usize>,
    supertile_children: [Vec<usize>; 4],
    boundary: Vec<usize>,
    composition: Vec<Vec<usize>>,
    adjacency: Vec<Vec<usize>>,
}

impl HatSystem {
    pub fn new() -> Self {
        let rules = crate::metatile::inflation_rules();

        let child_types: Vec<usize> = rules
            .iter()
            .map(|rule| match rule {
                InflationRule::Seed(t) => t.index(),
                InflationRule::Adjacent { child_type, .. } => child_type.index(),
                InflationRule::Bridge { child_type, .. } => child_type.index(),
            })
            .collect();

        let supertile_children = [
            SUPERTILE_H_CHILDREN.to_vec(),
            SUPERTILE_T_CHILDREN.to_vec(),
            SUPERTILE_P_CHILDREN.to_vec(),
            SUPERTILE_F_CHILDREN.to_vec(),
        ];

        let boundary = BOUNDARY_CHILDREN.to_vec();

        let comp = crate::metatile::supertile_composition();
        let composition: Vec<Vec<usize>> = comp.iter().map(|row| row.to_vec()).collect();

        // Build adjacency from inflation rules (neighbor indices only)
        let n = rules.len();
        let mut adjacency: Vec<Vec<usize>> = vec![Vec::new(); n];
        for (child_idx, rule) in rules.iter().enumerate() {
            match rule {
                InflationRule::Seed(_) => {}
                InflationRule::Adjacent { parent, .. } => {
                    if !adjacency[*parent].contains(&child_idx) {
                        adjacency[*parent].push(child_idx);
                    }
                    if !adjacency[child_idx].contains(parent) {
                        adjacency[child_idx].push(*parent);
                    }
                }
                InflationRule::Bridge {
                    parent_a, parent_b, ..
                } => {
                    if !adjacency[*parent_a].contains(&child_idx) {
                        adjacency[*parent_a].push(child_idx);
                    }
                    if !adjacency[child_idx].contains(parent_a) {
                        adjacency[child_idx].push(*parent_a);
                    }
                    if !adjacency[*parent_b].contains(&child_idx) {
                        adjacency[*parent_b].push(child_idx);
                    }
                    if !adjacency[child_idx].contains(parent_b) {
                        adjacency[child_idx].push(*parent_b);
                    }
                }
            }
        }

        Self {
            child_types,
            supertile_children,
            boundary,
            composition,
            adjacency,
        }
    }
}

impl TilingSystem for HatSystem {
    fn name(&self) -> &str {
        "hat"
    }
    fn num_types(&self) -> usize {
        4
    }
    fn type_name(&self, index: usize) -> &str {
        TYPE_NAMES[index]
    }
    fn supertile_name(&self, index: usize) -> &str {
        SUPERTILE_NAMES[index]
    }

    fn num_inflation_children(&self) -> usize {
        self.child_types.len()
    }
    fn inflation_child_type(&self, child: usize) -> usize {
        self.child_types[child]
    }
    fn supertile_children(&self, type_index: usize) -> &[usize] {
        &self.supertile_children[type_index]
    }
    fn boundary_children(&self) -> &[usize] {
        &self.boundary
    }

    fn composition(&self) -> &[Vec<usize>] {
        &self.composition
    }
    fn inflation_adjacency(&self) -> &[Vec<usize>] {
        &self.adjacency
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn hat_system_basics() {
        let sys = HatSystem::new();
        assert_eq!(sys.name(), "hat");
        assert_eq!(sys.num_types(), 4);
        assert_eq!(sys.num_inflation_children(), 29);
    }

    #[test]
    fn hat_composition_matches_metatile() {
        let sys = HatSystem::new();
        let comp = sys.composition();
        assert_eq!(comp[0], vec![3, 1, 3, 3]); // H'
        assert_eq!(comp[1], vec![1, 0, 0, 0]); // T'
        assert_eq!(comp[2], vec![2, 0, 1, 2]); // P'
        assert_eq!(comp[3], vec![2, 0, 1, 3]); // F'
    }

    #[test]
    fn hat_supertile_children_match() {
        let sys = HatSystem::new();
        assert_eq!(sys.supertile_children(0), SUPERTILE_H_CHILDREN);
        assert_eq!(sys.supertile_children(1), SUPERTILE_T_CHILDREN);
        assert_eq!(sys.supertile_children(2), SUPERTILE_P_CHILDREN);
        assert_eq!(sys.supertile_children(3), SUPERTILE_F_CHILDREN);
    }

    #[test]
    fn hat_child_types_match_rules() {
        let sys = HatSystem::new();
        let rules = crate::metatile::inflation_rules();
        for (i, rule) in rules.iter().enumerate() {
            let expected = match rule {
                InflationRule::Seed(t) => t.index(),
                InflationRule::Adjacent { child_type, .. } => child_type.index(),
                InflationRule::Bridge { child_type, .. } => child_type.index(),
            };
            assert_eq!(sys.inflation_child_type(i), expected, "child {} type mismatch", i);
        }
    }

    #[test]
    fn hat_adjacency_is_symmetric() {
        let sys = HatSystem::new();
        let adj = sys.inflation_adjacency();
        for (i, neighbors) in adj.iter().enumerate() {
            for &j in neighbors {
                assert!(
                    adj[j].contains(&i),
                    "adjacency {}->{} is not symmetric",
                    i,
                    j
                );
            }
        }
    }
}
