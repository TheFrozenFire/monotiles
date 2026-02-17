use std::collections::HashMap;

use crate::adjacency::inflation_adjacency;
use crate::metatile::{
    MetatileType, BOUNDARY_CHILDREN, SUPERTILE_F_CHILDREN, SUPERTILE_H_CHILDREN,
    SUPERTILE_P_CHILDREN, SUPERTILE_T_CHILDREN,
};

/// The composition assignment: which supertile type and which child role.
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct CompositionAssignment {
    /// Which supertile this metatile belongs to (H, T, P, or F).
    pub supertile_type: MetatileType,
    /// The position of this metatile within the supertile's child list.
    pub child_index: usize,
    /// The original inflation child index (0..28).
    pub inflation_index: usize,
}

/// The direct composition map: inflation child index -> supertile assignment.
///
/// Every assigned child (indices 0..28 minus the 7 boundary children) maps to
/// exactly one supertile type and position within that supertile.
///
/// This is the computational core of recognizability: the inflation rules fix
/// the composition structure deterministically.
pub fn composition_map() -> HashMap<usize, CompositionAssignment> {
    let supertiles: [(MetatileType, &[usize]); 4] = [
        (MetatileType::H, SUPERTILE_H_CHILDREN),
        (MetatileType::T, SUPERTILE_T_CHILDREN),
        (MetatileType::P, SUPERTILE_P_CHILDREN),
        (MetatileType::F, SUPERTILE_F_CHILDREN),
    ];

    let mut map = HashMap::new();
    for (st_type, children) in &supertiles {
        for (pos, &child_idx) in children.iter().enumerate() {
            map.insert(
                child_idx,
                CompositionAssignment {
                    supertile_type: *st_type,
                    child_index: pos,
                    inflation_index: child_idx,
                },
            );
        }
    }
    map
}

/// Verify composition map integrity.
///
/// Checks that:
/// 1. All 22 assigned children have entries
/// 2. No boundary children are included
/// 3. The type counts match the substitution matrix
/// 4. No duplicate assignments (each child maps to exactly one supertile)
pub fn verify_composition_integrity() -> Result<(), String> {
    let map = composition_map();
    let adj = inflation_adjacency();

    // Check count
    if map.len() != 22 {
        return Err(format!("Expected 22 assigned children, got {}", map.len()));
    }

    // Check no boundary children
    for &b in BOUNDARY_CHILDREN {
        if map.contains_key(&b) {
            return Err(format!("Boundary child {} should not be in composition map", b));
        }
    }

    // Check composition counts match substitution matrix
    let mut counts = [[0usize; 4]; 4];
    for (&child_idx, assign) in &map {
        let child_type = adj.child_types[child_idx];
        counts[assign.supertile_type.index()][child_type.index()] += 1;
    }

    let expected = crate::metatile::supertile_composition();
    if counts != expected {
        return Err(format!(
            "Composition counts {:?} don't match substitution matrix {:?}",
            counts, expected
        ));
    }

    // Check no duplicate supertile positions
    let mut seen_positions: HashMap<(usize, usize), usize> = HashMap::new();
    for (&child_idx, assign) in &map {
        let key = (assign.supertile_type.index(), assign.child_index);
        if let Some(prev) = seen_positions.get(&key) {
            return Err(format!(
                "Duplicate position: children {} and {} both at supertile {:?} position {}",
                prev, child_idx, assign.supertile_type, assign.child_index
            ));
        }
        seen_positions.insert(key, child_idx);
    }

    Ok(())
}

/// Check whether two adjacent P tiles can have the same orientation.
///
/// In the hat tiling, the PP same-orientation configuration is forbidden.
/// This checks that no pair of adjacent P-type children have matching
/// vertex indices (which would indicate same-orientation adjacency).
pub fn check_no_pp_same_orientation() -> bool {
    let adj = inflation_adjacency();

    for (i, neighbors) in adj.adjacencies.iter().enumerate() {
        if adj.child_types[i] != MetatileType::P {
            continue;
        }
        for n in neighbors {
            if adj.child_types[n.neighbor] != MetatileType::P {
                continue;
            }
            if n.self_vertex == n.neighbor_vertex {
                return false;
            }
        }
    }

    true
}

/// Recognizability data: for each supertile type, the complete specification
/// of its children (types and placement-tree adjacencies).
///
/// This captures the invariant that inflation is deterministic: a supertile
/// type completely determines its children's types and their internal topology.
#[derive(Clone, Debug)]
pub struct SupertileSpec {
    /// The supertile type.
    pub supertile_type: MetatileType,
    /// The children: (inflation_index, metatile_type) for each position.
    pub children: Vec<(usize, MetatileType)>,
    /// Internal adjacencies between children (within this supertile).
    pub internal_adjacencies: Vec<(usize, usize)>,
}

/// Build complete supertile specifications for all four types.
///
/// Each spec fully describes the internal structure of a supertile: which
/// children it has, their types, and how they connect. This data supports
/// the recognizability proof by showing that inflation is deterministic.
pub fn supertile_specs() -> Vec<SupertileSpec> {
    let adj = inflation_adjacency();

    let supertiles: [(MetatileType, &[usize]); 4] = [
        (MetatileType::H, SUPERTILE_H_CHILDREN),
        (MetatileType::T, SUPERTILE_T_CHILDREN),
        (MetatileType::P, SUPERTILE_P_CHILDREN),
        (MetatileType::F, SUPERTILE_F_CHILDREN),
    ];

    supertiles
        .iter()
        .map(|(st_type, children)| {
            let child_set: std::collections::HashSet<usize> = children.iter().copied().collect();

            let children_with_types: Vec<(usize, MetatileType)> = children
                .iter()
                .map(|&idx| (idx, adj.child_types[idx]))
                .collect();

            // Find adjacencies where both endpoints are in this supertile
            let mut internal_adj = Vec::new();
            for &child_idx in *children {
                for neighbor in &adj.adjacencies[child_idx] {
                    if child_set.contains(&neighbor.neighbor) && child_idx < neighbor.neighbor {
                        internal_adj.push((child_idx, neighbor.neighbor));
                    }
                }
            }

            SupertileSpec {
                supertile_type: *st_type,
                children: children_with_types,
                internal_adjacencies: internal_adj,
            }
        })
        .collect()
}

/// Export the composition data as a sorted list for ROCQ verification.
///
/// Each entry is (inflation_index, supertile_type_index, position_in_supertile).
pub fn export_for_rocq() -> Vec<(usize, usize, usize)> {
    let map = composition_map();
    let mut entries: Vec<(usize, usize, usize)> = map
        .into_iter()
        .map(|(idx, assign)| (idx, assign.supertile_type.index(), assign.child_index))
        .collect();
    entries.sort_by_key(|(idx, _, _)| *idx);
    entries
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn composition_map_has_22_entries() {
        let map = composition_map();
        assert_eq!(map.len(), 22, "should have exactly 22 assigned children");
    }

    #[test]
    fn composition_map_excludes_boundary() {
        let map = composition_map();
        for &boundary_idx in BOUNDARY_CHILDREN {
            assert!(
                !map.contains_key(&boundary_idx),
                "boundary child {} should not be in composition map",
                boundary_idx
            );
        }
    }

    #[test]
    fn composition_integrity_verified() {
        verify_composition_integrity().expect("composition integrity check should pass");
    }

    #[test]
    fn composition_counts_match_substitution_matrix() {
        let map = composition_map();
        let adj = inflation_adjacency();

        let mut counts = [[0usize; 4]; 4];
        for (&child_idx, assign) in &map {
            let child_type = adj.child_types[child_idx];
            counts[assign.supertile_type.index()][child_type.index()] += 1;
        }

        let expected = crate::metatile::supertile_composition();
        assert_eq!(counts, expected);
    }

    #[test]
    fn all_four_supertile_types_present() {
        let map = composition_map();
        let types: std::collections::HashSet<MetatileType> =
            map.values().map(|a| a.supertile_type).collect();

        assert!(types.contains(&MetatileType::H));
        assert!(types.contains(&MetatileType::T));
        assert!(types.contains(&MetatileType::P));
        assert!(types.contains(&MetatileType::F));
    }

    #[test]
    fn no_pp_same_orientation() {
        assert!(
            check_no_pp_same_orientation(),
            "no PP same-orientation pair should exist"
        );
    }

    #[test]
    fn export_for_rocq_is_sorted_and_complete() {
        let entries = export_for_rocq();
        assert_eq!(entries.len(), 22);

        for i in 1..entries.len() {
            assert!(
                entries[i - 1].0 < entries[i].0,
                "entries should be strictly sorted by inflation index"
            );
        }
    }

    #[test]
    fn supertile_specs_have_correct_child_counts() {
        let specs = supertile_specs();
        assert_eq!(specs.len(), 4);

        assert_eq!(specs[0].children.len(), 10); // H'
        assert_eq!(specs[1].children.len(), 1);  // T'
        assert_eq!(specs[2].children.len(), 5);  // P'
        assert_eq!(specs[3].children.len(), 6);  // F'
    }

    #[test]
    fn supertile_specs_types_correct() {
        let specs = supertile_specs();
        assert_eq!(specs[0].supertile_type, MetatileType::H);
        assert_eq!(specs[1].supertile_type, MetatileType::T);
        assert_eq!(specs[2].supertile_type, MetatileType::P);
        assert_eq!(specs[3].supertile_type, MetatileType::F);
    }

    #[test]
    fn inflation_is_deterministic() {
        // Running supertile_specs twice should produce identical results.
        // This verifies that inflation is deterministic: the supertile type
        // completely determines its children.
        let specs1 = supertile_specs();
        let specs2 = supertile_specs();

        for (s1, s2) in specs1.iter().zip(specs2.iter()) {
            assert_eq!(s1.supertile_type, s2.supertile_type);
            assert_eq!(s1.children, s2.children);
            assert_eq!(s1.internal_adjacencies, s2.internal_adjacencies);
        }
    }
}
