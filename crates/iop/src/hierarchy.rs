use ark_ff::Field;
use tiling::metatile::{
    inflation_rules, InflationRule, MetatileType, SUPERTILE_F_CHILDREN, SUPERTILE_H_CHILDREN,
    SUPERTILE_P_CHILDREN, SUPERTILE_T_CHILDREN,
};

use crate::types::{ChildRef, LevelOracle, TilingHierarchy};

/// Child index lists for each supertile type, in canonical order (H, T, P, F).
const SUPERTILE_CHILDREN: [&[usize]; 4] = [
    SUPERTILE_H_CHILDREN,
    SUPERTILE_T_CHILDREN,
    SUPERTILE_P_CHILDREN,
    SUPERTILE_F_CHILDREN,
];

/// Build a tiling hierarchy top-down via inflation.
///
/// Starting from a single tile of type `seed` at the top level, inflate downward
/// to produce `depth` levels. Each parent tile's children are determined by the
/// supertile composition rules and the 29 inflation rules.
///
/// Returns a `TilingHierarchy` with empty values (the prover fills level 0).
pub fn build_hierarchy<F: Field>(seed: MetatileType, depth: usize) -> TilingHierarchy<F> {
    let rules = inflation_rules();

    // Precompute child type for each of the 29 inflation rule indices
    let child_type_of = |idx: usize| -> MetatileType {
        match &rules[idx] {
            InflationRule::Seed(t) => *t,
            InflationRule::Adjacent { child_type, .. } => *child_type,
            InflationRule::Bridge { child_type, .. } => *child_type,
        }
    };

    // Build levels from top (depth) down to base (0).
    // level[depth] = single seed tile
    // level[k-1] = children of all tiles at level[k]
    let mut levels: Vec<LevelOracle<F>> = Vec::with_capacity(depth + 1);

    // Top level: single seed tile
    let top = LevelOracle {
        level: depth,
        values: vec![F::ZERO],
        tile_types: vec![seed],
        children: vec![vec![]], // will be filled when we create children
    };
    levels.push(top);

    // Inflate downward: for each level k (from depth to 1), create level k-1
    for step in 0..depth {
        let parent_level_idx = step; // index into `levels` vec
        let parent_level_num = depth - step;
        let child_level_num = parent_level_num - 1;

        // Count how many children we'll produce
        let mut child_tiles: Vec<MetatileType> = Vec::new();
        let mut parent_children: Vec<Vec<ChildRef>> = Vec::new();

        let parent_types: Vec<MetatileType> = levels[parent_level_idx].tile_types.clone();

        for parent_type in &parent_types {
            let assigned_indices = SUPERTILE_CHILDREN[parent_type.index()];
            let base_child_index = child_tiles.len();
            let mut refs = Vec::with_capacity(assigned_indices.len());

            for (local_idx, &rule_idx) in assigned_indices.iter().enumerate() {
                let ct = child_type_of(rule_idx);
                refs.push(ChildRef {
                    child_index: base_child_index + local_idx,
                    child_type: ct,
                });
                child_tiles.push(ct);
            }

            parent_children.push(refs);
        }

        // Update parent's children mapping
        levels[parent_level_idx].children = parent_children;

        // Create child level
        let child_level = LevelOracle {
            level: child_level_num,
            values: vec![F::ZERO; child_tiles.len()],
            tile_types: child_tiles,
            children: vec![], // will be filled in next iteration (or stays empty for level 0)
        };
        levels.push(child_level);
    }

    // Reverse so levels[0] = base, levels[depth] = top
    levels.reverse();

    TilingHierarchy {
        levels,
        seed,
        depth,
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use ark_bls12_381::Fr;

    #[test]
    fn hierarchy_depth_zero_is_single_tile() {
        let h = build_hierarchy::<Fr>(MetatileType::H, 0);
        assert_eq!(h.levels.len(), 1);
        assert_eq!(h.levels[0].tile_types.len(), 1);
        assert_eq!(h.levels[0].tile_types[0], MetatileType::H);
    }

    #[test]
    fn hierarchy_depth_one_matches_composition() {
        let h = build_hierarchy::<Fr>(MetatileType::H, 1);
        assert_eq!(h.levels.len(), 2);

        // Top level: 1 H tile
        assert_eq!(h.levels[1].tile_types.len(), 1);
        assert_eq!(h.levels[1].tile_types[0], MetatileType::H);

        // Base level: 10 children of H supertile
        assert_eq!(h.levels[0].tile_types.len(), 10);

        // Count types
        let mut counts = [0usize; 4];
        for t in &h.levels[0].tile_types {
            counts[t.index()] += 1;
        }
        // H' = 3H + 1T + 3P + 3F
        assert_eq!(counts, [3, 1, 3, 3]);
    }

    #[test]
    fn hierarchy_levels_have_correct_level_numbers() {
        let h = build_hierarchy::<Fr>(MetatileType::H, 3);
        for (i, level) in h.levels.iter().enumerate() {
            assert_eq!(level.level, i);
        }
    }

    #[test]
    fn parent_children_reference_valid_indices() {
        let h = build_hierarchy::<Fr>(MetatileType::H, 2);
        for k in 1..=h.depth {
            let parent = &h.levels[k];
            let child = &h.levels[k - 1];
            for refs in &parent.children {
                for r in refs {
                    assert!(
                        r.child_index < child.tile_types.len(),
                        "child_index {} out of bounds for level {} (size {})",
                        r.child_index,
                        k - 1,
                        child.tile_types.len()
                    );
                    assert_eq!(
                        r.child_type, child.tile_types[r.child_index],
                        "child type mismatch"
                    );
                }
            }
        }
    }

    #[test]
    fn hierarchy_counts_match_substitution() {
        let depth = 4;
        let h = build_hierarchy::<Fr>(MetatileType::H, depth);
        // generate_counts: level 0 = seed, level k = after k substitutions
        // hierarchy: level 0 = base (most tiles), level depth = seed (top)
        // So hierarchy level k corresponds to generate_counts level (depth - k)
        let expected = tiling::substitution::generate_counts(MetatileType::H, depth);

        for (level_idx, level) in h.levels.iter().enumerate() {
            let mut counts = [0usize; 4];
            for t in &level.tile_types {
                counts[t.index()] += 1;
            }
            let gen_level = depth - level_idx;
            assert_eq!(
                counts, expected[gen_level],
                "hierarchy level {} (= generate_counts level {}) mismatch",
                level_idx, gen_level
            );
        }
    }
}
