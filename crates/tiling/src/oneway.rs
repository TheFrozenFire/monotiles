//! One-way substitution function analysis.
//!
//! Investigates whether the hat tiling substitution exhibits computational
//! one-wayness: inflation is local (O(n)), but can deflation also be done
//! locally, or does it require global context?
//!
//! The key question: given only the MetatileTypes of tiles in a radius-r
//! neighborhood, can the center tile's parent assignment be uniquely determined?

use std::collections::{BTreeMap, HashMap, HashSet, VecDeque};

use crate::adjacency::inflation_adjacency;
use crate::metatile::{
    supertile_composition, InflationRule, MetatileType, SUPERTILE_F_CHILDREN,
    SUPERTILE_H_CHILDREN, SUPERTILE_P_CHILDREN, SUPERTILE_T_CHILDREN,
};

/// Child index lists for each supertile type, in canonical order (H, T, P, F).
const SUPERTILE_CHILDREN: [&[usize]; 4] = [
    SUPERTILE_H_CHILDREN,
    SUPERTILE_T_CHILDREN,
    SUPERTILE_P_CHILDREN,
    SUPERTILE_F_CHILDREN,
];

/// A flat hierarchy for analysis, without field elements or Merkle trees.
///
/// Built top-down from a seed tile, this captures the parent-child relationships
/// at every level. Level 0 is the base (most tiles), level `depth` is the top
/// (single seed tile).
pub struct FlatHierarchy {
    pub depth: usize,
    pub seed: MetatileType,
    /// `tile_types[level][tile_idx]` = MetatileType of that tile.
    pub tile_types: Vec<Vec<MetatileType>>,
    /// `parent_of[level][tile_idx]` = parent index at level+1.
    /// Valid for levels 0..depth-1.
    pub parent_of: Vec<Vec<usize>>,
    /// `position_in_parent[level][tile_idx]` = position within parent's child list.
    /// Valid for levels 0..depth-1.
    pub position_in_parent: Vec<Vec<usize>>,
}

/// Build a flat hierarchy top-down from seed.
///
/// Duplicates minimal logic from `iop::hierarchy::build_hierarchy` to avoid
/// a circular dependency (iop depends on tiling, not the reverse).
pub fn build_flat_hierarchy(seed: MetatileType, depth: usize) -> FlatHierarchy {
    let rules = crate::metatile::inflation_rules();
    let child_type_of = |idx: usize| -> MetatileType {
        match &rules[idx] {
            InflationRule::Seed(t) => *t,
            InflationRule::Adjacent { child_type, .. } => *child_type,
            InflationRule::Bridge { child_type, .. } => *child_type,
        }
    };

    // Build top-down: top_types[0] = top level (single seed)
    let mut top_types: Vec<Vec<MetatileType>> = Vec::with_capacity(depth + 1);
    let mut parent_maps: Vec<Vec<usize>> = Vec::new();
    let mut position_maps: Vec<Vec<usize>> = Vec::new();

    top_types.push(vec![seed]);

    for _step in 0..depth {
        let parent_types = top_types.last().unwrap();
        let mut child_tiles: Vec<MetatileType> = Vec::new();
        let mut parents: Vec<usize> = Vec::new();
        let mut positions: Vec<usize> = Vec::new();

        for (parent_idx, &parent_type) in parent_types.iter().enumerate() {
            let assigned_indices = SUPERTILE_CHILDREN[parent_type.index()];
            for (local_idx, &rule_idx) in assigned_indices.iter().enumerate() {
                child_tiles.push(child_type_of(rule_idx));
                parents.push(parent_idx);
                positions.push(local_idx);
            }
        }

        parent_maps.push(parents);
        position_maps.push(positions);
        top_types.push(child_tiles);
    }

    // Reverse so levels[0] = base, levels[depth] = top
    top_types.reverse();
    parent_maps.reverse();
    position_maps.reverse();

    FlatHierarchy {
        depth,
        seed,
        tile_types: top_types,
        parent_of: parent_maps,
        position_in_parent: position_maps,
    }
}

/// Flat parent assignment: for each tile at level k, which parent index at level k+1.
pub fn parent_assignments(seed: MetatileType, depth: usize) -> Vec<Vec<usize>> {
    build_flat_hierarchy(seed, depth).parent_of
}

/// Build adjacency graph where all siblings (same parent) are mutually adjacent.
///
/// This is the simplest adjacency model: every tile can see all its siblings
/// at radius 1. Since supertile compositions have unique type signatures,
/// this makes deflation trivially solvable at radius 1.
pub fn full_sibling_adjacency(hierarchy: &FlatHierarchy, level: usize) -> Vec<Vec<usize>> {
    assert!(level < hierarchy.depth, "level must be < depth for parent info");
    let n = hierarchy.tile_types[level].len();
    let mut adj: Vec<Vec<usize>> = vec![Vec::new(); n];

    let mut parent_groups: HashMap<usize, Vec<usize>> = HashMap::new();
    for (tile_idx, &parent_idx) in hierarchy.parent_of[level].iter().enumerate() {
        parent_groups.entry(parent_idx).or_default().push(tile_idx);
    }

    for group in parent_groups.values() {
        for &a in group {
            for &b in group {
                if a != b {
                    adj[a].push(b);
                }
            }
        }
    }

    adj
}

/// Build adjacency graph using intra-supertile inflation adjacency.
///
/// Two tiles at the given level are adjacent if they share the same parent AND
/// their corresponding inflation indices are adjacent in the inflation graph.
/// This is a stricter (sparser) adjacency than `full_sibling_adjacency`.
///
/// Note: H' supertile children are disconnected under this adjacency
/// (two components: {0,9,16,27,26,6,1,8,10,15} splits into two groups
/// connected only through boundary children not in the hierarchy).
pub fn intra_supertile_adjacency(hierarchy: &FlatHierarchy, level: usize) -> Vec<Vec<usize>> {
    assert!(level < hierarchy.depth, "level must be < depth for parent info");
    let n = hierarchy.tile_types[level].len();
    let mut adj: Vec<Vec<usize>> = vec![Vec::new(); n];

    let infl_adj = inflation_adjacency();

    // Group tiles by parent
    let mut parent_groups: HashMap<usize, Vec<usize>> = HashMap::new();
    for (tile_idx, &parent_idx) in hierarchy.parent_of[level].iter().enumerate() {
        parent_groups.entry(parent_idx).or_default().push(tile_idx);
    }

    for children in parent_groups.values() {
        let parent_idx = hierarchy.parent_of[level][children[0]];
        let parent_type = hierarchy.tile_types[level + 1][parent_idx];
        let assigned = SUPERTILE_CHILDREN[parent_type.index()];

        // Map position_in_parent -> tile_idx for this parent's children
        let mut pos_to_tile: HashMap<usize, usize> = HashMap::new();
        for &tile_idx in children {
            let pos = hierarchy.position_in_parent[level][tile_idx];
            pos_to_tile.insert(pos, tile_idx);
        }

        // Check inflation adjacency between children of the same parent
        for (&pos_a, &tile_a) in &pos_to_tile {
            let infl_idx_a = assigned[pos_a];
            for neighbor in &infl_adj.adjacencies[infl_idx_a] {
                if let Some(pos_b) = assigned.iter().position(|&x| x == neighbor.neighbor) {
                    if let Some(&tile_b) = pos_to_tile.get(&pos_b) {
                        if tile_a != tile_b && !adj[tile_a].contains(&tile_b) {
                            adj[tile_a].push(tile_b);
                        }
                    }
                }
            }
        }
    }

    adj
}

/// BFS neighborhood: all tiles reachable within `radius` hops (including the tile itself).
pub fn neighborhood(adjacency: &[Vec<usize>], tile: usize, radius: usize) -> HashSet<usize> {
    let mut visited = HashSet::new();
    let mut queue = VecDeque::new();
    queue.push_back((tile, 0usize));
    visited.insert(tile);

    while let Some((current, dist)) = queue.pop_front() {
        if dist >= radius {
            continue;
        }
        for &neighbor in &adjacency[current] {
            if visited.insert(neighbor) {
                queue.push_back((neighbor, dist + 1));
            }
        }
    }

    visited
}

/// Type signature: sorted type counts at each BFS distance shell.
///
/// Captures the local structure around a tile as seen through the adjacency graph.
/// Two tiles with identical type signatures have indistinguishable local neighborhoods
/// (up to the given radius) when only tile types are observable.
type TypeSignature = Vec<(usize, [usize; 4])>;

fn type_signature(
    hierarchy: &FlatHierarchy,
    adjacency: &[Vec<usize>],
    level: usize,
    tile: usize,
    radius: usize,
) -> TypeSignature {
    let mut visited: HashMap<usize, usize> = HashMap::new();
    let mut queue = VecDeque::new();
    queue.push_back((tile, 0usize));
    visited.insert(tile, 0);

    while let Some((current, dist)) = queue.pop_front() {
        if dist >= radius {
            continue;
        }
        for &neighbor in &adjacency[current] {
            if !visited.contains_key(&neighbor) {
                visited.insert(neighbor, dist + 1);
                queue.push_back((neighbor, dist + 1));
            }
        }
    }

    // Group by distance, count types per shell
    let mut by_distance: BTreeMap<usize, [usize; 4]> = BTreeMap::new();
    for (&tile_idx, &dist) in &visited {
        let type_idx = hierarchy.tile_types[level][tile_idx].index();
        by_distance.entry(dist).or_insert([0; 4])[type_idx] += 1;
    }

    by_distance.into_iter().collect()
}

/// Compute determination radius for every tile at a given level.
///
/// For each tile, finds the minimum BFS radius r such that its type signature
/// uniquely identifies its parent type among all tiles at that level.
/// Returns None for tiles that can't be determined within max_radius.
pub fn compute_determination_radii(
    hierarchy: &FlatHierarchy,
    adjacency: &[Vec<usize>],
    level: usize,
    max_radius: usize,
) -> Vec<Option<usize>> {
    let n = hierarchy.tile_types[level].len();
    let mut result = vec![None; n];

    for r in 0..=max_radius {
        // Compute signatures for ALL tiles at radius r
        let sigs: Vec<TypeSignature> = (0..n)
            .map(|i| type_signature(hierarchy, adjacency, level, i, r))
            .collect();

        // Group tiles by signature
        let mut groups: HashMap<&TypeSignature, Vec<usize>> = HashMap::new();
        for (i, sig) in sigs.iter().enumerate() {
            groups.entry(sig).or_default().push(i);
        }

        // Tiles in a group with uniform parent type are determined at this radius
        for tiles in groups.values() {
            let parent_types: HashSet<MetatileType> = tiles
                .iter()
                .map(|&t| {
                    let parent = hierarchy.parent_of[level][t];
                    hierarchy.tile_types[level + 1][parent]
                })
                .collect();

            if parent_types.len() == 1 {
                for &t in tiles {
                    if result[t].is_none() {
                        result[t] = Some(r);
                    }
                }
            }
        }

        if result.iter().all(|r| r.is_some()) {
            break;
        }
    }

    result
}

/// Given a bag of tile types (no positions/adjacency), count valid decompositions
/// into supertile compositions.
///
/// Due to the linear independence of the composition matrix rows, the system
/// of equations has at most one non-negative integer solution. Returns 1 if
/// a valid decomposition exists, 0 otherwise.
///
/// The composition matrix:
/// - H' = [3, 1, 3, 3]
/// - T' = [1, 0, 0, 0]
/// - P' = [2, 0, 1, 2]
/// - F' = [2, 0, 1, 3]
pub fn count_decompositions(type_counts: [usize; 4]) -> u64 {
    let [h, t, p, f] = type_counts;

    // Solving: 3*n_H + n_T + 2*n_P + 2*n_F = h
    //          n_H                           = t
    //          3*n_H +       n_P +   n_F     = p
    //          3*n_H +      2*n_P + 3*n_F    = f
    //
    // From row 2: n_H = t
    // From rows 3,4: n_F = f - 2p + 3t, n_P = 3p - 6t - f
    // From row 1: n_T = h + 3t - 2p

    // Check non-negativity using checked arithmetic
    let n_h = t;

    let n_f = match (f + 3 * t).checked_sub(2 * p) {
        Some(v) => v,
        None => return 0,
    };

    let n_p = match (3 * p).checked_sub(6 * t + f) {
        Some(v) => v,
        None => return 0,
    };

    let n_t = match (h + 3 * t).checked_sub(2 * p) {
        Some(v) => v,
        None => return 0,
    };

    // Verify round-trip (guards against overflow/logic errors)
    let check_h = 3 * n_h + n_t + 2 * n_p + 2 * n_f;
    let check_t = n_h;
    let check_p = 3 * n_h + n_p + n_f;
    let check_f = 3 * n_h + 2 * n_p + 3 * n_f;

    if check_h == h && check_t == t && check_p == p && check_f == f {
        1
    } else {
        0
    }
}

/// Greedy deflation: assign tiles to supertiles by type-count matching.
///
/// Uses only the flat list of tile types (no adjacency or position info).
/// Since the decomposition is unique when it exists, this determines the
/// exact number of each supertile type needed, then greedily assigns tiles.
///
/// Returns the per-tile parent type assignment (None if unassigned) and
/// the fraction of tiles successfully assigned.
pub fn greedy_deflate(types: &[MetatileType]) -> (Vec<Option<MetatileType>>, f64) {
    let comp = supertile_composition();
    let n = types.len();
    let mut assignments: Vec<Option<MetatileType>> = vec![None; n];
    let mut assigned = vec![false; n];

    // Compute type counts
    let mut type_counts = [0usize; 4];
    for t in types {
        type_counts[t.index()] += 1;
    }

    if count_decompositions(type_counts) == 0 {
        return (assignments, 0.0);
    }

    // Unique decomposition formula
    let [h, t, p, f] = type_counts;
    let target = [
        t,                    // n_H' = t (number of T-type tiles)
        h + 3 * t - 2 * p,   // n_T'
        3 * p - 6 * t - f,   // n_P'
        f + 3 * t - 2 * p,   // n_F'
    ];
    let supertile_types = MetatileType::all();

    let mut success = 0usize;
    for (st_idx, &st_type) in supertile_types.iter().enumerate() {
        let needed = comp[st_idx];
        for _ in 0..target[st_idx] {
            let mut found = [0usize; 4];
            let mut group = Vec::new();

            for (i, tile_type) in types.iter().enumerate() {
                if assigned[i] {
                    continue;
                }
                let ti = tile_type.index();
                if found[ti] < needed[ti] {
                    found[ti] += 1;
                    group.push(i);
                }
                if found == needed {
                    break;
                }
            }

            if found == needed {
                for &idx in &group {
                    assignments[idx] = Some(st_type);
                    assigned[idx] = true;
                    success += 1;
                }
            }
        }
    }

    let rate = if n > 0 { success as f64 / n as f64 } else { 1.0 };
    (assignments, rate)
}

/// Local deflation: use r-hop neighborhoods to resolve parent type assignment.
///
/// For each tile, computes its type signature at the given radius. If the
/// signature uniquely identifies the parent type (compared against all tiles
/// in the hierarchy), assigns that type. Otherwise marks as unresolved.
///
/// Returns (assignments, unresolved_count). Unresolved tiles get their
/// ground-truth parent type (for comparison purposes).
pub fn local_deflate(
    hierarchy: &FlatHierarchy,
    adjacency: &[Vec<usize>],
    level: usize,
    radius: usize,
) -> (Vec<MetatileType>, usize) {
    let n = hierarchy.tile_types[level].len();
    let mut assignments = Vec::with_capacity(n);
    let mut unresolved = 0;

    let sigs: Vec<TypeSignature> = (0..n)
        .map(|i| type_signature(hierarchy, adjacency, level, i, radius))
        .collect();

    // Group by signature to find unique parent types
    let mut groups: HashMap<&TypeSignature, HashSet<MetatileType>> = HashMap::new();
    for (i, sig) in sigs.iter().enumerate() {
        let parent = hierarchy.parent_of[level][i];
        let parent_type = hierarchy.tile_types[level + 1][parent];
        groups.entry(sig).or_default().insert(parent_type);
    }

    for (tile_idx, sig) in sigs.iter().enumerate() {
        let parent_types = &groups[sig];
        let parent = hierarchy.parent_of[level][tile_idx];
        let ground_truth = hierarchy.tile_types[level + 1][parent];

        if parent_types.len() == 1 {
            assignments.push(*parent_types.iter().next().unwrap());
        } else {
            assignments.push(ground_truth);
            unresolved += 1;
        }
    }

    (assignments, unresolved)
}

/// Per-level analysis results.
pub struct LevelResult {
    /// Histogram: determination radius -> number of tiles at that radius.
    pub radii_histogram: BTreeMap<usize, usize>,
    /// Tiles that couldn't be determined within max_radius.
    pub undetermined: usize,
    /// Min determination radius (None if all undetermined).
    pub min_radius: Option<usize>,
    /// Max determination radius (None if any undetermined).
    pub max_radius: Option<usize>,
    /// Mean determination radius (over determined tiles only).
    pub mean_radius: f64,
}

/// Complete one-way analysis results.
pub struct OnewayAnalysis {
    pub depth: usize,
    pub seed: MetatileType,
    pub tiles_per_level: Vec<usize>,
    /// Per-level results with full sibling adjacency (levels 0..depth-1).
    pub full_sibling: Vec<LevelResult>,
    /// Per-level results with intra-supertile inflation adjacency.
    pub inflation_adj: Vec<LevelResult>,
    /// Number of valid type-bag decompositions for the base level.
    pub base_decomposition_count: u64,
    /// Greedy deflation success rate (fraction of tiles assigned).
    pub greedy_success_rate: f64,
    /// Local deflation results at radius 1 with full sibling adjacency.
    pub local_deflate_unresolved: usize,
}

fn summarize_radii(radii: &[Option<usize>]) -> LevelResult {
    let mut hist: BTreeMap<usize, usize> = BTreeMap::new();
    let mut undetermined = 0;
    let mut sum = 0usize;
    let mut count = 0usize;

    for r in radii {
        match r {
            Some(r) => {
                *hist.entry(*r).or_insert(0) += 1;
                sum += r;
                count += 1;
            }
            None => undetermined += 1,
        }
    }

    let min_radius = hist.keys().next().copied();
    let max_radius = if undetermined == 0 {
        hist.keys().last().copied()
    } else {
        None
    };
    let mean_radius = if count > 0 {
        sum as f64 / count as f64
    } else {
        f64::NAN
    };

    LevelResult {
        radii_histogram: hist,
        undetermined,
        min_radius,
        max_radius,
        mean_radius,
    }
}

/// Run the full one-way substitution analysis.
pub fn analyze(seed: MetatileType, depth: usize, max_radius: usize) -> OnewayAnalysis {
    let hierarchy = build_flat_hierarchy(seed, depth);

    let tiles_per_level: Vec<usize> = hierarchy.tile_types.iter().map(|v| v.len()).collect();

    let mut full_sibling = Vec::new();
    let mut inflation_adj_results = Vec::new();

    for level in 0..depth {
        // Full sibling adjacency analysis
        let fs_adj = full_sibling_adjacency(&hierarchy, level);
        let fs_radii = compute_determination_radii(&hierarchy, &fs_adj, level, max_radius);
        full_sibling.push(summarize_radii(&fs_radii));

        // Intra-supertile inflation adjacency analysis
        let is_adj = intra_supertile_adjacency(&hierarchy, level);
        let is_radii = compute_determination_radii(&hierarchy, &is_adj, level, max_radius);
        inflation_adj_results.push(summarize_radii(&is_radii));
    }

    // Base-level decomposition count
    let mut base_type_counts = [0usize; 4];
    for t in &hierarchy.tile_types[0] {
        base_type_counts[t.index()] += 1;
    }
    let base_decomposition_count = count_decompositions(base_type_counts);

    // Greedy deflation on base level
    let (_, greedy_success_rate) = greedy_deflate(&hierarchy.tile_types[0]);

    // Local deflation at radius 1 with full sibling adjacency
    let local_deflate_unresolved = if depth > 0 {
        let fs_adj = full_sibling_adjacency(&hierarchy, 0);
        let (_, unresolved) = local_deflate(&hierarchy, &fs_adj, 0, 1);
        unresolved
    } else {
        0
    };

    OnewayAnalysis {
        depth,
        seed,
        tiles_per_level,
        full_sibling,
        inflation_adj: inflation_adj_results,
        base_decomposition_count,
        greedy_success_rate,
        local_deflate_unresolved,
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn ground_truth_matches_generate_counts() {
        let depth = 4;
        let hierarchy = build_flat_hierarchy(MetatileType::H, depth);
        let expected = crate::substitution::generate_counts(MetatileType::H, depth);

        for (level_idx, level_types) in hierarchy.tile_types.iter().enumerate() {
            let mut counts = [0usize; 4];
            for t in level_types {
                counts[t.index()] += 1;
            }
            // hierarchy level k corresponds to generate_counts level (depth - k)
            let gen_level = depth - level_idx;
            assert_eq!(
                counts, expected[gen_level],
                "hierarchy level {} (gen level {}) mismatch",
                level_idx, gen_level
            );
        }
    }

    #[test]
    fn full_sibling_adjacency_is_symmetric() {
        let hierarchy = build_flat_hierarchy(MetatileType::H, 2);
        let adj = full_sibling_adjacency(&hierarchy, 0);

        for (i, neighbors) in adj.iter().enumerate() {
            for &j in neighbors {
                assert!(
                    adj[j].contains(&i),
                    "full sibling adjacency: {}->{} but not {}<-{}",
                    i, j, j, i
                );
            }
        }
    }

    #[test]
    fn intra_supertile_adjacency_is_symmetric() {
        let hierarchy = build_flat_hierarchy(MetatileType::H, 2);
        let adj = intra_supertile_adjacency(&hierarchy, 0);

        for (i, neighbors) in adj.iter().enumerate() {
            for &j in neighbors {
                assert!(
                    adj[j].contains(&i),
                    "intra-supertile adjacency: {}->{} but not {}<-{}",
                    i, j, j, i
                );
            }
        }
    }

    #[test]
    fn determination_radius_at_depth_1() {
        // At depth 1, there's exactly 1 parent. Every tile's parent is trivially
        // determined at radius 0.
        let hierarchy = build_flat_hierarchy(MetatileType::H, 1);
        let adj = full_sibling_adjacency(&hierarchy, 0);
        let radii = compute_determination_radii(&hierarchy, &adj, 0, 5);

        for (i, r) in radii.iter().enumerate() {
            assert_eq!(
                *r,
                Some(0),
                "tile {} at depth 1 should be determined at radius 0",
                i
            );
        }
    }

    #[test]
    fn decomposition_count_single_supertile() {
        // Each supertile's composition has exactly 1 decomposition (itself)
        let comp = supertile_composition();
        for row in &comp {
            assert_eq!(
                count_decompositions(*row),
                1,
                "single supertile composition {:?} should have exactly 1 decomposition",
                row
            );
        }
    }

    #[test]
    fn decomposition_count_zero_for_invalid() {
        // A type-bag that can't form any valid supertile grouping
        assert_eq!(count_decompositions([0, 0, 0, 1]), 0);
        assert_eq!(count_decompositions([0, 1, 0, 0]), 0);
    }

    #[test]
    fn decomposition_uniqueness_from_hierarchy() {
        // The base level of any valid hierarchy should have exactly 1 decomposition
        for depth in 1..=3 {
            let hierarchy = build_flat_hierarchy(MetatileType::H, depth);
            let mut counts = [0usize; 4];
            for t in &hierarchy.tile_types[0] {
                counts[t.index()] += 1;
            }
            assert_eq!(
                count_decompositions(counts),
                1,
                "depth {} base level should have exactly 1 decomposition",
                depth
            );
        }
    }

    #[test]
    fn greedy_deflate_full_assignment() {
        // On a valid hierarchy's base level, greedy should assign all tiles
        let hierarchy = build_flat_hierarchy(MetatileType::H, 2);
        let (assignments, rate) = greedy_deflate(&hierarchy.tile_types[0]);

        assert!(
            (rate - 1.0).abs() < 1e-10,
            "greedy deflation should assign all tiles, got rate {}",
            rate
        );
        for (i, a) in assignments.iter().enumerate() {
            assert!(
                a.is_some(),
                "tile {} should be assigned by greedy deflation",
                i
            );
        }
    }

    #[test]
    fn neighborhood_radius_zero_is_self() {
        let adj = vec![vec![1, 2], vec![0], vec![0]];
        let hood = neighborhood(&adj, 0, 0);
        assert_eq!(hood, HashSet::from([0]));
    }

    #[test]
    fn neighborhood_radius_one() {
        let adj = vec![vec![1, 2], vec![0, 2], vec![0, 1]];
        let hood = neighborhood(&adj, 0, 1);
        assert_eq!(hood, HashSet::from([0, 1, 2]));
    }

    #[test]
    fn parent_of_is_valid() {
        let hierarchy = build_flat_hierarchy(MetatileType::H, 3);
        for level in 0..hierarchy.depth {
            let num_children = hierarchy.tile_types[level].len();
            let num_parents = hierarchy.tile_types[level + 1].len();
            for tile in 0..num_children {
                let parent = hierarchy.parent_of[level][tile];
                assert!(
                    parent < num_parents,
                    "level {} tile {} parent {} out of bounds (max {})",
                    level, tile, parent, num_parents
                );
            }
        }
    }

    #[test]
    fn full_sibling_determines_all_at_depth_2() {
        // With full sibling adjacency, all tiles at depth 2 should be
        // determined at radius <= 1.
        let hierarchy = build_flat_hierarchy(MetatileType::H, 2);
        let adj = full_sibling_adjacency(&hierarchy, 0);
        let radii = compute_determination_radii(&hierarchy, &adj, 0, 5);

        for (i, r) in radii.iter().enumerate() {
            assert!(
                r.is_some() && r.unwrap() <= 1,
                "tile {} should be determined at radius <= 1, got {:?}",
                i, r
            );
        }
    }
}
