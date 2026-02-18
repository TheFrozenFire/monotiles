//! One-way substitution function analysis.
//!
//! Investigates whether tiling substitutions exhibit computational
//! one-wayness: inflation is local (O(n)), but can deflation also be done
//! locally, or does it require global context?
//!
//! The key question: given only the type indices of tiles in a radius-r
//! neighborhood, can the center tile's parent assignment be uniquely determined?

use std::collections::{BTreeMap, HashMap, HashSet, VecDeque};

use crate::metatile::MetatileType;
use crate::systems::hat::HatSystem;
use crate::systems::TilingSystem;

/// A flat hierarchy for analysis, without field elements or Merkle trees.
///
/// Built top-down from a seed tile, this captures the parent-child relationships
/// at every level. Level 0 is the base (most tiles), level `depth` is the top
/// (single seed tile).
pub struct FlatHierarchy {
    pub depth: usize,
    pub seed_type: usize,
    pub num_types: usize,
    /// `tile_types[level][tile_idx]` = type index of that tile.
    pub tile_types: Vec<Vec<usize>>,
    /// `parent_of[level][tile_idx]` = parent index at level+1.
    /// Valid for levels 0..depth-1.
    pub parent_of: Vec<Vec<usize>>,
    /// `position_in_parent[level][tile_idx]` = position within parent's child list.
    /// Valid for levels 0..depth-1.
    pub position_in_parent: Vec<Vec<usize>>,
}

/// Build a flat hierarchy top-down from seed, using the given tiling system.
pub fn build_hierarchy(
    system: &dyn TilingSystem,
    seed: usize,
    depth: usize,
) -> FlatHierarchy {
    let num_types = system.num_types();

    // Build top-down: top_types[0] = top level (single seed)
    let mut top_types: Vec<Vec<usize>> = Vec::with_capacity(depth + 1);
    let mut parent_maps: Vec<Vec<usize>> = Vec::new();
    let mut position_maps: Vec<Vec<usize>> = Vec::new();

    top_types.push(vec![seed]);

    for _step in 0..depth {
        let parent_types = top_types.last().unwrap();
        let mut child_tiles: Vec<usize> = Vec::new();
        let mut parents: Vec<usize> = Vec::new();
        let mut positions: Vec<usize> = Vec::new();

        for (parent_idx, &parent_type) in parent_types.iter().enumerate() {
            let assigned_indices = system.supertile_children(parent_type);
            for (local_idx, &rule_idx) in assigned_indices.iter().enumerate() {
                child_tiles.push(system.inflation_child_type(rule_idx));
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
        seed_type: seed,
        num_types,
        tile_types: top_types,
        parent_of: parent_maps,
        position_in_parent: position_maps,
    }
}

/// Build a flat hierarchy using the hat tiling system.
pub fn build_flat_hierarchy(seed: MetatileType, depth: usize) -> FlatHierarchy {
    build_hierarchy(&HatSystem::new(), seed.index(), depth)
}

/// Flat parent assignment: for each tile at level k, which parent index at level k+1.
pub fn parent_assignments(seed: MetatileType, depth: usize) -> Vec<Vec<usize>> {
    build_flat_hierarchy(seed, depth).parent_of
}

/// Build adjacency graph where all siblings (same parent) are mutually adjacent.
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
/// their corresponding inflation indices are adjacent in the system's inflation graph.
pub fn intra_supertile_adjacency(
    system: &dyn TilingSystem,
    hierarchy: &FlatHierarchy,
    level: usize,
) -> Vec<Vec<usize>> {
    assert!(level < hierarchy.depth, "level must be < depth for parent info");
    let n = hierarchy.tile_types[level].len();
    let mut adj: Vec<Vec<usize>> = vec![Vec::new(); n];

    let infl_adj = system.inflation_adjacency();

    // Group tiles by parent
    let mut parent_groups: HashMap<usize, Vec<usize>> = HashMap::new();
    for (tile_idx, &parent_idx) in hierarchy.parent_of[level].iter().enumerate() {
        parent_groups.entry(parent_idx).or_default().push(tile_idx);
    }

    for children in parent_groups.values() {
        let parent_idx = hierarchy.parent_of[level][children[0]];
        let parent_type = hierarchy.tile_types[level + 1][parent_idx];
        let assigned = system.supertile_children(parent_type);

        // Map position_in_parent -> tile_idx for this parent's children
        let mut pos_to_tile: HashMap<usize, usize> = HashMap::new();
        for &tile_idx in children {
            let pos = hierarchy.position_in_parent[level][tile_idx];
            pos_to_tile.insert(pos, tile_idx);
        }

        // Check inflation adjacency between children of the same parent
        for (&pos_a, &tile_a) in &pos_to_tile {
            let infl_idx_a = assigned[pos_a];
            for &neighbor in &infl_adj[infl_idx_a] {
                if let Some(pos_b) = assigned.iter().position(|&x| x == neighbor) {
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

/// Backward-compatible wrapper: intra-supertile adjacency using the hat system.
#[cfg(test)]
fn hat_intra_supertile_adjacency(hierarchy: &FlatHierarchy, level: usize) -> Vec<Vec<usize>> {
    intra_supertile_adjacency(&HatSystem::new(), hierarchy, level)
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
pub(crate) type TypeSignature = Vec<(usize, Vec<usize>)>;

pub(crate) fn type_signature(
    hierarchy: &FlatHierarchy,
    adjacency: &[Vec<usize>],
    level: usize,
    tile: usize,
    radius: usize,
) -> TypeSignature {
    let num_types = hierarchy.num_types;
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
    let mut by_distance: BTreeMap<usize, Vec<usize>> = BTreeMap::new();
    for (&tile_idx, &dist) in &visited {
        let type_idx = hierarchy.tile_types[level][tile_idx];
        let entry = by_distance.entry(dist).or_insert_with(|| vec![0; num_types]);
        entry[type_idx] += 1;
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
            let parent_types: HashSet<usize> = tiles
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
/// into supertile compositions using the given system.
///
/// For systems with invertible composition matrices (hat: det=-1, spectre: det=1),
/// the decomposition is unique when it exists.
pub fn count_decompositions(system: &dyn TilingSystem, type_counts: &[usize]) -> u64 {
    let composition = system.composition();
    let n = system.num_types();
    assert_eq!(type_counts.len(), n);

    // Solve M^T * x = type_counts via Gaussian elimination
    let mut mat: Vec<Vec<i64>> = vec![vec![0; n + 1]; n];
    for i in 0..n {
        for j in 0..n {
            mat[i][j] = composition[j][i] as i64; // M^T[i][j] = composition[j][i]
        }
        mat[i][n] = type_counts[i] as i64;
    }

    // Forward elimination
    for col in 0..n {
        let pivot_row = match (col..n).find(|&r| mat[r][col] != 0) {
            Some(r) => r,
            None => return 0, // Singular
        };
        mat.swap(col, pivot_row);

        let pivot = mat[col][col];
        for row in (col + 1)..n {
            let factor = mat[row][col];
            if factor == 0 {
                continue;
            }
            for j in col..=n {
                mat[row][j] = mat[row][j] * pivot - mat[col][j] * factor;
            }
        }
    }

    // Back-substitution
    let mut x = vec![0i64; n];
    for i in (0..n).rev() {
        let mut sum = mat[i][n];
        for j in (i + 1)..n {
            sum -= mat[i][j] * x[j];
        }
        if mat[i][i] == 0 {
            return 0;
        }
        if sum % mat[i][i] != 0 {
            return 0;
        }
        x[i] = sum / mat[i][i];
        if x[i] < 0 {
            return 0;
        }
    }

    // Verify round-trip
    for j in 0..n {
        let mut check: i64 = 0;
        for i in 0..n {
            check += x[i] * composition[i][j] as i64;
        }
        if check != type_counts[j] as i64 {
            return 0;
        }
    }

    1
}

/// Hat-specific decomposition count (backward compatible).
pub fn count_decompositions_hat(type_counts: [usize; 4]) -> u64 {
    count_decompositions(&HatSystem::new(), &type_counts)
}

/// Greedy deflation: assign tiles to supertiles by type-count matching.
///
/// Uses only the flat list of tile types (no adjacency or position info).
pub fn greedy_deflate(
    system: &dyn TilingSystem,
    type_indices: &[usize],
) -> (Vec<Option<usize>>, f64) {
    let comp = system.composition();
    let n = type_indices.len();
    let num_types = system.num_types();
    let mut assignments: Vec<Option<usize>> = vec![None; n];
    let mut assigned = vec![false; n];

    // Compute type counts
    let mut type_counts = vec![0usize; num_types];
    for &t in type_indices {
        type_counts[t] += 1;
    }

    if count_decompositions(system, &type_counts) == 0 {
        return (assignments, 0.0);
    }

    // Solve for number of each supertile type needed
    let target = solve_supertile_counts(system, &type_counts);
    let target = match target {
        Some(t) => t,
        None => return (assignments, 0.0),
    };

    let mut success = 0usize;
    for st_idx in 0..num_types {
        let needed = &comp[st_idx];
        for _ in 0..target[st_idx] {
            let mut found = vec![0usize; num_types];
            let mut group = Vec::new();

            for (i, &tile_type) in type_indices.iter().enumerate() {
                if assigned[i] {
                    continue;
                }
                if found[tile_type] < needed[tile_type] {
                    found[tile_type] += 1;
                    group.push(i);
                }
                if found == *needed {
                    break;
                }
            }

            if found == *needed {
                for &idx in &group {
                    assignments[idx] = Some(st_idx);
                    assigned[idx] = true;
                    success += 1;
                }
            }
        }
    }

    let rate = if n > 0 { success as f64 / n as f64 } else { 1.0 };
    (assignments, rate)
}

/// Hat-specific greedy deflation (backward compatible).
pub fn greedy_deflate_hat(types: &[MetatileType]) -> (Vec<Option<MetatileType>>, f64) {
    let indices: Vec<usize> = types.iter().map(|t| t.index()).collect();
    let (assignments, rate) = greedy_deflate(&HatSystem::new(), &indices);
    let converted = assignments
        .iter()
        .map(|a| a.map(|i| MetatileType::all()[i]))
        .collect();
    (converted, rate)
}

/// Solve for the number of each supertile type given tile counts.
fn solve_supertile_counts(system: &dyn TilingSystem, type_counts: &[usize]) -> Option<Vec<usize>> {
    let composition = system.composition();
    let n = system.num_types();

    let mut mat: Vec<Vec<i64>> = vec![vec![0; n + 1]; n];
    for i in 0..n {
        for j in 0..n {
            mat[i][j] = composition[j][i] as i64;
        }
        mat[i][n] = type_counts[i] as i64;
    }

    for col in 0..n {
        let pivot_row = (col..n).find(|&r| mat[r][col] != 0)?;
        mat.swap(col, pivot_row);
        let pivot = mat[col][col];
        for row in (col + 1)..n {
            let factor = mat[row][col];
            if factor == 0 {
                continue;
            }
            for j in col..=n {
                mat[row][j] = mat[row][j] * pivot - mat[col][j] * factor;
            }
        }
    }

    let mut x = vec![0i64; n];
    for i in (0..n).rev() {
        let mut sum = mat[i][n];
        for j in (i + 1)..n {
            sum -= mat[i][j] * x[j];
        }
        if mat[i][i] == 0 || sum % mat[i][i] != 0 {
            return None;
        }
        x[i] = sum / mat[i][i];
        if x[i] < 0 {
            return None;
        }
    }

    Some(x.iter().map(|&v| v as usize).collect())
}

/// Local deflation: use r-hop neighborhoods to resolve parent type assignment.
pub fn local_deflate(
    hierarchy: &FlatHierarchy,
    adjacency: &[Vec<usize>],
    level: usize,
    radius: usize,
) -> (Vec<usize>, usize) {
    let n = hierarchy.tile_types[level].len();
    let mut assignments = Vec::with_capacity(n);
    let mut unresolved = 0;

    let sigs: Vec<TypeSignature> = (0..n)
        .map(|i| type_signature(hierarchy, adjacency, level, i, radius))
        .collect();

    // Group by signature to find unique parent types
    let mut groups: HashMap<&TypeSignature, HashSet<usize>> = HashMap::new();
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
    pub radii_histogram: BTreeMap<usize, usize>,
    pub undetermined: usize,
    pub min_radius: Option<usize>,
    pub max_radius: Option<usize>,
    pub mean_radius: f64,
}

/// Complete one-way analysis results.
pub struct OnewayAnalysis {
    pub depth: usize,
    pub seed_type: usize,
    pub tiles_per_level: Vec<usize>,
    pub full_sibling: Vec<LevelResult>,
    pub inflation_adj: Vec<LevelResult>,
    pub base_decomposition_count: u64,
    pub greedy_success_rate: f64,
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

/// Run the full one-way substitution analysis for a given tiling system.
pub fn analyze_system(
    system: &dyn TilingSystem,
    seed: usize,
    depth: usize,
    max_radius: usize,
) -> OnewayAnalysis {
    let hierarchy = build_hierarchy(system, seed, depth);

    let tiles_per_level: Vec<usize> = hierarchy.tile_types.iter().map(|v| v.len()).collect();

    let mut full_sibling = Vec::new();
    let mut inflation_adj_results = Vec::new();

    for level in 0..depth {
        let fs_adj = full_sibling_adjacency(&hierarchy, level);
        let fs_radii = compute_determination_radii(&hierarchy, &fs_adj, level, max_radius);
        full_sibling.push(summarize_radii(&fs_radii));

        let is_adj = intra_supertile_adjacency(system, &hierarchy, level);
        let is_radii = compute_determination_radii(&hierarchy, &is_adj, level, max_radius);
        inflation_adj_results.push(summarize_radii(&is_radii));
    }

    // Base-level decomposition count
    let mut base_type_counts = vec![0usize; system.num_types()];
    for &t in &hierarchy.tile_types[0] {
        base_type_counts[t] += 1;
    }
    let base_decomposition_count = count_decompositions(system, &base_type_counts);

    // Greedy deflation on base level
    let (_, greedy_success_rate) = greedy_deflate(system, &hierarchy.tile_types[0]);

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
        seed_type: seed,
        tiles_per_level,
        full_sibling,
        inflation_adj: inflation_adj_results,
        base_decomposition_count,
        greedy_success_rate,
        local_deflate_unresolved,
    }
}

/// Hat-specific analyze (backward compatible).
pub fn analyze(seed: MetatileType, depth: usize, max_radius: usize) -> OnewayAnalysis {
    analyze_system(&HatSystem::new(), seed.index(), depth, max_radius)
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
            for &t in level_types {
                counts[t] += 1;
            }
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
        let adj = hat_intra_supertile_adjacency(&hierarchy, 0);

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
        let comp = crate::metatile::supertile_composition();
        let system = HatSystem::new();
        for row in &comp {
            assert_eq!(
                count_decompositions(&system, &row[..]),
                1,
                "single supertile composition {:?} should have exactly 1 decomposition",
                row
            );
        }
    }

    #[test]
    fn decomposition_count_zero_for_invalid() {
        let system = HatSystem::new();
        assert_eq!(count_decompositions(&system, &[0, 0, 0, 1]), 0);
        assert_eq!(count_decompositions(&system, &[0, 1, 0, 0]), 0);
    }

    #[test]
    fn decomposition_uniqueness_from_hierarchy() {
        let system = HatSystem::new();
        for depth in 1..=3 {
            let hierarchy = build_flat_hierarchy(MetatileType::H, depth);
            let mut counts = vec![0usize; 4];
            for &t in &hierarchy.tile_types[0] {
                counts[t] += 1;
            }
            assert_eq!(
                count_decompositions(&system, &counts),
                1,
                "depth {} base level should have exactly 1 decomposition",
                depth
            );
        }
    }

    #[test]
    fn greedy_deflate_full_assignment() {
        let system = HatSystem::new();
        let hierarchy = build_flat_hierarchy(MetatileType::H, 2);
        let (assignments, rate) = greedy_deflate(&system, &hierarchy.tile_types[0]);

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

    // --- Scale tests (~142K base tiles, ~320x the depth-3 baseline) ---

    const LARGE_DEPTH: usize = 6;

    fn assert_hierarchy_counts(seed: MetatileType, depth: usize) {
        let hierarchy = build_flat_hierarchy(seed, depth);
        let expected = crate::substitution::generate_counts(seed, depth);
        for (level_idx, level_types) in hierarchy.tile_types.iter().enumerate() {
            let mut counts = [0usize; 4];
            for &t in level_types {
                counts[t] += 1;
            }
            let gen_level = depth - level_idx;
            assert_eq!(
                counts, expected[gen_level],
                "seed {:?} depth {} hierarchy level {} mismatch",
                seed, depth, level_idx
            );
        }
    }

    fn assert_decomposition_unique_all_levels(seed: MetatileType, depth: usize) {
        let system = HatSystem::new();
        let hierarchy = build_flat_hierarchy(seed, depth);
        for level in 0..=depth {
            let mut counts = vec![0usize; 4];
            for &t in &hierarchy.tile_types[level] {
                counts[t] += 1;
            }
            if level < depth {
                assert_eq!(
                    count_decompositions(&system, &counts),
                    1,
                    "seed {:?} depth {} level {} should have unique decomposition",
                    seed, depth, level
                );
            }
        }
    }

    #[test]
    fn large_hierarchy_counts() {
        assert_hierarchy_counts(MetatileType::H, LARGE_DEPTH);
    }

    #[test]
    fn large_decomposition_unique() {
        assert_decomposition_unique_all_levels(MetatileType::H, LARGE_DEPTH);
    }

    #[test]
    fn large_greedy_deflate_succeeds() {
        let system = HatSystem::new();
        let hierarchy = build_flat_hierarchy(MetatileType::H, LARGE_DEPTH);
        let (assignments, rate) = greedy_deflate(&system, &hierarchy.tile_types[0]);
        assert!(
            (rate - 1.0).abs() < 1e-10,
            "greedy deflation at depth {} should assign all {} tiles, got rate {}",
            LARGE_DEPTH,
            hierarchy.tile_types[0].len(),
            rate
        );
        assert!(assignments.iter().all(|a| a.is_some()));
    }

    #[test]
    fn large_full_sibling_all_determined_radius_1() {
        let hierarchy = build_flat_hierarchy(MetatileType::H, LARGE_DEPTH);
        for level in 0..LARGE_DEPTH {
            let adj = full_sibling_adjacency(&hierarchy, level);
            let radii = compute_determination_radii(&hierarchy, &adj, level, 1);
            let undetermined = radii.iter().filter(|r| r.is_none()).count();
            let max_r = radii.iter().filter_map(|r| *r).max().unwrap_or(0);
            assert_eq!(
                undetermined, 0,
                "level {} ({} tiles): {} undetermined",
                level,
                hierarchy.tile_types[level].len(),
                undetermined
            );
            assert!(
                max_r <= 1,
                "level {} max determination radius {} > 1",
                level, max_r
            );
        }
    }

    #[test]
    fn large_inflation_adj_all_determined_radius_4() {
        let hierarchy = build_flat_hierarchy(MetatileType::H, LARGE_DEPTH);
        let adj = hat_intra_supertile_adjacency(&hierarchy, 0);
        let radii = compute_determination_radii(&hierarchy, &adj, 0, 5);
        let undetermined = radii.iter().filter(|r| r.is_none()).count();
        let max_r = radii.iter().filter_map(|r| *r).max().unwrap_or(0);
        assert_eq!(
            undetermined, 0,
            "base level ({} tiles): {} undetermined with inflation adj",
            hierarchy.tile_types[0].len(),
            undetermined
        );
        assert!(
            max_r <= 4,
            "base level max inflation-adj determination radius {} > 4",
            max_r
        );
    }

    #[test]
    fn large_local_deflate_resolves_all() {
        let hierarchy = build_flat_hierarchy(MetatileType::H, LARGE_DEPTH);
        let adj = full_sibling_adjacency(&hierarchy, 0);
        let (_, unresolved) = local_deflate(&hierarchy, &adj, 0, 1);
        assert_eq!(
            unresolved, 0,
            "local deflate at radius 1 should resolve all {} base tiles",
            hierarchy.tile_types[0].len()
        );
    }

    #[test]
    fn large_determination_radius_distribution_stable() {
        let hierarchy = build_flat_hierarchy(MetatileType::H, LARGE_DEPTH);
        let adj = full_sibling_adjacency(&hierarchy, 0);
        let radii = compute_determination_radii(&hierarchy, &adj, 0, 1);

        let n = radii.len() as f64;
        let at_r0 = radii.iter().filter(|r| **r == Some(0)).count() as f64;
        let fraction_r0 = at_r0 / n;

        let mut type_counts = [0usize; 4];
        for &t in &hierarchy.tile_types[0] {
            type_counts[t] += 1;
        }
        let t_fraction = type_counts[1] as f64 / n;

        assert!(
            (fraction_r0 - t_fraction).abs() < 0.01,
            "fraction at radius 0 ({:.4}) should match T-type fraction ({:.4})",
            fraction_r0, t_fraction
        );
    }

    // --- All seeds test (verify properties are seed-independent) ---

    #[test]
    fn all_seeds_decomposition_unique_depth_4() {
        for seed in MetatileType::all() {
            assert_decomposition_unique_all_levels(seed, 4);
        }
    }

    #[test]
    fn all_seeds_full_sibling_radius_1_depth_4() {
        for seed in MetatileType::all() {
            let hierarchy = build_flat_hierarchy(seed, 4);
            for level in 0..4 {
                let adj = full_sibling_adjacency(&hierarchy, level);
                let radii = compute_determination_radii(&hierarchy, &adj, level, 1);
                let undetermined = radii.iter().filter(|r| r.is_none()).count();
                assert_eq!(
                    undetermined, 0,
                    "seed {:?} depth 4 level {}: {} undetermined with full sibling adj",
                    seed, level, undetermined
                );
            }
        }
    }

    #[test]
    fn all_seeds_greedy_deflate_depth_4() {
        let system = HatSystem::new();
        for seed in MetatileType::all() {
            let hierarchy = build_flat_hierarchy(seed, 4);
            let (_, rate) = greedy_deflate(&system, &hierarchy.tile_types[0]);
            assert!(
                (rate - 1.0).abs() < 1e-10,
                "seed {:?} depth 4: greedy rate {}",
                seed, rate
            );
        }
    }

    // --- Extra-large scale tests (~974K base tiles, ~2200x baseline) ---

    const XLARGE_DEPTH: usize = 7;

    #[test]
    #[ignore] // ~974K tiles, takes ~40s in release
    fn xlarge_hierarchy_counts() {
        assert_hierarchy_counts(MetatileType::H, XLARGE_DEPTH);
    }

    #[test]
    #[ignore]
    fn xlarge_decomposition_unique() {
        assert_decomposition_unique_all_levels(MetatileType::H, XLARGE_DEPTH);
    }

    #[test]
    #[ignore]
    fn xlarge_greedy_deflate_succeeds() {
        let system = HatSystem::new();
        let hierarchy = build_flat_hierarchy(MetatileType::H, XLARGE_DEPTH);
        let n = hierarchy.tile_types[0].len();
        let (assignments, rate) = greedy_deflate(&system, &hierarchy.tile_types[0]);
        assert!(
            (rate - 1.0).abs() < 1e-10,
            "greedy deflation at depth {} should assign all {} tiles, got rate {}",
            XLARGE_DEPTH, n, rate
        );
        assert!(assignments.iter().all(|a| a.is_some()));
    }

    #[test]
    #[ignore]
    fn xlarge_full_sibling_all_determined_radius_1() {
        let hierarchy = build_flat_hierarchy(MetatileType::H, XLARGE_DEPTH);
        for level in 0..XLARGE_DEPTH {
            let adj = full_sibling_adjacency(&hierarchy, level);
            let radii = compute_determination_radii(&hierarchy, &adj, level, 1);
            let undetermined = radii.iter().filter(|r| r.is_none()).count();
            assert_eq!(
                undetermined, 0,
                "level {} ({} tiles): {} undetermined",
                level,
                hierarchy.tile_types[level].len(),
                undetermined
            );
        }
    }

    #[test]
    #[ignore]
    fn xlarge_inflation_adj_all_determined_radius_4() {
        let hierarchy = build_flat_hierarchy(MetatileType::H, XLARGE_DEPTH);
        let adj = hat_intra_supertile_adjacency(&hierarchy, 0);
        let radii = compute_determination_radii(&hierarchy, &adj, 0, 5);
        let undetermined = radii.iter().filter(|r| r.is_none()).count();
        let max_r = radii.iter().filter_map(|r| *r).max().unwrap_or(0);
        assert_eq!(
            undetermined, 0,
            "base level ({} tiles): {} undetermined",
            hierarchy.tile_types[0].len(),
            undetermined
        );
        assert_eq!(max_r, 4, "expected max radius 4 at xlarge scale");
    }
}
