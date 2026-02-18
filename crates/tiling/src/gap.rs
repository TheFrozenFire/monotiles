//! Local-to-global gap analysis for aperiodic monotile tilings.
//!
//! Measures the gap between local indistinguishability (any finite patch appears
//! in every valid tiling) and global rigidity (the tiling is uniquely determined
//! by its seed). For each BFS radius, we measure what fraction of tiles can
//! determine which seed generated their tiling based on local neighborhood
//! information alone.

use std::collections::{HashMap, HashSet};

use tracing::info;

use crate::oneway::{
    build_hierarchy, cross_supertile_adjacency, full_sibling_adjacency, type_signature,
    FlatHierarchy, TypeSignature,
};
use crate::systems::TilingSystem;

// ---------------------------------------------------------------------------
// Multi-level ancestry
// ---------------------------------------------------------------------------

/// Walk up the parent chain from a tile at level 0 to the given target level.
fn ancestor_at_level(hierarchy: &FlatHierarchy, tile: usize, target_level: usize) -> usize {
    let mut current = tile;
    for level in 0..target_level {
        current = hierarchy.parent_of[level][current];
    }
    current
}

/// Summary of ancestry determination at one hierarchy level.
pub struct AncestryLevelResult {
    pub target_level: usize,
    pub tiles_total: usize,
    pub tiles_determined: usize,
    pub min_radius: Option<usize>,
    pub max_radius: Option<usize>,
    pub mean_radius: f64,
}

/// Compute the minimum BFS radius to determine each tile's ancestor type
/// at every hierarchy level.
///
/// Returns `[level_idx][tile]` where `level_idx` 0 = target level 1 (parent),
/// level_idx 1 = target level 2 (grandparent), etc. Each entry is the minimum
/// radius, or None if undetermined within `max_radius`.
pub fn compute_ancestry_radii(
    hierarchy: &FlatHierarchy,
    adjacency: &[Vec<usize>],
    max_radius: usize,
) -> Vec<Vec<Option<usize>>> {
    let n = hierarchy.tile_types[0].len();
    let depth = hierarchy.depth;
    let mut results: Vec<Vec<Option<usize>>> = vec![vec![None; n]; depth];

    for r in 0..=max_radius {
        let sigs: Vec<TypeSignature> = (0..n)
            .map(|i| type_signature(hierarchy, adjacency, 0, i, r))
            .collect();

        let mut groups: HashMap<&TypeSignature, Vec<usize>> = HashMap::new();
        for (i, sig) in sigs.iter().enumerate() {
            groups.entry(sig).or_default().push(i);
        }

        for target_level in 1..=depth {
            let level_idx = target_level - 1;
            if results[level_idx].iter().all(|v| v.is_some()) {
                continue;
            }

            for tiles in groups.values() {
                let ancestor_types: HashSet<usize> = tiles
                    .iter()
                    .map(|&t| {
                        let ancestor = ancestor_at_level(hierarchy, t, target_level);
                        hierarchy.tile_types[target_level][ancestor]
                    })
                    .collect();

                if ancestor_types.len() == 1 {
                    for &t in tiles {
                        if results[level_idx][t].is_none() {
                            results[level_idx][t] = Some(r);
                        }
                    }
                }
            }
        }

        if results
            .iter()
            .all(|level| level.iter().all(|v| v.is_some()))
        {
            break;
        }
    }

    results
}

// ---------------------------------------------------------------------------
// Hierarchical signature
// ---------------------------------------------------------------------------

/// Ancestor type chain: the types at levels 0, 1, ..., min(radius, depth).
///
/// At radius 0, just the tile's own type. At radius r, the chain of ancestor
/// types up to level r. At radius >= depth, the full chain including the seed.
/// This is the natural "what can you see at hierarchical distance r" measure:
/// each additional radius step reveals one more level of the hierarchy.
type HierarchicalSignature = Vec<usize>;

fn hierarchical_signature(
    hierarchy: &FlatHierarchy,
    tile: usize,
    radius: usize,
) -> HierarchicalSignature {
    let max_level = radius.min(hierarchy.depth);
    let mut sig = Vec::with_capacity(max_level + 1);
    sig.push(hierarchy.tile_types[0][tile]);
    let mut current = tile;
    for level in 0..max_level {
        current = hierarchy.parent_of[level][current];
        sig.push(hierarchy.tile_types[level + 1][current]);
    }
    sig
}

// ---------------------------------------------------------------------------
// Cross-seed distinguishing
// ---------------------------------------------------------------------------

/// Result of cross-seed distinguishing at one radius.
pub struct DistinguishingResult {
    pub radius: usize,
    /// Fraction of tiles (across all seeds) with a seed-unique signature.
    pub advantage: f64,
    pub distinct_signatures: usize,
    /// Per-seed advantage: fraction of each seed's tiles that are distinguishable.
    pub per_seed_advantage: Vec<f64>,
}

/// Build a hierarchy from each seed type and measure distinguishing advantage.
///
/// For each hierarchical radius r, computes what fraction of tiles produce a
/// signature (ancestor type chain up to level r) unique to their seed's hierarchy.
/// At radius >= depth the seed type is directly observable, so advantage = 1.0.
pub fn cross_seed_distinguishing(
    system: &dyn TilingSystem,
    depth: usize,
    max_radius: usize,
) -> Vec<DistinguishingResult> {
    let num_seeds = system.num_types();

    let hierarchies: Vec<FlatHierarchy> = (0..num_seeds)
        .map(|seed| build_hierarchy(system, seed, depth))
        .collect();

    let per_seed_count: Vec<usize> = hierarchies.iter().map(|h| h.tile_types[0].len()).collect();
    let total_tiles: usize = per_seed_count.iter().sum();

    let mut results = Vec::new();

    for r in 0..=max_radius {
        let mut all_sigs: Vec<(usize, HierarchicalSignature)> = Vec::new();
        for (seed_idx, hierarchy) in hierarchies.iter().enumerate() {
            let n = hierarchy.tile_types[0].len();
            for tile in 0..n {
                let sig = hierarchical_signature(hierarchy, tile, r);
                all_sigs.push((seed_idx, sig));
            }
        }

        // Pool: signature -> set of seeds that produce it
        let mut sig_to_seeds: HashMap<&HierarchicalSignature, HashSet<usize>> = HashMap::new();
        for (seed_idx, sig) in &all_sigs {
            sig_to_seeds.entry(sig).or_default().insert(*seed_idx);
        }

        let mut per_seed_unique = vec![0usize; num_seeds];
        let mut total_unique = 0usize;

        for (seed_idx, sig) in &all_sigs {
            if sig_to_seeds[sig].len() == 1 {
                per_seed_unique[*seed_idx] += 1;
                total_unique += 1;
            }
        }

        let advantage = if total_tiles > 0 {
            total_unique as f64 / total_tiles as f64
        } else {
            0.0
        };

        let per_seed_advantage: Vec<f64> = (0..num_seeds)
            .map(|s| {
                if per_seed_count[s] > 0 {
                    per_seed_unique[s] as f64 / per_seed_count[s] as f64
                } else {
                    0.0
                }
            })
            .collect();

        results.push(DistinguishingResult {
            radius: r,
            advantage,
            distinct_signatures: sig_to_seeds.len(),
            per_seed_advantage,
        });
    }

    results
}

// ---------------------------------------------------------------------------
// Information-theoretic analysis
// ---------------------------------------------------------------------------

/// Information-theoretic measurements at one radius.
pub struct InfoTheoreticResult {
    pub radius: usize,
    /// H(signature) — entropy of the signature distribution.
    pub signature_entropy: f64,
    /// H(seed | signature) — conditional entropy of seed given signature.
    pub conditional_entropy: f64,
    /// I(seed; signature) — mutual information between seed and signature.
    pub mutual_information: f64,
    /// I / H(seed), normalized to [0, 1].
    pub normalized_mi: f64,
    pub distinct_signatures: usize,
}

/// Compute Shannon entropy and mutual information between seed and signature.
///
/// Uses hierarchical signatures (ancestor type chains) as the observable.
pub fn information_theoretic_analysis(
    system: &dyn TilingSystem,
    depth: usize,
    max_radius: usize,
) -> Vec<InfoTheoreticResult> {
    let num_seeds = system.num_types();

    let hierarchies: Vec<FlatHierarchy> = (0..num_seeds)
        .map(|seed| build_hierarchy(system, seed, depth))
        .collect();

    let per_seed_count: Vec<usize> = hierarchies.iter().map(|h| h.tile_types[0].len()).collect();
    let total_tiles: usize = per_seed_count.iter().sum();

    // H(seed)
    let seed_entropy = {
        let mut h = 0.0f64;
        for &count in &per_seed_count {
            if count > 0 {
                let p = count as f64 / total_tiles as f64;
                h -= p * p.ln();
            }
        }
        h
    };

    let mut results = Vec::new();

    for r in 0..=max_radius {
        let mut joint: HashMap<(usize, HierarchicalSignature), usize> = HashMap::new();
        let mut sig_counts: HashMap<HierarchicalSignature, usize> = HashMap::new();

        for (seed_idx, hierarchy) in hierarchies.iter().enumerate() {
            let n = hierarchy.tile_types[0].len();
            for tile in 0..n {
                let sig = hierarchical_signature(hierarchy, tile, r);
                *joint.entry((seed_idx, sig.clone())).or_default() += 1;
                *sig_counts.entry(sig).or_default() += 1;
            }
        }

        let signature_entropy = {
            let mut h = 0.0f64;
            for &count in sig_counts.values() {
                let p = count as f64 / total_tiles as f64;
                h -= p * p.ln();
            }
            h
        };

        let joint_entropy = {
            let mut h = 0.0f64;
            for &count in joint.values() {
                let p = count as f64 / total_tiles as f64;
                h -= p * p.ln();
            }
            h
        };

        // H(seed | signature) = H(seed, signature) - H(signature)
        let conditional_entropy = (joint_entropy - signature_entropy).max(0.0);

        // I(seed; signature) = H(seed) - H(seed | signature)
        let mutual_information = (seed_entropy - conditional_entropy).max(0.0);

        let normalized_mi = if seed_entropy > 1e-12 {
            (mutual_information / seed_entropy).min(1.0)
        } else {
            0.0
        };

        results.push(InfoTheoreticResult {
            radius: r,
            signature_entropy,
            conditional_entropy,
            mutual_information,
            normalized_mi,
            distinct_signatures: sig_counts.len(),
        });
    }

    results
}

// ---------------------------------------------------------------------------
// Phase transition detection
// ---------------------------------------------------------------------------

/// Detected phase transition points.
pub struct PhaseTransition {
    /// Smallest radius with advantage > 0.5.
    pub critical_radius_50: Option<usize>,
    /// Smallest radius with advantage > 0.99.
    pub critical_radius_99: Option<usize>,
    /// Smallest radius with normalized MI > 0.5.
    pub info_critical_50: Option<usize>,
    /// Smallest radius with normalized MI > 0.99.
    pub info_critical_99: Option<usize>,
    /// Whether the transition happens over 1-2 radius steps.
    pub is_sharp: bool,
}

pub fn detect_phase_transition(
    distinguishing: &[DistinguishingResult],
    info_theory: &[InfoTheoreticResult],
) -> PhaseTransition {
    let critical_radius_50 = distinguishing
        .iter()
        .find(|d| d.advantage > 0.5)
        .map(|d| d.radius);
    let critical_radius_99 = distinguishing
        .iter()
        .find(|d| d.advantage > 0.99)
        .map(|d| d.radius);

    let info_critical_50 = info_theory
        .iter()
        .find(|i| i.normalized_mi > 0.5)
        .map(|i| i.radius);
    let info_critical_99 = info_theory
        .iter()
        .find(|i| i.normalized_mi > 0.99)
        .map(|i| i.radius);

    let is_sharp = match (critical_radius_50, critical_radius_99) {
        (Some(r50), Some(r99)) => r99.saturating_sub(r50) <= 2,
        _ => false,
    };

    PhaseTransition {
        critical_radius_50,
        critical_radius_99,
        info_critical_50,
        info_critical_99,
        is_sharp,
    }
}

// ---------------------------------------------------------------------------
// Top-level analysis and report
// ---------------------------------------------------------------------------

/// Complete local-to-global gap analysis.
pub struct GapAnalysis {
    pub system_name: String,
    pub depth: usize,
    pub seed_count: usize,
    pub tiles_per_seed: Vec<usize>,
    /// Ancestry radii with full sibling adjacency (baseline).
    pub ancestry: Vec<AncestryLevelResult>,
    /// Ancestry radii with cross-supertile adjacency (geometric comparison).
    /// Empty if depth < 2 (cross-supertile requires grandparent level).
    pub ancestry_cross_supertile: Vec<AncestryLevelResult>,
    pub distinguishing: Vec<DistinguishingResult>,
    pub info_theory: Vec<InfoTheoreticResult>,
    pub phase_transition: PhaseTransition,
}

/// Run the full gap analysis for a tiling system.
pub fn analyze_system(
    system: &dyn TilingSystem,
    depth: usize,
    max_radius: usize,
) -> GapAnalysis {
    let num_seeds = system.num_types();

    // Ancestry analysis using seed 0
    let hierarchy = build_hierarchy(system, 0, depth);

    fn ancestry_results(
        hierarchy: &FlatHierarchy,
        adjacency: Vec<Vec<usize>>,
        max_radius: usize,
    ) -> Vec<AncestryLevelResult> {
        let tiles_total = hierarchy.tile_types[0].len();
        let ancestry_radii = compute_ancestry_radii(hierarchy, &adjacency, max_radius);
        ancestry_radii
            .iter()
            .enumerate()
            .map(|(level_idx, radii)| {
                let target_level = level_idx + 1;
                let determined = radii.iter().filter(|v| v.is_some()).count();
                let determined_radii: Vec<usize> = radii.iter().filter_map(|v| *v).collect();
                let min_r = determined_radii.iter().copied().min();
                let max_r = if determined == tiles_total {
                    determined_radii.iter().copied().max()
                } else {
                    None
                };
                let mean_r = if !determined_radii.is_empty() {
                    determined_radii.iter().sum::<usize>() as f64
                        / determined_radii.len() as f64
                } else {
                    f64::NAN
                };
                AncestryLevelResult {
                    target_level,
                    tiles_total,
                    tiles_determined: determined,
                    min_radius: min_r,
                    max_radius: max_r,
                    mean_radius: mean_r,
                }
            })
            .collect()
    }

    let ancestry = if depth > 0 {
        let adjacency = full_sibling_adjacency(&hierarchy, 0);
        ancestry_results(&hierarchy, adjacency, max_radius)
    } else {
        Vec::new()
    };

    let ancestry_cross_supertile = if depth >= 2 {
        let adjacency = cross_supertile_adjacency(system, &hierarchy, 0);
        ancestry_results(&hierarchy, adjacency, max_radius)
    } else {
        Vec::new()
    };

    // Cross-seed distinguishing
    let distinguishing = cross_seed_distinguishing(system, depth, max_radius);

    // Information-theoretic analysis
    let info_theory = information_theoretic_analysis(system, depth, max_radius);

    // Phase transition
    let phase_transition = detect_phase_transition(&distinguishing, &info_theory);

    // Tile counts per seed
    let tiles_per_seed: Vec<usize> = (0..num_seeds)
        .map(|seed| build_hierarchy(system, seed, depth).tile_types[0].len())
        .collect();

    GapAnalysis {
        system_name: system.name().to_string(),
        depth,
        seed_count: num_seeds,
        tiles_per_seed,
        ancestry,
        ancestry_cross_supertile,
        distinguishing,
        info_theory,
        phase_transition,
    }
}

/// Print the gap analysis report.
pub fn print_report(system: &dyn TilingSystem, analysis: &GapAnalysis) {
    info!("=== Local-to-Global Gap Analysis ===\n");

    info!("System: {}", analysis.system_name);
    info!("Depth: {}", analysis.depth);
    info!("Seed types: {}", analysis.seed_count);
    for (i, &count) in analysis.tiles_per_seed.iter().enumerate() {
        info!("  {} seed: {} base tiles", system.type_name(i), count);
    }

    // Ancestry: full sibling adjacency
    info!(
        "\n--- Multi-level ancestry determination: full sibling adjacency (seed {}) ---",
        system.type_name(0)
    );
    for ar in &analysis.ancestry {
        let pct = if ar.tiles_total > 0 {
            ar.tiles_determined as f64 / ar.tiles_total as f64 * 100.0
        } else {
            0.0
        };
        let max_str = ar.max_radius.map_or("?".to_string(), |r| r.to_string());
        let min_str = ar.min_radius.map_or("?".to_string(), |r| r.to_string());
        info!(
            "  Level {}: {}/{} determined ({:.1}%) | min_r={}, max_r={}, mean_r={:.2}",
            ar.target_level, ar.tiles_determined, ar.tiles_total, pct, min_str, max_str,
            ar.mean_radius
        );
    }

    // Ancestry: cross-supertile adjacency
    if !analysis.ancestry_cross_supertile.is_empty() {
        info!(
            "\n--- Multi-level ancestry determination: cross-supertile adjacency (seed {}) ---",
            system.type_name(0)
        );
        info!("  (tiles in inflation-adjacent supertiles are connected across supertile boundaries)");
        for ar in &analysis.ancestry_cross_supertile {
            let pct = if ar.tiles_total > 0 {
                ar.tiles_determined as f64 / ar.tiles_total as f64 * 100.0
            } else {
                0.0
            };
            let max_str = ar.max_radius.map_or("?".to_string(), |r| r.to_string());
            let min_str = ar.min_radius.map_or("?".to_string(), |r| r.to_string());
            info!(
                "  Level {}: {}/{} determined ({:.1}%) | min_r={}, max_r={}, mean_r={:.2}",
                ar.target_level, ar.tiles_determined, ar.tiles_total, pct, min_str, max_str,
                ar.mean_radius
            );
        }

        // Print side-by-side comparison
        info!("\n--- Ancestry radius comparison: sibling vs cross-supertile ---");
        info!(
            "  {:>7}  {:>14}  {:>14}  {:>10}",
            "Level", "Sibling max_r", "Cross max_r", "Change"
        );
        for (sib, cross) in analysis.ancestry.iter().zip(analysis.ancestry_cross_supertile.iter()) {
            let sib_str = sib.max_radius.map_or("?".to_string(), |r| r.to_string());
            let cross_str = cross.max_radius.map_or("?".to_string(), |r| r.to_string());
            let change = match (sib.max_radius, cross.max_radius) {
                (Some(s), Some(c)) if c < s => format!("-{}", s - c),
                (Some(s), Some(c)) if c == s => "same".to_string(),
                (Some(s), Some(c)) => format!("+{}", c - s),
                _ => "?".to_string(),
            };
            info!(
                "  {:>7}  {:>14}  {:>14}  {:>10}",
                sib.target_level, sib_str, cross_str, change
            );
        }
    }

    // Cross-seed distinguishing
    info!("\n--- Cross-seed distinguishing ---");
    info!(
        "  {:>6} {:>12} {:>12}",
        "Radius", "Advantage", "Signatures"
    );
    for dr in &analysis.distinguishing {
        info!(
            "  {:>6} {:>11.1}% {:>12}",
            dr.radius,
            dr.advantage * 100.0,
            dr.distinct_signatures,
        );
    }

    // Information theory
    info!("\n--- Information-theoretic analysis ---");
    info!(
        "  {:>6} {:>10} {:>10} {:>10} {:>10}",
        "Radius", "H(sig)", "H(s|sig)", "I(s;sig)", "I/H(s)"
    );
    for it in &analysis.info_theory {
        info!(
            "  {:>6} {:>10.4} {:>10.4} {:>10.4} {:>10.4}",
            it.radius, it.signature_entropy, it.conditional_entropy, it.mutual_information,
            it.normalized_mi
        );
    }

    // Phase transition
    info!("\n--- Phase transition ---");
    let pt = &analysis.phase_transition;
    info!(
        "  Advantage > 50%: {}",
        pt.critical_radius_50
            .map_or("not reached".to_string(), |r| format!("radius {}", r))
    );
    info!(
        "  Advantage > 99%: {}",
        pt.critical_radius_99
            .map_or("not reached".to_string(), |r| format!("radius {}", r))
    );
    info!(
        "  Normalized MI > 50%: {}",
        pt.info_critical_50
            .map_or("not reached".to_string(), |r| format!("radius {}", r))
    );
    info!(
        "  Normalized MI > 99%: {}",
        pt.info_critical_99
            .map_or("not reached".to_string(), |r| format!("radius {}", r))
    );
    info!("  Sharp transition: {}", pt.is_sharp);

    // Verdict
    info!("\n=== VERDICT ===");
    if let Some(r) = pt.critical_radius_99 {
        info!("The local-to-global gap closes at radius {}.", r);
        info!("This is an information-theoretic gap, not computational hardness.");
    } else if let Some(r) = pt.critical_radius_50 {
        info!(
            "The gap partially closes (>50% advantage at radius {}) \
             but does not fully close within the tested radius.",
            r
        );
    } else {
        info!("The gap persists beyond the tested radius.");
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::oneway::compute_determination_radii;
    use crate::systems::hat::HatSystem;
    use crate::systems::spectre::SpectreSystem;

    #[test]
    fn ancestry_at_level_1_matches_determination_radii() {
        let system = HatSystem::new();
        let hierarchy = build_hierarchy(&system, 0, 3);
        let adjacency = full_sibling_adjacency(&hierarchy, 0);

        let ancestry = compute_ancestry_radii(&hierarchy, &adjacency, 5);
        let determination = compute_determination_radii(&hierarchy, &adjacency, 0, 5);

        assert_eq!(
            ancestry[0], determination,
            "level-1 ancestry radii should match determination radii"
        );
    }

    #[test]
    fn distinguishing_advantage_monotone_with_radius() {
        let system = HatSystem::new();
        let results = cross_seed_distinguishing(&system, 2, 5);

        for w in results.windows(2) {
            assert!(
                w[1].advantage >= w[0].advantage - 1e-10,
                "advantage should be non-decreasing: radius {} ({:.4}) -> {} ({:.4})",
                w[0].radius,
                w[0].advantage,
                w[1].radius,
                w[1].advantage
            );
        }
    }

    #[test]
    fn mutual_information_monotone_with_radius() {
        let system = HatSystem::new();
        let results = information_theoretic_analysis(&system, 2, 5);

        for w in results.windows(2) {
            assert!(
                w[1].mutual_information >= w[0].mutual_information - 1e-10,
                "MI should be non-decreasing: radius {} ({:.6}) -> {} ({:.6})",
                w[0].radius,
                w[0].mutual_information,
                w[1].radius,
                w[1].mutual_information
            );
        }
    }

    #[test]
    fn normalized_mi_bounded_0_1() {
        let system = HatSystem::new();
        let results = information_theoretic_analysis(&system, 2, 3);

        for it in &results {
            assert!(
                it.normalized_mi >= -1e-10 && it.normalized_mi <= 1.0 + 1e-10,
                "normalized MI should be in [0,1], got {} at radius {}",
                it.normalized_mi,
                it.radius
            );
        }
    }

    #[test]
    fn full_determination_at_large_radius() {
        let system = HatSystem::new();
        let results = cross_seed_distinguishing(&system, 3, 5);

        let max_advantage = results.iter().map(|r| r.advantage).fold(0.0f64, f64::max);
        assert!(
            max_advantage > 0.5,
            "advantage should exceed 0.5 at some radius, got {}",
            max_advantage
        );
    }

    #[test]
    fn spectre_distinguishing_runs() {
        let system = SpectreSystem::new();
        let results = cross_seed_distinguishing(&system, 2, 3);

        assert_eq!(results.len(), 4, "should have results for radii 0..=3");
        for r in &results {
            assert!(r.advantage >= 0.0 && r.advantage <= 1.0);
        }
    }

    #[test]
    fn analyze_system_hat_depth_2() {
        let system = HatSystem::new();
        let analysis = analyze_system(&system, 2, 3);

        assert_eq!(analysis.system_name, "hat");
        assert_eq!(analysis.depth, 2);
        assert_eq!(analysis.seed_count, 4);
        assert_eq!(analysis.tiles_per_seed.len(), 4);
        assert!(!analysis.ancestry.is_empty());
        assert!(!analysis.distinguishing.is_empty());
        assert!(!analysis.info_theory.is_empty());
    }
}
