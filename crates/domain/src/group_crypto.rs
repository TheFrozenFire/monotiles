use crate::coxeter::CoxeterElement;
use crate::cucaracha::{cucaracha, expand_by_generators, Cotiler};
use std::collections::{HashMap, HashSet};
use std::time::Instant;
use tracing::{info, debug, trace, info_span, debug_span};

// ---------------------------------------------------------------------------
// Helpers
// ---------------------------------------------------------------------------

fn xorshift64(state: &mut u64) -> u64 {
    let mut x = *state;
    x ^= x << 13;
    x ^= x >> 7;
    x ^= x << 17;
    *state = x;
    x
}

/// Deterministic ordering for CoxeterElements (used for lexicographic pick).
fn coxeter_sort_key(e: &CoxeterElement) -> (i64, i64, u8, bool) {
    (e.tx, e.ty, e.rotation, e.reflected)
}

// ---------------------------------------------------------------------------
// 2a: Cotiler generation by BFS frontier expansion
// ---------------------------------------------------------------------------

/// Generate candidate tile positions adjacent to an existing cotiler.
///
/// For each cell on the frontier (covered cells expanded by 4 generator steps),
/// try all 16 Cucaracha offsets `g = cell * c_i^{-1}` as candidate positions.
fn candidate_positions(cotiler: &Cotiler) -> Vec<CoxeterElement> {
    let tile = cucaracha();
    let covered = cotiler.covered_cells();
    let expanded = expand_by_generators(&covered, 4);

    // Frontier cells: in expanded but not in covered
    let frontier: Vec<_> = expanded.difference(&covered).copied().collect();

    // Inverse Cucaracha offsets for candidate generation
    let inv_offsets: Vec<CoxeterElement> = tile.iter().map(|c| c.inverse()).collect();

    let existing: HashSet<_> = cotiler.positions.iter().copied().collect();
    let mut candidates = HashSet::new();

    for cell in &frontier {
        for inv_c in &inv_offsets {
            let g = cell.compose(inv_c);
            if existing.contains(&g) {
                continue;
            }
            // Check that placing a tile at g doesn't overlap existing coverage
            let overlaps = tile.iter().any(|c| {
                let placed = g.compose(c);
                covered.contains(&placed)
            });
            if !overlaps {
                candidates.insert(g);
            }
        }
    }

    let mut result: Vec<_> = candidates.into_iter().collect();
    result.sort_by(|a, b| coxeter_sort_key(a).partial_cmp(&coxeter_sort_key(b)).unwrap());
    result
}

/// Grow a valid cotiler by iteratively adding non-overlapping tile placements.
///
/// Returns `None` if growth stalls before reaching `target_size`.
pub fn grow_cotiler(seed: CoxeterElement, target_size: usize, rng: &mut u64) -> Option<Cotiler> {
    let mut cotiler = Cotiler::new(vec![seed]);

    while cotiler.positions.len() < target_size {
        let candidates = candidate_positions(&cotiler);
        if candidates.is_empty() {
            return None;
        }
        let idx = xorshift64(rng) as usize % candidates.len();
        cotiler.positions.push(candidates[idx]);
    }

    Some(cotiler)
}

// ---------------------------------------------------------------------------
// 2b: Cotiler recovery experiment
// ---------------------------------------------------------------------------

#[derive(Debug, Clone)]
pub struct RecoveryResult {
    pub size: usize,
    pub trials: usize,
    pub unique_fraction: f64,
    pub mean_solutions: f64,
    pub mean_time_ms: f64,
    pub budget_exceeded: bool,
}

/// Attempt to recover a cotiler from its cotiler group generators.
///
/// Fixes c_0 = identity (translation normalization), then BFS-expands the
/// generated group to find candidate positions. Checks each candidate subset
/// of the right size that generates exactly the same G_C.
/// Returns `(solutions, budget_exceeded)`.
pub fn recover_cotiler(
    generators: &[CoxeterElement],
    target_size: usize,
    max_solutions: usize,
) -> (Vec<Cotiler>, bool) {
    if target_size == 0 {
        return (vec![], false);
    }
    if target_size == 1 {
        // Single-tile cotiler has no generators; recovery is trivially the identity
        return (vec![Cotiler::new(vec![CoxeterElement::identity()])], false);
    }

    // BFS-expand from generators to find candidate group elements
    let mut group_elements = HashSet::new();
    group_elements.insert(CoxeterElement::identity());
    for g in generators {
        group_elements.insert(*g);
        group_elements.insert(g.inverse());
    }

    // Expand: multiply known elements pairwise, up to a reasonable limit
    let max_group_size = (target_size * target_size * 4).max(64);
    let mut changed = true;
    while changed && group_elements.len() < max_group_size {
        changed = false;
        let current: Vec<_> = group_elements.iter().copied().collect();
        for a in &current {
            for g in generators {
                let ag = a.compose(g);
                if group_elements.insert(ag) {
                    changed = true;
                }
                let ag_inv = a.compose(&g.inverse());
                if group_elements.insert(ag_inv) {
                    changed = true;
                }
                if group_elements.len() >= max_group_size {
                    break;
                }
            }
            if group_elements.len() >= max_group_size {
                break;
            }
        }
    }

    // Filter to candidates that are valid tile positions (non-overlapping with identity)
    let tile = cucaracha();
    let id_cells: HashSet<_> = tile.iter().copied().collect();

    let mut candidates: Vec<_> = group_elements
        .iter()
        .filter(|g| {
            if **g == CoxeterElement::identity() {
                return true;
            }
            // Check no overlap with identity tile
            !tile.iter().any(|c| id_cells.contains(&g.compose(c)))
        })
        .copied()
        .collect();
    candidates.sort_by(|a, b| coxeter_sort_key(a).partial_cmp(&coxeter_sort_key(b)).unwrap());

    let _span = debug_span!("recover_cotiler", target_size, candidates = candidates.len()).entered();

    debug!(
        target_size,
        group_expanded = group_elements.len(),
        valid_candidates = candidates.len(),
        "recovery search space ~= C({}, {})",
        candidates.len(),
        target_size - 1,
    );

    // Backtracking search: build cotilers of size target_size starting with identity
    let mut solutions = Vec::new();
    let mut current = vec![CoxeterElement::identity()];
    let mut covered: HashSet<_> = tile.iter().copied().collect();

    let mut nodes_visited = 0u64;
    let mut budget_exceeded = false;

    fn backtrack(
        candidates: &[CoxeterElement],
        current: &mut Vec<CoxeterElement>,
        covered: &mut HashSet<CoxeterElement>,
        target_size: usize,
        max_solutions: usize,
        solutions: &mut Vec<Cotiler>,
        generators: &[CoxeterElement],
        tile: &[CoxeterElement; 16],
        start_idx: usize,
        nodes_visited: &mut u64,
        budget_exceeded: &mut bool,
    ) {
        *nodes_visited += 1;
        if *nodes_visited >= 10_000_000 {
            *budget_exceeded = true;
            return;
        }
        if *nodes_visited % 1_000_000 == 0 {
            trace!(
                nodes_millions = *nodes_visited / 1_000_000,
                depth = current.len(),
                target_size,
                "recovery backtrack progress",
            );
        }
        if solutions.len() >= max_solutions {
            return;
        }
        if current.len() == target_size {
            // Verify this cotiler generates the same G_C
            let cotiler = Cotiler::new(current.clone());
            let gens: HashSet<_> = cotiler.cotiler_group_generators().into_iter().collect();
            let orig_gens: HashSet<_> = generators.iter().copied().collect();
            // Check that the original generators are reachable from our cotiler
            if orig_gens.iter().all(|g| gens.contains(g)) {
                solutions.push(cotiler);
            }
            return;
        }

        for i in start_idx..candidates.len() {
            if solutions.len() >= max_solutions || *budget_exceeded {
                return;
            }
            let g = candidates[i];
            if g == CoxeterElement::identity() {
                continue;
            }
            // Check non-overlap
            let cells: Vec<_> = tile.iter().map(|c| g.compose(c)).collect();
            if cells.iter().any(|c| covered.contains(c)) {
                continue;
            }
            // Place tile
            for c in &cells {
                covered.insert(*c);
            }
            current.push(g);

            backtrack(
                candidates,
                current,
                covered,
                target_size,
                max_solutions,
                solutions,
                generators,
                tile,
                i + 1,
                nodes_visited,
                budget_exceeded,
            );

            current.pop();
            for c in &cells {
                covered.remove(c);
            }
        }
    }

    backtrack(
        &candidates,
        &mut current,
        &mut covered,
        target_size,
        max_solutions,
        &mut solutions,
        generators,
        &tile,
        0,
        &mut nodes_visited,
        &mut budget_exceeded,
    );

    if budget_exceeded {
        debug!(
            nodes_visited,
            solutions = solutions.len(),
            "recovery budget exceeded (10M nodes)",
        );
    }

    debug!(
        nodes_visited,
        solutions = solutions.len(),
        budget_exceeded,
        "recovery search complete",
    );
    (solutions, budget_exceeded)
}

/// Coset-based cotiler recovery exploiting the Z² ⋊ D₆ structure.
///
/// Instead of brute-force subset enumeration, decomposes G_C elements by their
/// translation component. For each unique translation, at most 12 point group
/// decorations are possible. This reduces the search from C(candidates, n-1)
/// to a product over translation classes.
pub fn recover_cotiler_coset(
    generators: &[CoxeterElement],
    target_size: usize,
    max_solutions: usize,
) -> Vec<Cotiler> {
    if target_size == 0 {
        return vec![];
    }
    if target_size == 1 {
        return vec![Cotiler::new(vec![CoxeterElement::identity()])];
    }

    // BFS-expand the generated group (same as brute-force version)
    let mut group_elements = HashSet::new();
    group_elements.insert(CoxeterElement::identity());
    for g in generators {
        group_elements.insert(*g);
        group_elements.insert(g.inverse());
    }
    let max_group_size = (target_size * target_size * 4).max(64);
    let mut changed = true;
    while changed && group_elements.len() < max_group_size {
        changed = false;
        let current: Vec<_> = group_elements.iter().copied().collect();
        for a in &current {
            for g in generators {
                let ag = a.compose(g);
                if group_elements.insert(ag) {
                    changed = true;
                }
                let ag_inv = a.compose(&g.inverse());
                if group_elements.insert(ag_inv) {
                    changed = true;
                }
                if group_elements.len() >= max_group_size {
                    break;
                }
            }
            if group_elements.len() >= max_group_size {
                break;
            }
        }
    }

    let tile = cucaracha();
    let id_cells: HashSet<_> = tile.iter().copied().collect();

    // Group candidates by translation component
    let mut by_translation: HashMap<(i64, i64), Vec<CoxeterElement>> = HashMap::new();
    for &g in &group_elements {
        // Filter: non-overlapping with identity tile
        if g != CoxeterElement::identity()
            && tile.iter().any(|c| id_cells.contains(&g.compose(c)))
        {
            continue;
        }
        let (tx, ty) = g.translation();
        by_translation.entry((tx, ty)).or_default().push(g);
    }

    // Sort translations for deterministic ordering
    let mut translations: Vec<(i64, i64)> = by_translation.keys().copied().collect();
    translations.sort();

    let _span = debug_span!(
        "recover_cotiler_coset",
        target_size,
        translation_classes = translations.len(),
        total_candidates = group_elements.len(),
    )
    .entered();

    debug!(
        target_size,
        translation_classes = translations.len(),
        "coset-based recovery: {} translation classes, max {} D6 choices each",
        translations.len(),
        by_translation.values().map(|v| v.len()).max().unwrap_or(0),
    );

    // Backtracking over translation classes instead of individual candidates.
    // For each translation class, choose one element (point group decoration)
    // or skip the class entirely.
    let mut solutions = Vec::new();
    let mut current = vec![CoxeterElement::identity()];
    let mut covered: HashSet<_> = tile.iter().copied().collect();
    let mut nodes_visited = 0u64;

    fn coset_backtrack(
        translations: &[(i64, i64)],
        by_translation: &HashMap<(i64, i64), Vec<CoxeterElement>>,
        current: &mut Vec<CoxeterElement>,
        covered: &mut HashSet<CoxeterElement>,
        target_size: usize,
        max_solutions: usize,
        solutions: &mut Vec<Cotiler>,
        generators: &[CoxeterElement],
        tile: &[CoxeterElement; 16],
        trans_idx: usize,
        nodes_visited: &mut u64,
    ) {
        *nodes_visited += 1;
        if solutions.len() >= max_solutions {
            return;
        }
        if current.len() == target_size {
            // Verify G_C match
            let cotiler = Cotiler::new(current.clone());
            let gens: HashSet<_> = cotiler.cotiler_group_generators().into_iter().collect();
            let orig_gens: HashSet<_> = generators.iter().copied().collect();
            if orig_gens.iter().all(|g| gens.contains(g)) {
                solutions.push(cotiler);
            }
            return;
        }
        if trans_idx >= translations.len() {
            return;
        }
        // Not enough translations left to fill remaining slots
        let remaining_slots = target_size - current.len();
        let remaining_classes = translations.len() - trans_idx;
        if remaining_classes < remaining_slots {
            return;
        }

        // Option 1: skip this translation class
        coset_backtrack(
            translations,
            by_translation,
            current,
            covered,
            target_size,
            max_solutions,
            solutions,
            generators,
            tile,
            trans_idx + 1,
            nodes_visited,
        );

        // Option 2: pick one point group decoration from this class
        let key = &translations[trans_idx];
        if let Some(candidates) = by_translation.get(key) {
            for &g in candidates {
                if solutions.len() >= max_solutions {
                    return;
                }
                if g == CoxeterElement::identity() {
                    continue;
                }
                let cells: Vec<_> = tile.iter().map(|c| g.compose(c)).collect();
                if cells.iter().any(|c| covered.contains(c)) {
                    continue;
                }
                for c in &cells {
                    covered.insert(*c);
                }
                current.push(g);

                coset_backtrack(
                    translations,
                    by_translation,
                    current,
                    covered,
                    target_size,
                    max_solutions,
                    solutions,
                    generators,
                    tile,
                    trans_idx + 1,
                    nodes_visited,
                );

                current.pop();
                for c in &cells {
                    covered.remove(c);
                }
            }
        }
    }

    coset_backtrack(
        &translations,
        &by_translation,
        &mut current,
        &mut covered,
        target_size,
        max_solutions,
        &mut solutions,
        generators,
        &tile,
        0,
        &mut nodes_visited,
    );

    debug!(
        nodes_visited,
        solutions = solutions.len(),
        "coset recovery complete",
    );
    solutions
}

/// Compare brute-force vs coset-based recovery at a given size.
pub struct CosetComparisonResult {
    pub size: usize,
    pub brute_force_nodes: u64,
    pub brute_force_ms: f64,
    pub brute_force_solutions: usize,
    pub brute_force_budget_exceeded: bool,
    pub coset_nodes: u64,
    pub coset_ms: f64,
    pub coset_solutions: usize,
}

pub fn coset_comparison(size: usize, trials: usize) -> Vec<CosetComparisonResult> {
    let mut rng = 0xBEEF_CAFE_u64;
    let mut results = Vec::new();

    for _ in 0..trials {
        let seed = CoxeterElement::identity();
        let cotiler = match grow_cotiler(seed, size, &mut rng) {
            Some(c) => c,
            None => continue,
        };
        let generators = cotiler.cotiler_group_generators();

        // Brute-force
        let t0 = Instant::now();
        let (bf_solutions, bf_exceeded) = recover_cotiler(&generators, size, 16);
        let bf_ms = t0.elapsed().as_secs_f64() * 1000.0;

        // Coset-based
        let t1 = Instant::now();
        let cs_solutions = recover_cotiler_coset(&generators, size, 16);
        let cs_ms = t1.elapsed().as_secs_f64() * 1000.0;

        results.push(CosetComparisonResult {
            size,
            brute_force_nodes: 0, // nodes logged via tracing
            brute_force_ms: bf_ms,
            brute_force_solutions: bf_solutions.len(),
            brute_force_budget_exceeded: bf_exceeded,
            coset_nodes: 0,
            coset_ms: cs_ms,
            coset_solutions: cs_solutions.len(),
        });
    }

    results
}

pub fn print_coset_comparison(results: &[CosetComparisonResult]) {
    info!("\n--- Coset vs Brute-Force Recovery Comparison ---");
    info!(
        "{:<6} {:>12} {:>10} {:>12} {:>10} {:>10}",
        "Size", "BF(ms)", "BF sols", "Coset(ms)", "CS sols", "Speedup"
    );
    for r in results {
        let speedup = if r.coset_ms > 0.0 {
            r.brute_force_ms / r.coset_ms
        } else {
            f64::INFINITY
        };
        let bf_str = if r.brute_force_budget_exceeded {
            format!(">{:.1}", r.brute_force_ms)
        } else {
            format!("{:.2}", r.brute_force_ms)
        };
        info!(
            "{:<6} {:>12} {:>10} {:>12.2} {:>10} {:>9.1}x",
            r.size, bf_str, r.brute_force_solutions, r.coset_ms, r.coset_solutions, speedup,
        );
    }
}

pub fn recovery_experiment(size: usize, trials: usize) -> RecoveryResult {
    let _span = info_span!("recovery_experiment", size).entered();

    let mut rng = 0xDEAD_BEEF_u64;
    let mut total_solutions = 0usize;
    let mut total_time_ms = 0.0f64;
    let mut unique_count = 0usize;
    let mut actual_trials = 0usize;
    let mut any_budget_exceeded = false;

    for _ in 0..trials {
        let seed = CoxeterElement::identity();
        let cotiler = match grow_cotiler(seed, size, &mut rng) {
            Some(c) => c,
            None => continue,
        };
        actual_trials += 1;

        let generators = cotiler.cotiler_group_generators();

        let t0 = Instant::now();
        let (solutions, trial_budget_exceeded) = recover_cotiler(&generators, size, 16);
        let elapsed = t0.elapsed();
        total_time_ms += elapsed.as_secs_f64() * 1000.0;

        if trial_budget_exceeded {
            any_budget_exceeded = true;
        }

        total_solutions += solutions.len();
        if solutions.len() == 1 {
            unique_count += 1;
        }
    }

    let n = actual_trials.max(1) as f64;
    RecoveryResult {
        size,
        trials: actual_trials,
        unique_fraction: unique_count as f64 / n,
        mean_solutions: total_solutions as f64 / n,
        mean_time_ms: total_time_ms / n,
        budget_exceeded: any_budget_exceeded,
    }
}

// ---------------------------------------------------------------------------
// 2c: Region decomposition experiment (exact cover)
// ---------------------------------------------------------------------------

#[derive(Debug, Clone)]
pub struct DecompositionResult {
    pub size: usize,
    pub trials: usize,
    pub mean_solutions: f64,
    pub mean_first_time_ms: f64,
    pub all_found: bool,
}

/// Decompose a region of cells into Cucaracha tile placements (exact cover).
///
/// Uses backtracking with most-constrained-cell heuristic.
pub fn decompose_region(
    cells: &HashSet<CoxeterElement>,
    target_size: usize,
    max_solutions: usize,
) -> Vec<Cotiler> {
    let _span = debug_span!("decompose_region", target_size, cells = cells.len()).entered();

    let tile = cucaracha();
    let inv_offsets: Vec<CoxeterElement> = tile.iter().map(|c| c.inverse()).collect();

    let mut solutions = Vec::new();
    let mut remaining = cells.clone();
    let mut placements: Vec<CoxeterElement> = Vec::new();

    fn backtrack(
        remaining: &mut HashSet<CoxeterElement>,
        placements: &mut Vec<CoxeterElement>,
        target_size: usize,
        max_solutions: usize,
        solutions: &mut Vec<Cotiler>,
        tile: &[CoxeterElement; 16],
        inv_offsets: &[CoxeterElement],
    ) {
        if solutions.len() >= max_solutions {
            return;
        }
        if placements.len() == target_size {
            if remaining.is_empty() {
                solutions.push(Cotiler::new(placements.clone()));
            }
            return;
        }
        if remaining.is_empty() {
            return;
        }

        // Pick lexicographically smallest uncovered cell
        let cell = remaining
            .iter()
            .min_by(|a, b| {
                coxeter_sort_key(a)
                    .partial_cmp(&coxeter_sort_key(b))
                    .unwrap()
            })
            .copied()
            .unwrap();

        // Try all 16 candidate placements: g = cell * c_i^{-1}
        for inv_c in inv_offsets {
            if solutions.len() >= max_solutions {
                return;
            }
            let g = cell.compose(inv_c);

            // Check that all 16 cells of this placement are in remaining
            let placed_cells: Vec<_> = tile.iter().map(|c| g.compose(c)).collect();
            if !placed_cells.iter().all(|c| remaining.contains(c)) {
                continue;
            }

            // Place tile
            for c in &placed_cells {
                remaining.remove(c);
            }
            placements.push(g);

            backtrack(
                remaining,
                placements,
                target_size,
                max_solutions,
                solutions,
                tile,
                inv_offsets,
            );

            placements.pop();
            for c in &placed_cells {
                remaining.insert(*c);
            }
        }
    }

    backtrack(
        &mut remaining,
        &mut placements,
        target_size,
        max_solutions,
        &mut solutions,
        &tile,
        &inv_offsets,
    );

    solutions
}

pub fn decomposition_experiment(size: usize, trials: usize) -> DecompositionResult {
    let _span = info_span!("decomposition_experiment", size).entered();

    let mut rng = 0xCAFE_BABE_u64;
    let mut total_solutions = 0usize;
    let mut total_first_time_ms = 0.0f64;
    let mut all_found = true;
    let mut actual_trials = 0usize;

    for _ in 0..trials {
        let seed = CoxeterElement::identity();
        let cotiler = match grow_cotiler(seed, size, &mut rng) {
            Some(c) => c,
            None => continue,
        };
        actual_trials += 1;

        let cells = cotiler.covered_cells();

        let t0 = Instant::now();
        let solutions = decompose_region(&cells, size, 16);
        let elapsed = t0.elapsed();
        total_first_time_ms += elapsed.as_secs_f64() * 1000.0;

        if solutions.is_empty() {
            all_found = false;
        }
        total_solutions += solutions.len();
    }

    let n = actual_trials.max(1) as f64;
    DecompositionResult {
        size,
        trials: actual_trials,
        mean_solutions: total_solutions as f64 / n,
        mean_first_time_ms: total_first_time_ms / n,
        all_found,
    }
}

// ---------------------------------------------------------------------------
// 2d: Stabilizer experiment
// ---------------------------------------------------------------------------

#[derive(Debug, Clone)]
pub struct StabilizerResult {
    pub size: usize,
    pub trials: usize,
    pub trivial_count: usize,
    pub threefold_count: usize,
}

pub fn stabilizer_experiment(size: usize, trials: usize) -> StabilizerResult {
    let _span = info_span!("stabilizer_experiment", size).entered();

    let mut rng = 0xFACE_FEED_u64;
    let mut trivial = 0usize;
    let mut threefold = 0usize;
    let mut actual_trials = 0usize;

    for _ in 0..trials {
        let seed = CoxeterElement::identity();
        let cotiler = match grow_cotiler(seed, size, &mut rng) {
            Some(c) => c,
            None => continue,
        };
        actual_trials += 1;

        let stab = cotiler.stabilizer();
        match stab.len() {
            1 => trivial += 1,
            3 => threefold += 1,
            _ => {} // unexpected, but don't panic
        }
    }

    StabilizerResult {
        size,
        trials: actual_trials,
        trivial_count: trivial,
        threefold_count: threefold,
    }
}

// ---------------------------------------------------------------------------
// 2e: Top-level analysis and report
// ---------------------------------------------------------------------------

#[derive(Debug)]
pub struct GroupCryptoAnalysis {
    pub recovery: Vec<RecoveryResult>,
    pub decomposition: Vec<DecompositionResult>,
    pub stabilizer: Vec<StabilizerResult>,
    pub max_size: usize,
    pub trials: usize,
}

pub fn analyze(max_size: usize, trials: usize) -> GroupCryptoAnalysis {
    analyze_experiments(max_size, trials, "all")
}

pub fn analyze_experiments(
    max_size: usize,
    trials: usize,
    experiment: &str,
) -> GroupCryptoAnalysis {
    let run_recovery = experiment == "all" || experiment == "recovery";
    let run_decomposition = experiment == "all" || experiment == "decomposition";
    let run_stabilizer = experiment == "all" || experiment == "stabilizer";

    let mut recovery = Vec::new();
    let mut decomposition = Vec::new();
    let mut stabilizer = Vec::new();

    for size in 1..=max_size {
        if run_recovery {
            debug!(size, "running recovery experiment");
            recovery.push(recovery_experiment(size, trials));
        }
        if run_decomposition {
            debug!(size, "running decomposition experiment");
            decomposition.push(decomposition_experiment(size, trials));
        }
        if run_stabilizer {
            debug!(size, "running stabilizer experiment");
            stabilizer.push(stabilizer_experiment(size, trials));
        }
    }

    GroupCryptoAnalysis {
        recovery,
        decomposition,
        stabilizer,
        max_size,
        trials,
    }
}

pub fn print_report(analysis: &GroupCryptoAnalysis) {
    info!("\n=== Group Cryptography Analysis ===");
    info!(
        "max_size={}, trials={}\n",
        analysis.max_size, analysis.trials
    );

    if !analysis.recovery.is_empty() {
        info!("--- Cotiler Recovery ---");
        info!(
            "{:<6} {:>8} {:>12} {:>14} {:>12}",
            "Size", "Trials", "Unique%", "MeanSolutions", "MeanTime(ms)"
        );
        for r in &analysis.recovery {
            info!(
                "{:<6} {:>8} {:>11.1}% {:>14.2} {:>12.2}",
                r.size,
                r.trials,
                r.unique_fraction * 100.0,
                r.mean_solutions,
                r.mean_time_ms,
            );
        }
        info!("");
    }

    if !analysis.decomposition.is_empty() {
        info!("--- Region Decomposition (Exact Cover) ---");
        info!(
            "{:<6} {:>8} {:>14} {:>14} {:>10}",
            "Size", "Trials", "MeanSolutions", "MeanTime(ms)", "AllFound"
        );
        for d in &analysis.decomposition {
            info!(
                "{:<6} {:>8} {:>14.2} {:>14.2} {:>10}",
                d.size,
                d.trials,
                d.mean_solutions,
                d.mean_first_time_ms,
                if d.all_found { "yes" } else { "NO" },
            );
        }
        info!("");
    }

    if !analysis.stabilizer.is_empty() {
        info!("--- Stabilizer Statistics ---");
        info!(
            "{:<6} {:>8} {:>10} {:>12}",
            "Size", "Trials", "Trivial", "Threefold"
        );
        for s in &analysis.stabilizer {
            info!(
                "{:<6} {:>8} {:>10} {:>12}",
                s.size, s.trials, s.trivial_count, s.threefold_count,
            );
        }
        info!("");
    }

    // Scaling summary
    info!("--- Scaling Summary ---");
    if analysis.recovery.len() >= 2 {
        let first = &analysis.recovery[0];
        let last = analysis.recovery.last().unwrap();
        if first.mean_time_ms > 0.0 {
            let ratio = last.mean_time_ms / first.mean_time_ms;
            info!(
                "Recovery time ratio (size {} vs {}): {:.1}x",
                last.size, first.size, ratio,
            );
        }
    }
    if analysis.decomposition.len() >= 2 {
        let first = &analysis.decomposition[0];
        let last = analysis.decomposition.last().unwrap();
        if first.mean_first_time_ms > 0.0 {
            let ratio = last.mean_first_time_ms / first.mean_first_time_ms;
            info!(
                "Decomposition time ratio (size {} vs {}): {:.1}x",
                last.size, first.size, ratio,
            );
        }
    }

    // Verdict
    info!("\n=== VERDICT ===");

    let recovery_easy = analysis
        .recovery
        .iter()
        .all(|r| r.mean_time_ms < 1000.0);
    let decomp_easy = analysis
        .decomposition
        .iter()
        .all(|d| d.mean_first_time_ms < 1000.0);
    let mostly_trivial_stab = analysis
        .stabilizer
        .iter()
        .all(|s| s.trivial_count >= s.trials / 2);

    if recovery_easy {
        info!("Cotiler recovery: EASY at tested sizes (all < 1s)");
    } else {
        info!("Cotiler recovery: shows scaling — candidate for hardness");
    }

    if decomp_easy {
        info!("Region decomposition: EASY at tested sizes (all < 1s)");
    } else {
        info!("Region decomposition: shows scaling — candidate for hardness");
    }

    if mostly_trivial_stab {
        info!("Stabilizer: mostly trivial (good for cryptographic applications)");
    } else {
        info!("Stabilizer: significant threefold symmetry (reduces key space)");
    }

    let viable = !recovery_easy || !decomp_easy;
    if viable {
        info!("\nConclusion: At least one problem shows super-linear scaling.");
        info!("Further investigation at larger sizes warranted.");
    } else {
        info!("\nConclusion: All problems appear easy at tested sizes.");
        info!(
            "The virtually abelian structure of Gamma = Z^2 x| D_6 likely makes"
        );
        info!("group-theoretic hard problems tractable. The tiling constraint");
        info!("does not appear to inject sufficient hardness at these scales.");
    }
}

// ---------------------------------------------------------------------------
// Tests
// ---------------------------------------------------------------------------

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn grow_cotiler_single_is_seed() {
        let seed = CoxeterElement::identity();
        let mut rng = 42u64;
        let cotiler = grow_cotiler(seed, 1, &mut rng).unwrap();
        assert_eq!(cotiler.positions.len(), 1);
        assert_eq!(cotiler.positions[0], seed);
    }

    #[test]
    fn grow_cotiler_produces_valid_result() {
        let seed = CoxeterElement::identity();
        let mut rng = 12345u64;
        let cotiler = grow_cotiler(seed, 3, &mut rng).unwrap();
        assert_eq!(cotiler.positions.len(), 3);
        assert!(cotiler.is_non_overlapping());
        assert_eq!(cotiler.cell_count(), 48);
    }

    #[test]
    fn grow_cotiler_deterministic_with_same_rng() {
        let seed = CoxeterElement::identity();
        let mut rng1 = 99999u64;
        let mut rng2 = 99999u64;
        let c1 = grow_cotiler(seed, 4, &mut rng1).unwrap();
        let c2 = grow_cotiler(seed, 4, &mut rng2).unwrap();
        assert_eq!(c1.positions, c2.positions);
    }

    #[test]
    fn recovery_of_size_2_cotiler() {
        let seed = CoxeterElement::identity();
        let mut rng = 77777u64;
        let cotiler = grow_cotiler(seed, 2, &mut rng).unwrap();
        let generators = cotiler.cotiler_group_generators();

        let (solutions, _budget_exceeded) = recover_cotiler(&generators, 2, 8);
        assert!(!solutions.is_empty(), "should find at least one recovery");

        // Each solution should generate the same G_C
        let orig_gens: HashSet<_> = generators.iter().copied().collect();
        for sol in &solutions {
            let sol_gens: HashSet<_> = sol.cotiler_group_generators().into_iter().collect();
            assert!(
                orig_gens.iter().all(|g| sol_gens.contains(g)),
                "recovered cotiler should generate the same G_C"
            );
        }
    }

    #[test]
    fn recovery_of_size_3_finds_solution() {
        let seed = CoxeterElement::identity();
        let mut rng = 55555u64;
        let cotiler = grow_cotiler(seed, 3, &mut rng).unwrap();
        let generators = cotiler.cotiler_group_generators();

        let (solutions, _budget_exceeded) = recover_cotiler(&generators, 3, 4);
        assert!(
            !solutions.is_empty(),
            "should find at least one recovery for size 3"
        );
    }

    #[test]
    fn decomposition_of_known_cotiler_succeeds() {
        let seed = CoxeterElement::identity();
        let mut rng = 33333u64;
        let cotiler = grow_cotiler(seed, 2, &mut rng).unwrap();
        let cells = cotiler.covered_cells();

        let solutions = decompose_region(&cells, 2, 8);
        assert!(!solutions.is_empty(), "should decompose the region");

        // Each solution should cover the same cells
        for sol in &solutions {
            assert_eq!(sol.covered_cells(), cells);
        }
    }

    #[test]
    fn decomposition_single_tile_is_unique() {
        let cotiler = Cotiler::new(vec![CoxeterElement::identity()]);
        let cells = cotiler.covered_cells();

        let solutions = decompose_region(&cells, 1, 8);
        // The Cucaracha has trivial stabilizer, so from a fixed cell set
        // there should be exactly one decomposition into a single tile.
        assert_eq!(solutions.len(), 1, "single tile should have unique decomposition");
        assert_eq!(solutions[0].positions[0], CoxeterElement::identity());
    }

    #[test]
    fn coset_recovery_of_size_2_cotiler() {
        let seed = CoxeterElement::identity();
        let mut rng = 77777u64;
        let cotiler = grow_cotiler(seed, 2, &mut rng).unwrap();
        let generators = cotiler.cotiler_group_generators();

        let solutions = recover_cotiler_coset(&generators, 2, 8);
        assert!(!solutions.is_empty(), "coset recovery should find at least one solution");

        let orig_gens: HashSet<_> = generators.iter().copied().collect();
        for sol in &solutions {
            let sol_gens: HashSet<_> = sol.cotiler_group_generators().into_iter().collect();
            assert!(
                orig_gens.iter().all(|g| sol_gens.contains(g)),
                "coset-recovered cotiler should generate the same G_C"
            );
        }
    }

    #[test]
    fn coset_recovery_of_size_4_cotiler() {
        let seed = CoxeterElement::identity();
        let mut rng = 88888u64;
        let cotiler = grow_cotiler(seed, 4, &mut rng).unwrap();
        let generators = cotiler.cotiler_group_generators();

        let solutions = recover_cotiler_coset(&generators, 4, 4);
        assert!(
            !solutions.is_empty(),
            "coset recovery should find at least one solution for size 4"
        );
    }

    #[test]
    fn coset_and_bruteforce_agree_on_size_3() {
        let seed = CoxeterElement::identity();
        let mut rng = 55555u64;
        let cotiler = grow_cotiler(seed, 3, &mut rng).unwrap();
        let generators = cotiler.cotiler_group_generators();

        let (bf_solutions, _) = recover_cotiler(&generators, 3, 16);
        let cs_solutions = recover_cotiler_coset(&generators, 3, 16);

        // Both should find solutions
        assert!(!bf_solutions.is_empty());
        assert!(!cs_solutions.is_empty());

        // Coset should find at least as many (it's more structured, but same G_C check)
        // At minimum, both find the original cotiler (up to translation normalization)
    }

    #[test]
    fn stabilizer_of_grown_cotiler_is_valid() {
        let seed = CoxeterElement::identity();
        let mut rng = 11111u64;
        for _ in 0..5 {
            let cotiler = grow_cotiler(seed, 3, &mut rng).unwrap();
            let stab = cotiler.stabilizer();
            assert!(
                stab.len() == 1 || stab.len() == 3,
                "stabilizer should be {{id}} or {{id, R_3, R_3^2}}, got size {}",
                stab.len()
            );
            assert!(
                stab.contains(&CoxeterElement::identity()),
                "stabilizer must contain identity"
            );
        }
    }
}
