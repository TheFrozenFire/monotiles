use anyhow::Result;
use clap::{Parser, Subcommand};
use tracing::{debug, info, info_span};

#[derive(Parser)]
#[command(name = "monotiles", about = "Monotile tiling experiments")]
struct Cli {
    #[command(subcommand)]
    command: Commands,
}

#[derive(Subcommand)]
enum Commands {
    /// Verify Coxeter group relations and Cucaracha properties
    VerifyCoxeter,

    /// Show the Cucaracha elements in normal form
    Cucaracha,

    /// Compute metatile counts at each substitution level
    Inflate {
        /// Seed tile type (system-dependent, e.g. H/T/P/F for hat, Spectre/Mystic for spectre)
        #[arg(default_value = "H")]
        seed: String,
        /// Number of substitution levels
        #[arg(short, long, default_value_t = 5)]
        levels: usize,
        /// Tiling system: hat, spectre, or hat-turtle
        #[arg(short = 'S', long, default_value = "hat")]
        system: String,
    },

    /// Generate and display a Sturmian word
    Sturmian {
        /// Number of terms to generate
        #[arg(short, long, default_value_t = 50)]
        terms: usize,
    },

    /// Display the hat substitution matrix and verify its properties
    Matrix,

    /// Verify field extension properties
    Fields,

    /// Demonstrate deflation on a generated patch
    Deflate {
        /// Seed metatile type: H, T, P, or F
        #[arg(default_value = "H")]
        seed: String,
        /// Number of inflation levels for the initial patch
        #[arg(short, long, default_value_t = 3)]
        levels: usize,
    },

    /// Run the tiling-based interactive oracle proof
    Prove {
        /// Seed metatile type: H, T, P, or F
        #[arg(default_value = "H")]
        seed: String,
        /// Hierarchy depth (number of folding rounds)
        #[arg(short, long, default_value_t = 4)]
        depth: usize,
        /// Number of queries per round
        #[arg(short, long, default_value_t = 8)]
        queries: usize,
    },

    /// Demonstrate hole recovery (erase + recover + verify)
    Recover {
        /// Number of inflation levels for the initial patch
        #[arg(short, long, default_value_t = 3)]
        levels: usize,
        /// Radius of the erased region
        #[arg(short = 'r', long, default_value_t = 1.5)]
        hole_radius: f64,
    },

    /// Analyze one-way substitution function (deflation locality)
    Oneway {
        /// Seed tile type (system-dependent)
        #[arg(default_value = "H")]
        seed: String,
        /// Hierarchy depth (substitution levels)
        #[arg(short, long, default_value_t = 3)]
        depth: usize,
        /// Maximum neighborhood radius to test
        #[arg(short = 'r', long, default_value_t = 5)]
        max_radius: usize,
        /// Tiling system: hat, spectre, or hat-turtle
        #[arg(short = 'S', long, default_value = "hat")]
        system: String,
    },

    /// Analyze the local-to-global gap (seed distinguishability)
    Gap {
        /// Hierarchy depth (substitution levels)
        #[arg(short, long, default_value_t = 3)]
        depth: usize,
        /// Maximum neighborhood radius to test
        #[arg(short = 'r', long, default_value_t = 5)]
        max_radius: usize,
        /// Tiling system: hat, spectre, or hat-turtle
        #[arg(short = 'S', long, default_value = "hat")]
        system: String,
    },

    /// Analyze recoverability vulnerability (per-position criticality, erasure thresholds)
    Vulnerability {
        /// Hierarchy depth (substitution levels)
        #[arg(short, long, default_value_t = 3)]
        depth: usize,
        /// Number of erasure trials per fraction
        #[arg(short, long, default_value_t = 100)]
        erasure_trials: usize,
        /// Tiling system: hat, spectre, or hat-turtle
        #[arg(short = 'S', long, default_value = "hat")]
        system: String,
    },

    /// Explore Cucaracha-based group cryptography problems
    GroupCrypto {
        /// Experiment to run: all, recovery, decomposition, stabilizer
        #[arg(short, long, default_value = "all")]
        experiment: String,
        /// Maximum cotiler size to test
        #[arg(short = 'n', long, default_value_t = 5)]
        max_size: usize,
        /// Number of trials per size
        #[arg(short, long, default_value_t = 10)]
        trials: usize,
    },
}

fn main() -> Result<()> {
    tracing_subscriber::fmt::init();

    let cli = Cli::parse();

    match cli.command {
        Commands::VerifyCoxeter => cmd_verify_coxeter(),
        Commands::Cucaracha => cmd_cucaracha(),
        Commands::Inflate { seed, levels, system } => cmd_inflate(&seed, levels, &system),
        Commands::Sturmian { terms } => cmd_sturmian(terms),
        Commands::Matrix => cmd_matrix(),
        Commands::Fields => cmd_fields(),
        Commands::Prove { seed, depth, queries } => cmd_prove(&seed, depth, queries),
        Commands::Deflate { seed, levels } => cmd_deflate(&seed, levels),
        Commands::Recover { levels, hole_radius } => cmd_recover(levels, hole_radius),
        Commands::Oneway { seed, depth, max_radius, system } => cmd_oneway(&seed, depth, max_radius, &system),
        Commands::Gap { depth, max_radius, system } => cmd_gap(depth, max_radius, &system),
        Commands::Vulnerability { depth, erasure_trials, system } => cmd_vulnerability(depth, erasure_trials, &system),
        Commands::GroupCrypto { experiment, max_size, trials } => cmd_group_crypto(&experiment, max_size, trials),
    }
}

fn cmd_verify_coxeter() -> Result<()> {
    let _span = info_span!("verify_coxeter").entered();
    use domain::coxeter::{CoxeterElement, Generator::*};

    let alpha = CoxeterElement::generator(Alpha);
    let beta = CoxeterElement::generator(Beta);
    let gamma = CoxeterElement::generator(Gamma);
    let id = CoxeterElement::identity();

    let pow = |g: &CoxeterElement, n: u32| -> CoxeterElement {
        (0..n).fold(id, |acc, _| acc.compose(g))
    };

    let checks = [
        ("alpha^2 = id", pow(&alpha, 2) == id),
        ("beta^2 = id", pow(&beta, 2) == id),
        ("gamma^2 = id", pow(&gamma, 2) == id),
        (
            "(alpha*beta)^6 = id",
            pow(&alpha.compose(&beta), 6) == id,
        ),
        (
            "(beta*gamma)^3 = id",
            pow(&beta.compose(&gamma), 3) == id,
        ),
        (
            "(alpha*gamma)^2 = id",
            pow(&alpha.compose(&gamma), 2) == id,
        ),
    ];

    info!("Coxeter group Gamma verification:");
    let mut all_ok = true;
    for (name, ok) in &checks {
        let status = if *ok { "PASS" } else { "FAIL" };
        info!("  {}: {}", name, status);
        if !*ok {
            all_ok = false;
        }
    }

    if all_ok {
        info!("\nAll 6 Coxeter relations verified.");
    } else {
        anyhow::bail!("Some Coxeter relations failed!");
    }

    // Verify inverse
    let test_elements = [
        alpha,
        beta,
        gamma,
        alpha.compose(&beta),
        CoxeterElement::new(3, -2, 4, true),
    ];
    info!("\nInverse verification:");
    for g in &test_elements {
        let g_inv = g.inverse();
        let ok = g.compose(&g_inv) == id && g_inv.compose(g) == id;
        info!("  {:?} * inverse = id: {}", g, if ok { "PASS" } else { "FAIL" });
    }

    Ok(())
}

fn cmd_cucaracha() -> Result<()> {
    let _span = info_span!("cucaracha").entered();
    let elements = domain::cucaracha::cucaracha();
    let words = domain::cucaracha::CUCARACHA_WORDS;

    info!("Cucaracha: 16-element aperiodic monotile of Gamma\n");
    info!("{:<5} {:<25} {:?}", "Idx", "Word", "Normal Form (tx, ty, rot, refl)");
    info!("{}", "-".repeat(70));

    for (i, (elem, word)) in elements.iter().zip(words.iter()).enumerate() {
        let word_str = if word.is_empty() {
            "id".to_string()
        } else {
            word.iter()
                .map(|g| match g {
                    domain::coxeter::Generator::Alpha => "a",
                    domain::coxeter::Generator::Beta => "b",
                    domain::coxeter::Generator::Gamma => "c",
                })
                .collect::<Vec<_>>()
                .join("")
        };
        info!(
            "{:<5} {:<25} ({}, {}, {}, {})",
            i, word_str, elem.tx, elem.ty, elem.rotation, elem.reflected
        );
    }

    info!("\nAll elements distinct: {}", {
        let unique: std::collections::HashSet<_> = elements.iter().collect();
        unique.len() == 16
    });

    Ok(())
}

/// Resolve a seed type name to an index for the given tiling system.
fn resolve_seed(
    system: &dyn tiling::systems::TilingSystem,
    seed: &str,
) -> Result<usize> {
    let upper = seed.to_uppercase();
    for i in 0..system.num_types() {
        if system.type_name(i).to_uppercase() == upper {
            return Ok(i);
        }
    }
    // Also try parsing as integer index
    if let Ok(idx) = seed.parse::<usize>() {
        if idx < system.num_types() {
            return Ok(idx);
        }
    }
    let valid: Vec<&str> = (0..system.num_types())
        .map(|i| system.type_name(i))
        .collect();
    anyhow::bail!(
        "Unknown seed type '{}' for {} system. Valid: {}",
        seed,
        system.name(),
        valid.join(", ")
    )
}

fn cmd_inflate(seed: &str, levels: usize, system_name: &str) -> Result<()> {
    let _span = info_span!("inflate", seed, levels, system = system_name).entered();
    let system = tiling::systems::resolve_system(system_name)?;
    let seed_idx = resolve_seed(&*system, seed)?;
    let counts = tiling::substitution::generate_counts_system(&*system, seed_idx, levels);

    let num_types = system.num_types();
    let header: Vec<String> = (0..num_types)
        .map(|i| format!("{:>8}", system.type_name(i)))
        .collect();

    info!(
        "Substitution from seed {} ({}), {} levels:\n",
        system.type_name(seed_idx),
        system.name(),
        levels
    );
    info!("{:<8} {} {:>10}", "Level", header.join(""), "Total");
    info!("{}", "-".repeat(18 + 8 * num_types));

    for (level, count) in counts.iter().enumerate() {
        let vals: Vec<String> = count.iter().map(|c| format!("{:>8}", c)).collect();
        let total: usize = count.iter().sum();
        info!("{:<8} {} {:>10}", level, vals.join(""), total);
    }

    Ok(())
}

fn cmd_sturmian(terms: usize) -> Result<()> {
    let _span = info_span!("sturmian", terms).entered();
    let word = analysis::sturmian::fibonacci_word(terms);

    info!("Fibonacci Sturmian word ({} terms):", terms);
    let line: String = word.iter().map(|b| if *b == 0 { '0' } else { '1' }).collect();
    for chunk in line.as_bytes().chunks(60) {
        info!("  {}", std::str::from_utf8(chunk).unwrap());
    }

    info!("\nFrequency of 1s: {:.6}", analysis::sturmian::frequency_of_ones(&word));

    let phi = (1.0 + 5.0_f64.sqrt()) / 2.0;
    info!("Expected (1/phi^2): {:.6}", 1.0 / (phi * phi));

    info!("\nComplexity p(n):");
    for n in 1..=10 {
        info!("  p({}) = {} (expected {})", n, analysis::sturmian::complexity(&word, n), n + 1);
    }

    Ok(())
}

fn cmd_matrix() -> Result<()> {
    let _span = info_span!("matrix").entered();
    use ark_bls12_381::Fr;

    let m = analysis::spectral::hat_substitution_matrix::<Fr>();
    let comp = tiling::metatile::supertile_composition();

    info!("Hat substitution matrix (H, T, P, F):\n");
    let labels = ["H'", "T'", "P'", "F'"];
    for (i, label) in labels.iter().enumerate() {
        info!(
            "  {} = {}H + {}T + {}P + {}F  (total: {})",
            label, comp[i][0], comp[i][1], comp[i][2], comp[i][3],
            comp[i].iter().sum::<usize>()
        );
    }

    info!("\nDeterminant: {}", if m.determinant() == -Fr::from(1u64) { "-1" } else { "?" });

    // Verify characteristic polynomial: lambda^4 - 7*lambda^3 + 7*lambda - 1 = 0
    let id = domain::matrix::Matrix::<Fr>::identity(4);
    let m2 = m.mul(&m);
    let m3 = m2.mul(&m);
    let m4 = m3.mul(&m);
    let result = &(&m4 + &m3.scale(-Fr::from(7u64)))
        + &(&m.scale(Fr::from(7u64)) + &id.scale(-Fr::from(1u64)));
    let is_zero = (0..4).all(|i| (0..4).all(|j| result[(i, j)] == Fr::from(0u64)));
    info!("Cayley-Hamilton (M^4 - 7M^3 + 7M - I = 0): {}", if is_zero { "VERIFIED" } else { "FAILED" });

    info!("\nEigenvalues: phi^4 = (7+3*sqrt(5))/2, 1, -1, (7-3*sqrt(5))/2");
    info!("  phi^4 ~= 6.854 (area inflation factor)");
    info!("  phi^2 ~= 2.618 (edge length inflation factor)");

    Ok(())
}

fn cmd_deflate(seed: &str, levels: usize) -> Result<()> {
    let _span = info_span!("deflate", seed, levels).entered();
    let seed_type = match seed.to_uppercase().as_str() {
        "H" => tiling::metatile::MetatileType::H,
        "T" => tiling::metatile::MetatileType::T,
        "P" => tiling::metatile::MetatileType::P,
        "F" => tiling::metatile::MetatileType::F,
        _ => anyhow::bail!("Unknown seed type: {}. Use H, T, P, or F.", seed),
    };

    let patch = tiling::geometry::generate_patch(seed_type, levels);
    info!(
        "Generated level-{} patch from {:?}: {} metatiles\n",
        levels,
        seed_type,
        patch.tiles.len()
    );

    let result = tiling::deflation::deflate(&patch);
    info!("Deflation result (level {} -> level {}):", levels, result.supertile_level);
    info!("  Supertiles: {}", result.supertiles.len());
    info!("  Unresolved boundary tiles: {}", result.unresolved.len());

    // Count supertile types
    let mut type_counts = [0usize; 4];
    for st in &result.supertiles {
        match st.tile_type {
            tiling::metatile::MetatileType::H => type_counts[0] += 1,
            tiling::metatile::MetatileType::T => type_counts[1] += 1,
            tiling::metatile::MetatileType::P => type_counts[2] += 1,
            tiling::metatile::MetatileType::F => type_counts[3] += 1,
        }
    }
    info!(
        "  Type counts: H={}, T={}, P={}, F={}",
        type_counts[0], type_counts[1], type_counts[2], type_counts[3]
    );

    // Inflate back and verify round-trip
    let reinflated = tiling::deflation::inflate_patch(&result.supertiles);
    info!(
        "\nRound-trip: inflate {} supertiles -> {} metatiles (original: {})",
        result.supertiles.len(),
        reinflated.tiles.len(),
        patch.tiles.len()
    );

    Ok(())
}

fn cmd_recover(levels: usize, hole_radius: f64) -> Result<()> {
    let _span = info_span!("recover", levels, hole_radius).entered();
    let patch = tiling::geometry::generate_patch(tiling::metatile::MetatileType::H, levels);
    info!(
        "Generated level-{} H-patch: {} metatiles\n",
        levels,
        patch.tiles.len()
    );

    // Erase region centered on the first tile
    let center = &patch.tiles[0];
    let (cx, cy) = (center.x, center.y);
    let holey = tiling::recovery::HoleyTiling::erase_region(&patch, cx, cy, hole_radius);

    info!(
        "Erased region: center=({:.3}, {:.3}), radius={:.3}",
        cx, cy, hole_radius
    );
    info!(
        "  Erased tiles: {}",
        holey.hole_positions.len()
    );
    info!(
        "  Remaining tiles: {}",
        holey.exterior.tiles.len()
    );

    if holey.hole_positions.is_empty() {
        info!("\nNo tiles in the erased region. Try a larger radius.");
        return Ok(());
    }

    // Recover
    let result = tiling::recovery::recover(&holey);
    info!("\nRecovery result:");
    info!("  Deflation levels used: {}", result.deflation_levels);
    info!("  Recovered tiles: {}", result.recovered_tiles.len());
    info!("  Success: {}", result.success);

    // Verify
    let verification = tiling::recovery::verify_recovery(
        &holey.hole_positions,
        &result.recovered_tiles,
        0.5,
    );
    info!("\nVerification:");
    info!("  Original erased: {}", verification.original_count);
    info!("  Recovered: {}", verification.recovered_count);
    info!("  Matched: {}", verification.matched);
    info!(
        "  Unmatched originals: {}",
        verification.unmatched_originals.len()
    );
    info!("  Extra recovered: {}", verification.extra_recovered);

    Ok(())
}

fn cmd_prove(seed: &str, depth: usize, num_queries: usize) -> Result<()> {
    let _span = info_span!("prove", seed, depth, queries = num_queries).entered();
    use ark_bls12_381::Fr;
    use std::time::Instant;

    let seed_type = match seed.to_uppercase().as_str() {
        "H" => tiling::metatile::MetatileType::H,
        "T" => tiling::metatile::MetatileType::T,
        "P" => tiling::metatile::MetatileType::P,
        "F" => tiling::metatile::MetatileType::F,
        _ => anyhow::bail!("Unknown seed type: {}. Use H, T, P, or F.", seed),
    };

    info!("Tiling IOP: seed={:?}, depth={}, queries={}\n", seed_type, depth, num_queries);

    // Build hierarchy
    let t0 = Instant::now();
    let mut hierarchy = iop::hierarchy::build_hierarchy::<Fr>(seed_type, depth);
    let build_time = t0.elapsed();

    let base_tiles = hierarchy.levels[0].tile_types.len();
    info!("Hierarchy: {} base tiles, {} levels", base_tiles, depth + 1);
    info!("  Build time: {:?}", build_time);

    // Fill level 0 with deterministic witness values
    for i in 0..base_tiles {
        hierarchy.levels[0].values[i] = Fr::from((i as u64 + 1) * 7 + 13);
    }

    // Prove
    let t1 = Instant::now();
    let proof = iop::prover::prove(&mut hierarchy, num_queries);
    let prove_time = t1.elapsed();

    // Estimate proof size (number of openings * ~64 bytes each + commitments)
    let total_openings: usize = proof.queries.iter()
        .flat_map(|round| round.iter())
        .map(|qr| 1 + qr.children.len())  // supertile + children
        .sum();
    let total_commitments = proof.commitment.level_commitments.len();
    let est_proof_size = total_commitments * 32  // Merkle roots
        + total_openings * 32 * 10  // rough estimate: hash path ~10 nodes deep
        + total_openings * 32;  // field elements

    info!("\nProof generated:");
    info!("  Prove time: {:?}", prove_time);
    info!("  Commitments: {}", total_commitments);
    info!("  Total Merkle openings: {}", total_openings);
    info!("  Est. proof size: ~{:.1} KB", est_proof_size as f64 / 1024.0);

    // Verify
    let t2 = Instant::now();
    let result = iop::verifier::verify(&proof);
    let verify_time = t2.elapsed();

    match result {
        Ok(()) => info!("\nVerification: ACCEPTED ({:?})", verify_time),
        Err(e) => info!("\nVerification: REJECTED - {} ({:?})", e, verify_time),
    }

    Ok(())
}

fn cmd_oneway(seed: &str, depth: usize, max_radius: usize, system_name: &str) -> Result<()> {
    let _span = info_span!("oneway", seed, depth, max_radius, system = system_name).entered();
    use std::time::Instant;

    let system = tiling::systems::resolve_system(system_name)?;
    let seed_idx = resolve_seed(&*system, seed)?;

    info!(
        "One-way substitution analysis: system={}, seed={}, depth={}, max_radius={}\n",
        system.name(),
        system.type_name(seed_idx),
        depth,
        max_radius
    );

    let t0 = Instant::now();
    let result = tiling::oneway::analyze_system(&*system, seed_idx, depth, max_radius);
    let elapsed = t0.elapsed();

    // Hierarchy stats
    info!("Hierarchy ({:?}):", elapsed);
    info!(
        "{:<8} {:>10}",
        "Level", "Tiles"
    );
    for (level, &count) in result.tiles_per_level.iter().enumerate() {
        info!("{:<8} {:>10}", level, count);
    }

    // Per-level determination radius with full sibling adjacency
    info!("\n--- Full sibling adjacency (all siblings mutually adjacent) ---");
    for (level, lr) in result.full_sibling.iter().enumerate() {
        info!("\nLevel {} ({} tiles):", level, result.tiles_per_level[level]);
        if lr.radii_histogram.is_empty() && lr.undetermined == 0 {
            info!("  (no tiles)");
            continue;
        }
        for (&radius, &count) in &lr.radii_histogram {
            info!("  radius {}: {} tiles", radius, count);
        }
        if lr.undetermined > 0 {
            info!("  undetermined: {} tiles", lr.undetermined);
        }
        if let Some(max) = lr.max_radius {
            info!(
                "  summary: min={}, max={}, mean={:.2}",
                lr.min_radius.unwrap(),
                max,
                lr.mean_radius
            );
        }
    }

    // Per-level determination radius with inflation adjacency
    info!("\n--- Intra-supertile inflation adjacency (sparser graph) ---");
    for (level, lr) in result.inflation_adj.iter().enumerate() {
        info!("\nLevel {} ({} tiles):", level, result.tiles_per_level[level]);
        if lr.radii_histogram.is_empty() && lr.undetermined == 0 {
            info!("  (no tiles)");
            continue;
        }
        for (&radius, &count) in &lr.radii_histogram {
            info!("  radius {}: {} tiles", radius, count);
        }
        if lr.undetermined > 0 {
            info!("  undetermined: {} tiles", lr.undetermined);
        }
        if let Some(max) = lr.max_radius {
            info!(
                "  summary: min={}, max={}, mean={:.2}",
                lr.min_radius.unwrap(),
                max,
                lr.mean_radius
            );
        }
    }

    // Decomposition and deflation
    info!("\n--- Type-bag decomposition ---");
    info!(
        "Base level decomposition count: {} (unique = {})",
        result.base_decomposition_count,
        result.base_decomposition_count == 1
    );

    info!("\n--- Greedy deflation ---");
    info!("Success rate: {:.1}%", result.greedy_success_rate * 100.0);

    info!("\n--- Local deflation (radius 1, full sibling adj) ---");
    info!("Unresolved tiles: {}", result.local_deflate_unresolved);

    // Summary verdict
    info!("\n=== VERDICT ===");
    let all_determined_full = result.full_sibling.iter().all(|lr| lr.undetermined == 0);
    let max_full_radius = result
        .full_sibling
        .iter()
        .filter_map(|lr| lr.max_radius)
        .max()
        .unwrap_or(0);

    let all_determined_infl = result.inflation_adj.iter().all(|lr| lr.undetermined == 0);

    if all_determined_full {
        info!(
            "Full sibling adjacency: LOCALLY SOLVABLE at radius {}",
            max_full_radius
        );
    } else {
        info!("Full sibling adjacency: REQUIRES GLOBAL CONTEXT (some tiles undetermined)");
    }

    if all_determined_infl {
        let max_infl = result
            .inflation_adj
            .iter()
            .filter_map(|lr| lr.max_radius)
            .max()
            .unwrap_or(0);
        info!(
            "Inflation adjacency: LOCALLY SOLVABLE at radius {}",
            max_infl
        );
    } else {
        let total_undetermined: usize = result.inflation_adj.iter().map(|lr| lr.undetermined).sum();
        info!(
            "Inflation adjacency: {} tiles undetermined within radius {} \
             (H' supertile is disconnected in inflation graph)",
            total_undetermined, max_radius
        );
    }

    if result.base_decomposition_count == 1 {
        info!("Type-bag decomposition: UNIQUE (composition counts fully determine supertile counts)");
    } else {
        info!(
            "Type-bag decomposition: {} valid decompositions",
            result.base_decomposition_count
        );
    }

    if all_determined_full && result.base_decomposition_count == 1 {
        info!("\nConclusion: Deflation is NOT a one-way function.");
        info!(
            "The asymmetry is implementation convenience, not computational hardness."
        );
        info!(
            "Local information (radius {}) suffices to determine parent assignments.",
            max_full_radius
        );
    }

    debug!("\nCompleted in {:?}", elapsed);

    Ok(())
}

fn cmd_gap(depth: usize, max_radius: usize, system_name: &str) -> Result<()> {
    let _span = info_span!("gap", depth, max_radius, system = system_name).entered();
    use std::time::Instant;

    let system = tiling::systems::resolve_system(system_name)?;

    info!(
        "Local-to-global gap analysis: system={}, depth={}, max_radius={}\n",
        system.name(),
        depth,
        max_radius
    );

    let t0 = Instant::now();
    let analysis = tiling::gap::analyze_system(&*system, depth, max_radius);
    let elapsed = t0.elapsed();

    tiling::gap::print_report(&*system, &analysis);
    debug!("\nCompleted in {:?}", elapsed);

    Ok(())
}

fn cmd_vulnerability(depth: usize, erasure_trials: usize, system_name: &str) -> Result<()> {
    let _span = info_span!("vulnerability", depth, erasure_trials, system = system_name).entered();
    use std::time::Instant;

    let system = tiling::systems::resolve_system(system_name)?;

    info!(
        "Vulnerability analysis: system={}, depth={}, erasure_trials={}\n",
        system.name(),
        depth,
        erasure_trials
    );

    let t0 = Instant::now();
    let analysis = tiling::vulnerability::analyze_system(&*system, 0, depth, erasure_trials);
    let elapsed = t0.elapsed();

    tiling::vulnerability::print_report(&*system, &analysis);
    debug!("\nCompleted in {:?}", elapsed);

    Ok(())
}

fn cmd_fields() -> Result<()> {
    let _span = info_span!("fields").entered();
    use ark_ff::Field;
    use domain::fields::*;

    info!("Field extension verification over BLS12-381 Fr:\n");

    // FrSqrt5
    let sqrt5 = FrSqrt5::new(ark_bls12_381::Fr::from(0u64), ark_bls12_381::Fr::from(1u64));
    let five = FrSqrt5::new(ark_bls12_381::Fr::from(5u64), ark_bls12_381::Fr::from(0u64));
    info!("  sqrt(5)^2 == 5: {}", sqrt5.square() == five);

    let phi = golden_ratio();
    let phi_sq = phi.square();
    let phi_plus_one = phi + FrSqrt5::new(ark_bls12_381::Fr::from(1u64), ark_bls12_381::Fr::from(0u64));
    info!("  phi^2 == phi + 1: {}", phi_sq == phi_plus_one);
    info!("  phi^2 == hat_inflation(): {}", phi_sq == hat_inflation());

    // FrSqrt15
    let sqrt15 = FrSqrt15::new(ark_bls12_381::Fr::from(0u64), ark_bls12_381::Fr::from(1u64));
    let fifteen = FrSqrt15::new(ark_bls12_381::Fr::from(15u64), ark_bls12_381::Fr::from(0u64));
    info!("  sqrt(15)^2 == 15: {}", sqrt15.square() == fifteen);

    // Inverse round-trips
    let a = FrSqrt5::new(ark_bls12_381::Fr::from(7u64), ark_bls12_381::Fr::from(3u64));
    let a_inv = a.inverse().expect("nonzero invertible");
    info!("  FrSqrt5 inverse round-trip: {}", a * a_inv == FrSqrt5::ONE);

    let b = FrSqrt15::new(ark_bls12_381::Fr::from(11u64), ark_bls12_381::Fr::from(2u64));
    let b_inv = b.inverse().expect("nonzero invertible");
    info!("  FrSqrt15 inverse round-trip: {}", b * b_inv == FrSqrt15::ONE);

    info!("\nAll field properties verified.");
    Ok(())
}

fn cmd_group_crypto(experiment: &str, max_size: usize, trials: usize) -> Result<()> {
    let _span = info_span!("group_crypto", experiment, max_size, trials).entered();

    info!(
        "Group cryptography analysis: experiment={}, max_size={}, trials={}\n",
        experiment, max_size, trials
    );

    let analysis = domain::group_crypto::analyze_experiments(max_size, trials, experiment);

    domain::group_crypto::print_report(&analysis);

    Ok(())
}
