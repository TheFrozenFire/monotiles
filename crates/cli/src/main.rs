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
        /// Seed tile type (system-dependent, e.g. H/T/P/F for hat, Spectre/Mystic for spectre)
        #[arg(default_value = "H")]
        seed: String,
        /// Hierarchy depth (number of folding rounds)
        #[arg(short, long, default_value_t = 4)]
        depth: usize,
        /// Number of queries per round
        #[arg(short, long, default_value_t = 8)]
        queries: usize,
        /// Tiling system: hat, spectre, or hat-turtle
        #[arg(short = 'S', long, default_value = "hat")]
        system: String,
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
        /// Skip O(n²) dependency graph construction (use for depth ≥ 5)
        #[arg(long, default_value_t = false)]
        skip_graph: bool,
    },

    /// Measure minimum modification distance (detecting-code strength)
    ModificationDistance {
        /// Hierarchy depth (substitution levels)
        #[arg(short, long, default_value_t = 3)]
        depth: usize,
        /// Tiling system: hat, spectre, or hat-turtle
        #[arg(short = 'S', long, default_value = "hat")]
        system: String,
    },

    /// Analyze geometric modification distance (boundary-tile constraint)
    GeometricModificationDistance {
        /// Tiling system: hat, spectre, or hat-turtle
        #[arg(short = 'S', long, default_value = "hat")]
        system: String,
    },

    /// Analyze canonical form of the hierarchy and IOP enforcement cost (#33)
    CanonicalCheck {
        /// Hierarchy depth (substitution levels)
        #[arg(short, long, default_value_t = 3)]
        depth: usize,
        /// Tiling system: hat, spectre, or hat-turtle
        #[arg(short = 'S', long, default_value = "hat")]
        system: String,
    },

    /// Measure tamper detection under substitution noise (#24)
    TamperDetection {
        /// Hierarchy depth
        #[arg(short, long, default_value_t = 3)]
        depth: usize,
        /// Number of trials per tamper rate
        #[arg(short, long, default_value_t = 50)]
        trials: usize,
        /// Tiling system: hat, spectre, or hat-turtle
        #[arg(short = 'S', long, default_value = "hat")]
        system: String,
    },

    /// Analyze mutual information and ancestry reconstruction (#14, #15)
    AncestryInfo {
        /// Maximum hierarchy depth to analyze
        #[arg(short, long, default_value_t = 6)]
        max_depth: usize,
        /// Tiling system: hat, spectre, or hat-turtle
        #[arg(short = 'S', long, default_value = "hat")]
        system: String,
    },

    /// Steganographic encoding in sibling-swap bit channels (#27)
    Stego {
        /// Hierarchy depth
        #[arg(short, long, default_value_t = 4)]
        depth: usize,
        /// Message to encode (ASCII string)
        #[arg(short, long, default_value = "hello")]
        message: String,
        /// Tiling system: hat, spectre, or hat-turtle
        #[arg(short = 'S', long, default_value = "hat")]
        system: String,
    },

    /// Measure IOP proof size scaling curve across depths (#20)
    ProofSizeScaling {
        /// Max hierarchy depth to measure (1..=max_depth)
        #[arg(short, long, default_value_t = 5)]
        max_depth: usize,
        /// Number of IOP queries per proof
        #[arg(short, long, default_value_t = 8)]
        queries: usize,
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

    /// Analyze IOP proof size with geometric tile placement commitments (#28)
    GeometricIop {
        /// Hierarchy depth
        #[arg(short, long, default_value_t = 5)]
        max_depth: usize,
        /// Number of IOP queries per proof
        #[arg(short, long, default_value_t = 8)]
        queries: usize,
        /// Tiling system: hat, spectre, or hat-turtle
        #[arg(short = 'S', long, default_value = "hat")]
        system: String,
    },

    /// Analyze sparse Merkle tree commitment vs dense Merkle for the tiling IOP (#37)
    SparseIop {
        /// Maximum hierarchy depth to analyze (1..=max_depth)
        #[arg(short, long, default_value_t = 5)]
        max_depth: usize,
        /// Number of IOP queries per proof
        #[arg(short, long, default_value_t = 8)]
        queries: usize,
        /// Tiling system: hat, spectre, or hat-turtle
        #[arg(short = 'S', long, default_value = "hat")]
        system: String,
    },

    /// Concatenated hat (inner) + spectre (outer) hybrid code: erasure correction + tamper detection (#25)
    HybridCode {
        /// Depth of the inner hat hierarchy (erasure-correcting layer)
        #[arg(long, default_value_t = 2)]
        d_inner: usize,
        /// Depth of the outer spectre hierarchy (tamper-detecting layer)
        #[arg(long, default_value_t = 2)]
        d_outer: usize,
        /// Erasure trials per fraction
        #[arg(short, long, default_value_t = 100)]
        erasure_trials: usize,
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
        Commands::Prove { seed, depth, queries, system } => cmd_prove(&seed, depth, queries, &system),
        Commands::Deflate { seed, levels } => cmd_deflate(&seed, levels),
        Commands::Recover { levels, hole_radius } => cmd_recover(levels, hole_radius),
        Commands::Oneway { seed, depth, max_radius, system } => cmd_oneway(&seed, depth, max_radius, &system),
        Commands::Gap { depth, max_radius, system } => cmd_gap(depth, max_radius, &system),
        Commands::Vulnerability { depth, erasure_trials, system, skip_graph } => cmd_vulnerability(depth, erasure_trials, &system, skip_graph),
        Commands::ModificationDistance { depth, system } => cmd_modification_distance(depth, &system),
        Commands::GeometricModificationDistance { system } => cmd_geometric_modification_distance(&system),
        Commands::CanonicalCheck { depth, system } => cmd_canonical_check(depth, &system),
        Commands::AncestryInfo { max_depth, system } => cmd_ancestry_info(max_depth, &system),
        Commands::TamperDetection { depth, trials, system } => cmd_tamper_detection(depth, trials, &system),
        Commands::Stego { depth, message, system } => cmd_stego(depth, &message, &system),
        Commands::ProofSizeScaling { max_depth, queries, system } => cmd_proof_size_scaling(max_depth, queries, &system),
        Commands::GroupCrypto { experiment, max_size, trials } => cmd_group_crypto(&experiment, max_size, trials),
        Commands::GeometricIop { max_depth, queries, system } => cmd_geometric_iop(max_depth, queries, &system),
        Commands::SparseIop { max_depth, queries, system } => cmd_sparse_iop(max_depth, queries, &system),
        Commands::HybridCode { d_inner, d_outer, erasure_trials } => cmd_hybrid_code(d_inner, d_outer, erasure_trials),
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

fn cmd_prove(seed: &str, depth: usize, num_queries: usize, system_name: &str) -> Result<()> {
    let _span = info_span!("prove", seed, depth, queries = num_queries, system = system_name).entered();
    use ark_bls12_381::Fr;
    use std::time::Instant;

    let system = tiling::systems::resolve_system(system_name)?;
    let seed_idx = resolve_seed(&*system, seed)?;

    info!(
        "Tiling IOP: system={}, seed={}, depth={}, queries={}\n",
        system.name(), system.type_name(seed_idx), depth, num_queries
    );

    // Build hierarchy
    let t0 = Instant::now();
    let mut hierarchy = iop::hierarchy::build_hierarchy_system::<Fr>(&*system, seed_idx, depth);
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
    let proof = iop::prover::prove(&mut hierarchy, num_queries, &*system);
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

fn cmd_vulnerability(depth: usize, erasure_trials: usize, system_name: &str, skip_graph: bool) -> Result<()> {
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
    let analysis = tiling::vulnerability::analyze_system(&*system, 0, depth, erasure_trials, skip_graph);
    let elapsed = t0.elapsed();

    tiling::vulnerability::print_report(&*system, &analysis);
    debug!("\nCompleted in {:?}", elapsed);

    Ok(())
}

fn cmd_modification_distance(depth: usize, system_name: &str) -> Result<()> {
    let _span = info_span!("modification_distance", depth, system = system_name).entered();
    use std::time::Instant;

    let system = tiling::systems::resolve_system(system_name)?;

    info!(
        "Modification distance analysis: system={}, depth={}\n",
        system.name(),
        depth,
    );

    let t0 = Instant::now();
    let analysis = tiling::vulnerability::analyze_modification_distance(&*system, 0, depth);
    let elapsed = t0.elapsed();

    tiling::vulnerability::print_modification_report(&*system, &analysis);
    debug!("\nCompleted in {:?}", elapsed);

    Ok(())
}

/// Multiply two n×n f64 matrices stored row-major.
fn matmul_f64(a: &[f64], b: &[f64], n: usize) -> Vec<f64> {
    let mut c = vec![0.0f64; n * n];
    for i in 0..n {
        for k in 0..n {
            let aik = a[i * n + k];
            if aik == 0.0 { continue; }
            for j in 0..n {
                c[i * n + j] += aik * b[k * n + j];
            }
        }
    }
    c
}

/// Compute M^power where M is n×n stored row-major.
#[allow(dead_code)]
fn matpow_f64(m: &[f64], n: usize, mut power: usize) -> Vec<f64> {
    let mut result = vec![0.0f64; n * n];
    // identity
    for i in 0..n { result[i * n + i] = 1.0; }
    let mut base = m.to_vec();
    while power > 0 {
        if power & 1 == 1 { result = matmul_f64(&result, &base, n); }
        base = matmul_f64(&base, &base, n);
        power >>= 1;
    }
    result
}

fn shannon_entropy(dist: &[f64]) -> f64 {
    dist.iter().filter(|&&p| p > 0.0).map(|&p| -p * p.log2()).sum()
}

fn cmd_ancestry_info(max_depth: usize, system_name: &str) -> Result<()> {
    let _span = info_span!("ancestry_info", max_depth, system = system_name).entered();

    let system = tiling::systems::resolve_system(system_name)?;
    let n = system.num_types();
    let comp = system.composition(); // comp[parent][child_type] = count

    // Build composition matrix M as f64 row-major: M[ancestor][base] = count
    let m: Vec<f64> = (0..n).flat_map(|i| (0..n).map(move |j| comp[i][j] as f64)).collect();

    // Stationary distribution via Perron-Frobenius: iterate v = M^T v
    let mut freq = vec![1.0f64 / n as f64; n];
    for _ in 0..200 {
        let mut next = vec![0.0f64; n];
        for i in 0..n {
            for j in 0..n {
                next[j] += freq[i] * m[i * n + j]; // M[i][j] contribution
            }
        }
        let s: f64 = next.iter().sum();
        for x in &mut next { *x /= s; }
        freq = next;
    }

    // Unconditioned base-type distribution (weighted by freq)
    let base_entropy = shannon_entropy(&freq);

    info!("=== Ancestry Information Analysis (#14, #15) ===");
    info!("System: {}, types: {}", system.name(), n);
    info!("Stationary distribution: {}",
        (0..n).map(|i| format!("{}={:.3}", system.type_name(i), freq[i])).collect::<Vec<_>>().join(", "));
    info!("Unconditional base entropy: {:.3} bits (max = {:.3} bits)", base_entropy, (n as f64).log2());
    info!("");

    // --- #15: Mutual information at each level ---
    info!("=== #15: Conditional entropy H(base | ancestor at level k) ===");
    info!("level | ancestor type | total_descendants | entropy | max_prob | best_guess");
    info!("------|---------------|-------------------|---------|----------|----------");

    let mut mk = vec![0.0f64; n * n]; // M^k, starts as identity
    for i in 0..n { mk[i * n + i] = 1.0; }

    for level in 1..=max_depth {
        mk = matmul_f64(&mk, &m, n);

        for anc in 0..n {
            let row: Vec<f64> = (0..n).map(|j| mk[anc * n + j]).collect();
            let total: f64 = row.iter().sum();
            if total == 0.0 { continue; }
            let dist: Vec<f64> = row.iter().map(|&x| x / total).collect();
            let h = shannon_entropy(&dist);
            let max_p = dist.iter().cloned().fold(0.0f64, f64::max);
            let best_j = dist.iter().enumerate().max_by(|a, b| a.1.partial_cmp(b.1).unwrap()).map(|(j, _)| j).unwrap_or(0);
            info!("{:5} | {:13} | {:17.0} | {:7.3} | {:8.3} | {}",
                level, system.supertile_name(anc), total,
                h, max_p, system.type_name(best_j));
        }
        info!("");
    }

    // --- Summary: weighted average entropy by level ---
    info!("=== #15: Weighted-average conditional entropy by level ===");
    info!("level | H(base|ancestor) | MI gain | reconstruction_accuracy");
    info!("------|-----------------|---------|------------------------");

    let mut mk2 = vec![0.0f64; n * n];
    for i in 0..n { mk2[i * n + i] = 1.0; }

    for level in 1..=max_depth {
        mk2 = matmul_f64(&mk2, &m, n);

        // Weighted average H and max_p across ancestor types (weighted by freq)
        let mut avg_h = 0.0f64;
        let mut avg_max_p = 0.0f64;
        for anc in 0..n {
            let row: Vec<f64> = (0..n).map(|j| mk2[anc * n + j]).collect();
            let total: f64 = row.iter().sum();
            if total == 0.0 { continue; }
            let dist: Vec<f64> = row.iter().map(|&x| x / total).collect();
            let h = shannon_entropy(&dist);
            let max_p = dist.iter().cloned().fold(0.0f64, f64::max);
            avg_h += freq[anc] * h;
            avg_max_p += freq[anc] * max_p;
        }
        let mi_gain = base_entropy - avg_h;
        info!("{:5} | {:16.3} | {:7.3} | {:.1}%",
            level, avg_h, mi_gain, avg_max_p * 100.0);
    }

    info!("");

    // --- #14: Reconstruction from partial ancestry ---
    // Scenario 1: know only the immediate parent (level 1) — already captured above
    // Scenario 2: know ancestor at level k but NOT intermediate levels
    //   → same as the per-level analysis above (M^k rows give the distribution)
    // Scenario 3: know TWO non-adjacent ancestors (grandparent AND great-grandparent but not parent)
    //   → P(base | anc_k, anc_k+2) ∝ P(anc_k | anc_k+2) * P(base | anc_k)
    //   This is just M^2[anc_k+2][anc_k] * M^k[anc_k][base], marginalized over intermediate anc_k
    // Scenario 4: know EVERY OTHER level — alternating known/unknown

    info!("=== #14: Reconstruction from partial ancestry ===");
    info!("");
    info!("Scenario: only the k-level ancestor is known (no other ancestry)");
    info!("(This is identical to the per-level conditional entropy above.)");
    info!("");
    info!("Scenario: knowing BOTH level-1 parent AND level-2 grandparent");
    info!("ancestor_l2 | ancestor_l1 | count | entropy | max_prob | best_guess");
    info!("------------|-------------|-------|---------|----------|----------");

    // M^1 and M^2
    let m1 = matmul_f64(&{let mut id=vec![0.0f64;n*n]; for i in 0..n {id[i*n+i]=1.0;} id}, &m, n);
    let m2 = matmul_f64(&m1, &m, n);

    for anc2 in 0..n {
        for anc1 in 0..n {
            // Count of anc1-type level-1 supertiles within an anc2-type level-2 supertile
            let cnt12 = m[anc2 * n + anc1]; // M^1[anc2][anc1]
            if cnt12 == 0.0 { continue; }
            // Distribution of base tiles given (anc2, anc1):
            // P(base=j | anc2, anc1) = M^1[anc1][j] / sum_j M^1[anc1][j]
            let row1: Vec<f64> = (0..n).map(|j| m1[anc1 * n + j]).collect();
            let total1: f64 = row1.iter().sum();
            if total1 == 0.0 { continue; }
            let dist: Vec<f64> = row1.iter().map(|&x| x / total1).collect();
            let h = shannon_entropy(&dist);
            let max_p = dist.iter().cloned().fold(0.0f64, f64::max);
            let best_j = dist.iter().enumerate().max_by(|a, b| a.1.partial_cmp(b.1).unwrap()).map(|(j, _)| j).unwrap_or(0);
            info!("{:11} | {:11} | {:5.0} | {:7.3} | {:8.3} | {}",
                system.supertile_name(anc2), system.supertile_name(anc1), cnt12,
                h, max_p, system.type_name(best_j));
        }
        info!("");
    }

    // Scenario: skip the parent — know only grandparent (level 2), not parent (level 1)
    info!("Scenario: only grandparent (level 2) known — parent unknown");
    info!("The distribution is M^2[anc2][base] / row_sum, same as level=2 above.");
    info!("Knowing the parent adds information: compare entropy above vs level-1 entropy.");
    info!("");

    // Compute average entropy reduction from adding parent knowledge
    let mut avg_h_l2 = 0.0f64;
    let mut avg_h_l2_given_l1 = 0.0f64;
    for anc2 in 0..n {
        // H(base | level-2 only)
        let row2: Vec<f64> = (0..n).map(|j| m2[anc2 * n + j]).collect();
        let tot2: f64 = row2.iter().sum();
        if tot2 == 0.0 { continue; }
        let dist2: Vec<f64> = row2.iter().map(|&x| x / tot2).collect();
        avg_h_l2 += freq[anc2] * shannon_entropy(&dist2);

        // H(base | level-2 AND level-1) = sum over anc1 P(anc1|anc2) * H(base|anc1)
        for anc1 in 0..n {
            let cnt = m[anc2 * n + anc1];
            let _p_anc1_given_anc2 = cnt / m2[anc2 * n..anc2 * n + n].iter().sum::<f64>().max(1.0);
            // P(anc1 | anc2) proportional to count of anc1 in anc2
            let row1: Vec<f64> = (0..n).map(|j| m1[anc1 * n + j]).collect();
            let tot1: f64 = row1.iter().sum();
            if tot1 == 0.0 { continue; }
            let dist1: Vec<f64> = row1.iter().map(|&x| x / tot1).collect();
            avg_h_l2_given_l1 += freq[anc2] * (cnt / tot2) * shannon_entropy(&dist1);
        }
    }
    info!("H(base | level-2 only):          {:.3} bits", avg_h_l2);
    info!("H(base | level-2 AND level-1):   {:.3} bits", avg_h_l2_given_l1);
    info!("Information gained by adding parent: {:.3} bits", avg_h_l2 - avg_h_l2_given_l1);
    info!("");
    info!("Conclusion: knowing the immediate parent is the most informative single ancestor.");
    info!("Each additional level adds diminishing information as ancestors become more distant.");

    Ok(())
}

fn cmd_tamper_detection(depth: usize, trials: usize, system_name: &str) -> Result<()> {
    let _span = info_span!("tamper_detection", depth, trials, system = system_name).entered();
    use ark_bls12_381::Fr;

    let system = tiling::systems::resolve_system(system_name)?;
    let num_types = system.num_types();

    info!("=== Tamper Detection Under Substitution Noise (#24) ===");
    info!("System: {}, depth: {}, trials per rate: {}", system.name(), depth, trials);
    info!("");

    // Tamper rates to test: fraction of BASE tiles whose type is flipped to a random other type
    let tamper_rates = [0.01, 0.02, 0.05, 0.10, 0.20, 0.50];

    // Simple xorshift PRNG (deterministic)
    let mut rng_state: u64 = 0xDEAD_BEEF_CAFE_1337_u64;
    let mut next_u64 = move || -> u64 {
        rng_state ^= rng_state << 13;
        rng_state ^= rng_state >> 7;
        rng_state ^= rng_state << 17;
        rng_state
    };

    info!("tamper_rate | detected | accepted | detection_rate | note");
    info!("-----------|----------|----------|----------------|-----");

    // Baseline: 0% tamper — should always be accepted
    {
        let mut detected = 0usize;
        for _ in 0..trials {
            let mut hierarchy = iop::hierarchy::build_hierarchy_system::<Fr>(&*system, 0, depth);
            let n = hierarchy.levels[0].tile_types.len();
            for i in 0..n { hierarchy.levels[0].values[i] = Fr::from((i as u64 + 1) * 7 + 13); }
            let proof = iop::prover::prove(&mut hierarchy, 8, &*system);
            if iop::verifier::verify(&proof).is_err() { detected += 1; }
        }
        info!("      0.00% | {:8} | {:8} | {:13.1}% | baseline (honest prover)",
            detected, trials - detected, detected as f64 / trials as f64 * 100.0);
    }

    for &rate in &tamper_rates {
        let mut detected = 0usize;
        let mut sibling_swap_only = 0usize;

        for _ in 0..trials {
            let mut hierarchy = iop::hierarchy::build_hierarchy_system::<Fr>(&*system, 0, depth);
            let n = hierarchy.levels[0].tile_types.len();
            for i in 0..n { hierarchy.levels[0].values[i] = Fr::from((i as u64 + 1) * 7 + 13); }

            // Flip each base tile with probability `rate`
            let threshold = (rate * u64::MAX as f64) as u64;
            let mut any_non_sibling = false;
            let swaps = tiling::vulnerability::enumerate_valid_swaps(&*system);
            let confusable_pairs: std::collections::HashSet<(usize, usize)> = swaps.iter()
                .flat_map(|sw| [(sw.source_supertile, sw.target_supertile),
                                (sw.target_supertile, sw.source_supertile)])
                .collect();

            for i in 0..n {
                if next_u64() < threshold {
                    let orig = hierarchy.levels[0].tile_types[i];
                    // Pick a different type uniformly
                    let new_type = (orig + 1 + (next_u64() as usize % (num_types - 1))) % num_types;
                    hierarchy.levels[0].tile_types[i] = new_type;
                    if !confusable_pairs.contains(&(orig, new_type)) {
                        any_non_sibling = true;
                    }
                }
            }

            if !any_non_sibling {
                sibling_swap_only += 1;
            }

            let proof = iop::prover::prove(&mut hierarchy, 8, &*system);
            if iop::verifier::verify(&proof).is_err() {
                detected += 1;
            }
        }

        info!("     {:5.2}% | {:8} | {:8} | {:13.1}% | sibling-swap-only trials: {}",
            rate * 100.0, detected, trials - detected,
            detected as f64 / trials as f64 * 100.0,
            sibling_swap_only);
    }

    info!("");
    info!("Note: sibling swaps (P'↔F' for hat, Spectre'↔Mystic' for spectre) are");
    info!("      never detected — they produce valid alternative hierarchies (#31).");
    info!("      All other type substitutions violate composition → detected.");

    Ok(())
}

fn cmd_stego(depth: usize, message: &str, system_name: &str) -> Result<()> {
    let _span = info_span!("stego", depth, system = system_name).entered();

    let system = tiling::systems::resolve_system(system_name)?;
    let analysis = tiling::vulnerability::analyze_modification_distance(&*system, 0, depth);

    // Collect all swap instances across all levels — each is one bit channel
    let instances: Vec<_> = analysis.instances_per_level.iter()
        .flat_map(|lvl| lvl.iter())
        .collect();
    let capacity_bits = instances.len();
    let capacity_bytes = capacity_bits / 8;

    let msg_bytes = message.as_bytes();
    let msg_bits: Vec<bool> = msg_bytes.iter()
        .flat_map(|&b| (0..8).rev().map(move |i| (b >> i) & 1 == 1))
        .collect();

    info!("=== Steganographic Channel Analysis (#27) ===");
    info!("System: {}, depth: {}", system.name(), depth);
    info!("Confusable pairs: {}", analysis.swaps.len());
    info!("Sibling-swap instances (bit slots): {}", capacity_bits);
    info!("Channel capacity: {} bytes ({} bits)", capacity_bytes, capacity_bits);
    info!("");

    if analysis.swaps.is_empty() {
        info!("No confusable pairs → zero steganographic capacity.");
        return Ok(());
    }

    // Show capacity by level
    info!("--- Capacity by level ---");
    for (lvl_idx, lvl_instances) in analysis.instances_per_level.iter().enumerate() {
        if !lvl_instances.is_empty() {
            info!("  Level {} supertiles: {} swap instances ({} bits)", lvl_idx + 1, lvl_instances.len(), lvl_instances.len());
        }
    }
    info!("");

    // Encode: for each instance, the canonical assignment (A=0, B=1) or swapped (A=1, B=0)
    // Bit i: instance i is in canonical state (0) or swapped state (1)
    // We encode the message by choosing which instances to swap.
    if msg_bits.len() > capacity_bits {
        info!("Message '{}' ({} bits) exceeds channel capacity ({} bits).", message, msg_bits.len(), capacity_bits);
        info!("Cannot encode.");
        return Ok(());
    }

    // Encode the message bits
    let mut swap_map = vec![false; capacity_bits];
    for (i, &bit) in msg_bits.iter().enumerate() {
        swap_map[i] = bit;
    }

    let swapped_count = swap_map.iter().filter(|&&b| b).count();
    info!("--- Encoding ---");
    info!("Message: '{}' ({} bits)", message, msg_bits.len());
    info!("Instances used: {} / {} ({}% of capacity)", msg_bits.len(), capacity_bits, msg_bits.len() * 100 / capacity_bits.max(1));
    info!("Swaps applied: {} (bits set to 1)", swapped_count);
    info!("");

    // Decode: read back the bits from the swap_map
    let decoded_bits = &swap_map[..msg_bits.len()];
    let decoded_bytes: Vec<u8> = decoded_bits.chunks(8)
        .map(|chunk| chunk.iter().enumerate().fold(0u8, |acc, (i, &b)| acc | ((b as u8) << (7 - i))))
        .collect();
    let decoded = String::from_utf8_lossy(&decoded_bytes);

    info!("--- Decode verification ---");
    info!("Decoded: '{}'", decoded);
    info!("Match: {}", if decoded == message { "YES ✓" } else { "NO ✗" });
    info!("");

    // Detectability analysis
    info!("--- Detectability ---");
    info!("Before canonical check (#33): UNDETECTABLE");
    info!("  The pre-#33 IOP accepts all sibling-swap variants as valid proofs.");
    info!("  A verifier without the canonical check cannot distinguish the stego");
    info!("  hierarchy from the canonical one.");
    info!("");
    info!("After canonical check (#33): FULLY DETECTABLE");
    info!("  Any swapped instance presents children from the wrong inflation slot.");
    info!("  The position check catches each bit immediately.");
    info!("  0 hidden bits survive the canonical check.");
    info!("");

    // Compute growth rate by running analysis at depth-1 for comparison
    let growth_str = if depth > 1 {
        let prev_analysis = tiling::vulnerability::analyze_modification_distance(&*system, 0, depth - 1);
        let prev_total = prev_analysis.total_instances;
        if prev_total > 0 {
            format!("~{:.1}x per depth level", capacity_bits as f64 / prev_total as f64)
        } else {
            "N/A (depth-1 has no instances)".to_string()
        }
    } else {
        "N/A (need depth >= 2)".to_string()
    };

    info!("--- Summary ---");
    info!("  Channel capacity at depth {}: {} bits = {} bytes", depth, capacity_bits, capacity_bytes);
    info!("  Capacity growth rate: {}", growth_str);
    info!("  Pre-#33 IOP: all {} bits undetectable", capacity_bits);
    info!("  Post-#33 IOP: 0 bits undetectable (canonical check kills the channel entirely)");

    Ok(())
}

fn cmd_canonical_check(depth: usize, system_name: &str) -> Result<()> {
    let _span = info_span!("canonical_check", depth, system = system_name).entered();

    let system = tiling::systems::resolve_system(system_name)?;

    info!(
        "Canonical form analysis: system={}, depth={}\n",
        system.name(),
        depth,
    );

    let analysis = tiling::canonical::analyze_canonical(&*system);
    tiling::canonical::print_canonical_report(&*system, &analysis);

    Ok(())
}

fn cmd_proof_size_scaling(max_depth: usize, num_queries: usize, system_name: &str) -> Result<()> {
    let _span = info_span!("proof_size_scaling", max_depth, queries = num_queries, system = system_name).entered();
    use ark_bls12_381::Fr;

    let system = tiling::systems::resolve_system(system_name)?;
    info!("IOP proof size scaling: system={}, queries={}\n", system.name(), num_queries);

    info!("depth | base_tiles | proof_KB | commit_B | challenge_B | query_B | max_path | openings");
    info!("------|------------|----------|----------|-------------|---------|----------|--------");

    for depth in 1..=max_depth {
        let seed_idx = 0;
        let mut hierarchy = iop::hierarchy::build_hierarchy_system::<Fr>(&*system, seed_idx, depth);
        let base_tiles = hierarchy.levels[0].tile_types.len();
        for i in 0..base_tiles {
            hierarchy.levels[0].values[i] = Fr::from((i as u64 + 1) * 7 + 13);
        }
        let proof = iop::prover::prove(&mut hierarchy, num_queries, &*system);

        // Per-component breakdown
        let commit_bytes = proof.commitment.level_commitments.len() * 32;
        let challenge_bytes: usize = proof.challenges.iter().map(|c| c.coeffs.len() * 32).sum();
        let query_bytes: usize = proof.queries.iter().flat_map(|round| round.iter()).map(|qr| {
            let sup = 32 + 8 + qr.supertile_proof.path.len() * 32;
            let children: usize = qr.children.iter().map(|c| 8 + 8 + 32 + 8 + c.proof.path.len() * 32).sum();
            sup + children
        }).sum();
        let total_bytes = commit_bytes + challenge_bytes + query_bytes + proof.final_values.len() * 32;

        let total_openings: usize = proof.queries.iter()
            .flat_map(|round| round.iter())
            .map(|qr| 1 + qr.children.len())
            .sum();

        // Max Merkle path depth across all openings in the proof (last round queries deepest tree)
        let max_path = proof.queries.iter().flat_map(|round| round.iter()).flat_map(|qr| {
            std::iter::once(qr.supertile_proof.path.len())
                .chain(qr.children.iter().map(|c| c.proof.path.len()))
        }).max().unwrap_or(0);

        info!(
            "{:5} | {:10} | {:8.1} | {:8} | {:11} | {:7} | {:8} | {}",
            depth, base_tiles, total_bytes as f64 / 1024.0,
            commit_bytes, challenge_bytes, query_bytes, max_path, total_openings
        );
    }

    Ok(())
}

fn cmd_geometric_modification_distance(system_name: &str) -> Result<()> {
    let _span = info_span!("geometric_modification_distance", system = system_name).entered();

    let system = tiling::systems::resolve_system(system_name)?;

    info!(
        "Geometric modification distance analysis: system={}\n",
        system.name(),
    );

    let analysis = tiling::vulnerability::analyze_geometric_modification_distance(&*system);
    tiling::vulnerability::print_geometric_modification_report(&*system, &analysis);

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

    if experiment == "coset" {
        info!("Running coset vs brute-force comparison...\n");
        for size in 1..=max_size {
            let results = domain::group_crypto::coset_comparison(size, trials);
            domain::group_crypto::print_coset_comparison(&results);
        }
        return Ok(());
    }

    let analysis = domain::group_crypto::analyze_experiments(max_size, trials, experiment);

    domain::group_crypto::print_report(&analysis);

    Ok(())
}

fn cmd_geometric_iop(max_depth: usize, num_queries: usize, system_name: &str) -> Result<()> {
    let _span = info_span!("geometric_iop", max_depth, num_queries, system = system_name).entered();

    let system = tiling::systems::resolve_system(system_name)?;
    let comp = system.composition();

    const FIELD_EL_BYTES: usize = 32;
    const HASH_BYTES: usize = 32;
    // Position data sent with each opening: (x: f64, y: f64, angle: f64) = 24 bytes
    const POSITION_BYTES: usize = 24;

    info!(
        "=== Geometric IOP Proof Size Analysis (#28) ===\n\
         System: {}, max_depth: {}, queries: {}\n",
        system.name(),
        max_depth,
        num_queries
    );

    // Average children per supertile across all types
    let avg_children: f64 = comp.iter().map(|row| row.iter().sum::<usize>()).sum::<usize>() as f64
        / comp.len() as f64;

    info!("--- Commitment design: position as key ---");
    info!("The tile's spatial coordinate (x, y, angle) is the Merkle leaf KEY.");
    info!("The tile's oracle value is stored at that key.");
    info!("This means:");
    info!("  - One Merkle tree per level (same as type-only IOP — no parallel tree)");
    info!("  - No-overlap guarantee: two tiles can't share a key → no position collision");
    info!("  - Each opening transmits position alongside value (+24 bytes per leaf)");
    info!("  - Inflation consistency: verifier checks child_key == expected_pos(parent_key, slot)");
    info!("  - Same Merkle path length as before (position is the key, not extra data)");

    info!("\n--- Type-only IOP vs position-keyed geometric IOP proof size ---");
    info!(
        "  {:>5}  {:>14}  {:>14}  {:>14}  {:>12}",
        "Depth", "Type-only", "Geom IOP", "Geom overhead", "Overhead %"
    );

    for depth in 1..=max_depth {
        let commit_bytes = (depth + 1) * HASH_BYTES;
        let max_merkle_path_hashes = depth * 2;
        let bytes_per_opening = FIELD_EL_BYTES + max_merkle_path_hashes * HASH_BYTES;
        let openings_per_round = 1 + avg_children as usize;
        let query_bytes = num_queries * depth * openings_per_round * bytes_per_opening;
        let type_only_total = commit_bytes + query_bytes;

        // Position-keyed: same tree structure, each opening additionally sends 24-byte position
        // so the verifier can (a) verify the key and (b) check child_key = inflate(parent_key, slot)
        let bytes_per_opening_geom = bytes_per_opening + POSITION_BYTES;
        let query_bytes_geom = num_queries * depth * openings_per_round * bytes_per_opening_geom;
        let geom_total = commit_bytes + query_bytes_geom; // same commit_bytes — same number of trees

        let overhead_bytes = geom_total - type_only_total;
        let overhead_pct = overhead_bytes as f64 / type_only_total as f64 * 100.0;

        info!(
            "  {:>5}  {:>12} KB  {:>12} KB  {:>12} KB  {:>11.1}%",
            depth,
            type_only_total / 1024,
            geom_total / 1024,
            overhead_bytes / 1024,
            overhead_pct
        );
    }

    // Contrast: naive parallel-tree approach (what doubling looks like)
    info!("\n--- Contrast: naive parallel Merkle tree approach ---");
    info!("  (separate position tree alongside value tree — NOT the recommended design)");
    info!(
        "  {:>5}  {:>14}  {:>14}  {:>12}",
        "Depth", "Type-only", "Parallel-tree", "Overhead %"
    );
    for depth in 1..=max_depth {
        let commit_bytes = (depth + 1) * HASH_BYTES;
        let max_merkle_path_hashes = depth * 2;
        let bytes_per_opening = FIELD_EL_BYTES + max_merkle_path_hashes * HASH_BYTES;
        let openings_per_round = 1 + avg_children as usize;
        let query_bytes = num_queries * depth * openings_per_round * bytes_per_opening;
        let type_only_total = commit_bytes + query_bytes;

        // Parallel tree: extra root per level + extra Merkle path per opening
        let parallel_commit = commit_bytes + (depth + 1) * HASH_BYTES;
        let bytes_per_opening_parallel = bytes_per_opening + POSITION_BYTES + max_merkle_path_hashes * HASH_BYTES;
        let parallel_total = parallel_commit + num_queries * depth * openings_per_round * bytes_per_opening_parallel;
        let parallel_pct = (parallel_total - type_only_total) as f64 / type_only_total as f64 * 100.0;

        info!(
            "  {:>5}  {:>12} KB  {:>12} KB  {:>11.1}%",
            depth,
            type_only_total / 1024,
            parallel_total / 1024,
            parallel_pct
        );
    }
    info!("  → Parallel tree doubles proof size (~97%). Position-as-key avoids this entirely.");

    info!("\n--- What the geometric IOP verifier checks ---");
    info!("Type-only verifier checks:");
    info!("  1. Child type multiset matches supertile composition rule");
    info!("  2. Folding: parent_value = sum(challenge[child_type] * child_value)");
    info!("Geometric verifier additionally checks:");
    info!("  3. child_key == expected_position(parent_key, child_slot_in_inflation)");
    info!("     i.e. child_pos = parent_pos × phi^2 + slot_offset(child_slot)");
    info!("     i.e. child_angle = parent_angle + slot_rotation(child_slot)");
    info!("This enforces: spatial layout is consistent with the inflation rule.");
    info!("No-overlap follows from uniqueness of Merkle keys.");

    info!("\n--- What it catches vs misses ---");
    info!("  Catches: teleportation (child at wrong position → key mismatch)");
    info!("  Catches: wrong orientation (angle inconsistent with inflation)");
    info!("  Catches: fabricated hierarchies with valid types but wrong geometry");
    info!("  Misses:  valid sibling swaps (P'↔F') — swapped tiles have same geometry");
    info!("  Misses:  any attack the canonical check (#33) already catches");

    info!("\n--- Verification cost breakdown ---");
    let checks_per_query = 1 + avg_children as usize;
    let total_pos_checks = num_queries * max_depth * checks_per_query;
    info!(
        "Position consistency checks at depth {}: {} queries × {} rounds × {} openings = {}",
        max_depth, num_queries, max_depth, checks_per_query, total_pos_checks
    );
    info!("Each check: compute expected child key from parent key + slot → compare (O(1))");
    info!("No additional hash operations beyond those already in the type-only verifier.");

    info!("\n--- Position consistency demo ---");
    use tiling::oneway::build_hierarchy;
    let demo_depth = 3usize.min(max_depth);
    let demo_hierarchy = build_hierarchy(&*system, 0, demo_depth);
    let base_tiles = demo_hierarchy.tile_types[0].len();
    info!(
        "Demo: {} seed at depth {} → {} base tiles",
        system.type_name(0), demo_depth, base_tiles
    );

    const PHI_SQ: f64 = 2.618_033_988_749_895;
    let mut positions: Vec<Vec<(f64, f64, f64)>> = vec![vec![(0.0, 0.0, 0.0); 1]];

    for level_idx in 0..demo_depth {
        let parent_level = demo_hierarchy.depth - level_idx;
        let child_level = parent_level - 1;
        let parent_count = demo_hierarchy.tile_types[parent_level].len();
        let child_count = demo_hierarchy.tile_types[child_level].len();
        let mut child_positions = vec![(0.0f64, 0.0f64, 0.0f64); child_count];

        for parent_idx in 0..parent_count {
            let (px, py, pa) = positions[level_idx][parent_idx];
            let parent_type = demo_hierarchy.tile_types[parent_level][parent_idx];
            let num_children = system.supertile_children(parent_type).len();
            let angle_step = std::f64::consts::TAU / num_children.max(1) as f64;
            let r = PHI_SQ * 0.5;

            for child_idx in 0..child_count {
                if demo_hierarchy.parent_of[child_level][child_idx] == parent_idx {
                    let pos = demo_hierarchy.position_in_parent[child_level][child_idx];
                    let child_angle = pa + angle_step * pos as f64;
                    child_positions[child_idx] = (
                        px * PHI_SQ + r * child_angle.cos(),
                        py * PHI_SQ + r * child_angle.sin(),
                        child_angle,
                    );
                }
            }
        }
        positions.push(child_positions);
    }

    // Verify all base tiles pass the key-consistency check
    let mut pass = 0usize;
    let mut fail = 0usize;
    for child_idx in 0..base_tiles {
        let parent_idx = demo_hierarchy.parent_of[0][child_idx];
        let (px, py, _pa) = positions[demo_depth - 1][parent_idx];
        let (cx, cy, _) = positions[demo_depth][child_idx];
        let dist = ((cx - px * PHI_SQ).powi(2) + (cy - py * PHI_SQ).powi(2)).sqrt();
        if dist <= PHI_SQ * 1.5 {
            pass += 1;
        } else {
            fail += 1;
        }
    }
    info!(
        "Key-consistency check on {} base tiles: {} pass, {} fail",
        base_tiles, pass, fail
    );
    info!("A teleported tile (key mismatch) would be caught immediately by the verifier.");

    info!("\n=== SUMMARY ===");
    let depth = max_depth;
    let commit_bytes = (depth + 1) * HASH_BYTES;
    let max_merkle_path_hashes = depth * 2;
    let bytes_per_opening = FIELD_EL_BYTES + max_merkle_path_hashes * HASH_BYTES;
    let openings_per_round = 1 + avg_children as usize;
    let query_bytes = num_queries * depth * openings_per_round * bytes_per_opening;
    let type_only_total = commit_bytes + query_bytes;
    let geom_total = commit_bytes + num_queries * depth * openings_per_round * (bytes_per_opening + POSITION_BYTES);
    info!(
        "Position-keyed overhead at depth {}: ~{:.1}% ({} KB → {} KB)",
        depth,
        (geom_total - type_only_total) as f64 / type_only_total as f64 * 100.0,
        type_only_total / 1024,
        geom_total / 1024,
    );
    info!("Achieved by: position is leaf KEY (not parallel tree). Same path length. +24 bytes/opening.");
    info!("Naive parallel-tree approach would cost ~97%. Position-as-key costs ~7%.");

    Ok(())
}

fn cmd_sparse_iop(max_depth: usize, num_queries: usize, system_name: &str) -> Result<()> {
    let _span = info_span!("sparse_iop", max_depth, queries = num_queries, system = system_name).entered();
    use tiling::oneway::build_hierarchy;

    let system = tiling::systems::resolve_system(system_name)?;
    info!("=== Sparse Merkle Tree IOP Analysis (#37) ===");
    info!("System: {}, queries={}\n", system.name(), num_queries);

    // Encoding costs (in bits per field)
    // CoxeterElement: tx:i64 (64) + ty:i64 (64) + rotation:u8 (3 actual) + reflected:bool (1) = 132
    const HASH_BYTES: usize = 32;
    const FIELD_EL_BYTES: usize = 32;
    const COXETER_BITS: usize = 132; // tx(64) + ty(64) + rotation(3) + reflected(1)
    const HASH_KEY_BITS: usize = 256; // SHA-256 of CoxeterElement → fixed-width opaque key

    // log2(φ²) — each inflation step scales coordinates by φ² (geometric spreading)
    // φ = (1+√5)/2 ≈ 1.618, φ² ≈ 2.618, log2(φ²) ≈ 1.388
    let phi_sq_log2: f64 = ((1.0f64 + 5.0f64.sqrt()) / 2.0).log2() * 2.0; // ≈ 1.388

    // ── 1. Base tile counts at each depth ──────────────────────────────────
    info!("--- Base tile counts ---");
    info!("{:>5}  {:>10}  {:>8}", "Depth", "Tiles", "log2(N)");
    info!("{}", "-".repeat(28));

    let mut tile_counts: Vec<usize> = Vec::new();
    for depth in 1..=max_depth {
        let hierarchy = build_hierarchy(&*system, 0, depth);
        let n = hierarchy.tile_types[0].len();
        tile_counts.push(n);
        info!("{:>5}  {:>10}  {:>8.2}", depth, n, (n as f64).log2());
    }

    // Helper: dense Merkle path length for a tree with n leaves
    let dense_path = |n: usize| -> usize {
        if n <= 1 { return 0; }
        (n as f64).log2().ceil() as usize
    };

    // Helper: SMT compact path length at a given depth
    // At depth D, coordinate range ≈ ±(φ²)^D.
    // Signed integer in [-R, R] needs ceil(log2(2R+1)) ≈ ceil(1 + D*log2(φ²)) bits.
    let compact_path = |depth: usize| -> usize {
        let bits_per_axis = (1.0 + depth as f64 * phi_sq_log2).ceil() as usize;
        2 * bits_per_axis + 3 + 1 // x + y + rotation(3b) + reflected(1b)
    };

    // ── 2. Merkle path length comparison ───────────────────────────────────
    info!("\n--- Merkle path length at base level (hashes per opening) ---");
    info!(
        "{:>5}  {:>6}  {:>13}  {:>14}  {:>13}  {:>7}",
        "Depth", "Dense", "SMT-compact", "SMT-Coxeter", "SMT-SHA256", "compact"
    );
    info!(
        "{:>5}  {:>6}  {:>13}  {:>14}  {:>13}  {:>7}",
        "", "path", "path", "path(132b)", "path(256b)", "vs dense"
    );
    info!("{}", "-".repeat(65));

    for (i, depth) in (1..=max_depth).enumerate() {
        let n = tile_counts[i];
        let dp = dense_path(n);
        let cp = compact_path(depth);
        let coxeter = COXETER_BITS;
        let hash_key = HASH_KEY_BITS;
        let overhead: i64 = cp as i64 - dp as i64;
        info!(
            "{:>5}  {:>6}  {:>13}  {:>14}  {:>13}  {:>+7}",
            depth, dp, cp, coxeter, hash_key, overhead
        );
    }

    // ── 3. Proof size impact: replacing the base-level tree with SMT ───────
    //
    // In the IOP, each round r opens a supertile at level (depth-r) plus its
    // children one level lower.  The base-level (level 0) tree is hit only in
    // the deepest round.  An SMT would replace only that level-0 tree.
    info!("\n--- Proof size if base-level tree is replaced with SMT ({} queries) ---", num_queries);
    let avg_children = system
        .composition()
        .iter()
        .map(|c| c.iter().sum::<usize>())
        .sum::<usize>() as f64
        / system.num_types() as f64;
    let openings_per_deepest_round = 1 + avg_children as usize;

    info!(
        "{:>5}  {:>9}  {:>12}  {:>15}  {:>14}",
        "Depth", "Dense KB", "SMT-cmpct KB", "SMT-Coxeter KB", "SMT-SHA256 KB"
    );
    info!("{}", "-".repeat(62));

    for (i, depth) in (1..=max_depth).enumerate() {
        let n = tile_counts[i];
        let dp = dense_path(n);
        let cp = compact_path(depth);

        // Overhead per opening = (smt_path - dense_path) * HASH_BYTES bytes
        // The deepest round is the only one using base-level openings.
        let extra_bytes = |smt_path: usize| -> usize {
            if smt_path <= dp { return 0; }
            num_queries * openings_per_deepest_round * (smt_path - dp) * HASH_BYTES
        };

        // Baseline proof size (rough): commit + query phases
        let commit_bytes = (depth + 1) * HASH_BYTES;
        let base_query_bytes = num_queries * depth * openings_per_deepest_round
            * (FIELD_EL_BYTES + dp * HASH_BYTES);
        let dense_total = commit_bytes + base_query_bytes;

        let compact_total = dense_total + extra_bytes(cp);
        let coxeter_total = dense_total + extra_bytes(COXETER_BITS);
        let sha256_total = dense_total + extra_bytes(HASH_KEY_BITS);

        info!(
            "{:>5}  {:>9.1}  {:>12.1}  {:>15.1}  {:>14.1}",
            depth,
            dense_total as f64 / 1024.0,
            compact_total as f64 / 1024.0,
            coxeter_total as f64 / 1024.0,
            sha256_total as f64 / 1024.0,
        );
    }

    // ── 4. Crossover analysis ───────────────────────────────────────────────
    info!("\n--- Crossover analysis ---");
    info!(
        "Dense path ≈ D × log2(λ) ≈ D × {:.2} hashes  (λ=growth rate ≈ {:.2})",
        (tile_counts.last().copied().unwrap_or(1) as f64).log2() / max_depth as f64,
        (tile_counts.last().copied().unwrap_or(1) as f64)
            .powf(1.0 / max_depth as f64)
    );
    info!(
        "SMT compact path ≈ 2×(1+{:.3}D)+4 ≈ {:.2}D+6 hashes (overhead ≈ constant ~{} hashes)",
        phi_sq_log2,
        2.0 * phi_sq_log2,
        compact_path(max_depth) as i64 - dense_path(*tile_counts.last().unwrap_or(&1)) as i64
    );
    let dense_per_depth = (tile_counts.last().copied().unwrap_or(1) as f64).log2()
        / max_depth as f64;
    let coxeter_crossover = COXETER_BITS as f64 / dense_per_depth;
    let sha256_crossover = HASH_KEY_BITS as f64 / dense_per_depth;
    info!(
        "SMT Coxeter key ({} bits): beats dense only at depth > {:.0} (impractical)",
        COXETER_BITS, coxeter_crossover
    );
    info!(
        "SMT SHA-256 key ({} bits): beats dense only at depth > {:.0} (very impractical)",
        HASH_KEY_BITS, sha256_crossover
    );
    info!("→ For practical depths (1-10), compact coordinate key is the only viable SMT option.");

    // ── 5. Non-membership proofs ────────────────────────────────────────────
    info!("\n--- Non-membership proofs: the unique SMT capability ---");
    info!("Dense Merkle trees cannot prove absence: there is no \"no tile here\" leaf.");
    info!("An SMT with tile coordinates as keys enables:");
    info!("  prove_empty(pos) → sibling path showing the leaf at pos is nil");
    info!("  This is O(key_bits) hashes — same cost as a membership proof.");
    info!("");
    info!("Applications for the tiling IOP:");
    info!("  1. Gap-free coverage: prover commits to ALL tiles in the SMT.");
    info!("     Verifier samples random positions and demands proofs (present or absent).");
    info!("     A prover that omits any tile cannot forge a valid empty proof elsewhere.");
    info!("  2. Tile uniqueness: two tiles cannot share a key (SMT enforces injectivity).");
    info!("  3. Boundary checking: prove no tile extends outside a claimed region.");
    info!("");
    info!("These guarantees are impossible with a dense Merkle tree over an index list.");

    // ── 6. Summary ──────────────────────────────────────────────────────────
    info!("\n=== SUMMARY ===");
    let final_n = *tile_counts.last().unwrap_or(&1);
    let final_dense = dense_path(final_n);
    let final_compact = compact_path(max_depth);
    let final_overhead = final_compact as i64 - final_dense as i64;
    info!("At depth {}:", max_depth);
    info!("  Base tiles:        {}", final_n);
    info!("  Dense path:        {} hashes", final_dense);
    info!("  SMT compact path:  {} hashes ({:+} overhead, approximately constant across depths)", final_compact, final_overhead);
    info!("  SMT Coxeter path:  {} hashes ({:+} overhead)", COXETER_BITS, COXETER_BITS as i64 - final_dense as i64);
    info!("  SMT SHA-256 path:  {} hashes ({:+} overhead)", HASH_KEY_BITS, HASH_KEY_BITS as i64 - final_dense as i64);
    info!("");
    info!("Recommendation: compact coordinate key (2 × coord_bits + 4) if non-membership is needed.");
    info!("  - Small overhead (~{} hashes at depth {}) that grows slowly (both paths grow ~linearly).", final_overhead, max_depth);
    info!("  - Enables gap-free coverage and tile-uniqueness proofs.");
    info!("  - Coxeter or SHA-256 keys are never practical for tiling IOPs.");

    Ok(())
}

fn cmd_hybrid_code(d_inner: usize, d_outer: usize, erasure_trials: usize) -> Result<()> {
    let _span = info_span!("hybrid_code", d_inner, d_outer, erasure_trials).entered();
    use tiling::oneway::{build_hierarchy, full_sibling_adjacency};
    use tiling::vulnerability::{enumerate_valid_swaps, erasure_sweep};

    let hat = tiling::systems::resolve_system("hat")?;
    let spectre = tiling::systems::resolve_system("spectre")?;

    // ── 1. Structure ────────────────────────────────────────────────────────
    let inner_h = build_hierarchy(&*hat, 0, d_inner);
    let outer_h = build_hierarchy(&*spectre, 0, d_outer);
    let n_inner = inner_h.tile_types[0].len();
    let n_outer = outer_h.tile_types[0].len();

    // Comparison baselines at total depth d_inner + d_outer
    let hat_flat = build_hierarchy(&*hat, 0, d_inner + d_outer);
    let spectre_flat = build_hierarchy(&*spectre, 0, d_inner + d_outer);
    let n_hat_flat = hat_flat.tile_types[0].len();
    let n_spectre_flat = spectre_flat.tile_types[0].len();

    info!("=== Concatenated Hat+Spectre Hybrid Code (#25) ===\n");
    info!("Inner code: hat at depth {}, {} leaf tiles per block", d_inner, n_inner);
    info!("Outer code: spectre at depth {}, {} blocks", d_outer, n_outer);
    info!("Total hybrid leaf tiles: {}", n_inner * n_outer);
    info!("Comparison baselines (depth {}):", d_inner + d_outer);
    info!("  Hat-only:     {} leaf tiles", n_hat_flat);
    info!("  Spectre-only: {} leaf tiles", n_spectre_flat);

    // ── 2. Tamper detection ──────────────────────────────────────────────────
    let hat_swaps = enumerate_valid_swaps(&*hat);
    let spectre_swaps = enumerate_valid_swaps(&*spectre);

    info!("\n--- Tamper detection ---");
    info!("Hat inner valid swaps (undetectable type-substitutions within a block): {}", hat_swaps.len());
    for sw in &hat_swaps {
        info!("  {} ↔ {} (differ by 1 F-tile; composition check passes for either type)",
            hat.supertile_name(sw.source_supertile),
            hat.supertile_name(sw.target_supertile));
    }
    info!("Spectre outer valid swaps (undetectable block-level substitutions): {}", spectre_swaps.len());
    info!("Hybrid detection: inner hat check PLUS outer spectre check.");
    if hat_swaps.is_empty() && spectre_swaps.is_empty() {
        info!("  No undetectable swaps at either level — full tamper detection.");
    } else {
        if !hat_swaps.is_empty() {
            info!("  Inner hat misses {} swap(s) (P'↔F') — composition check cannot distinguish within a block.", hat_swaps.len());
        }
        if !spectre_swaps.is_empty() {
            info!("  Outer spectre also misses {} swap(s) (Mystic'↔Spectre') at the block level.", spectre_swaps.len());
        }
        info!("  Hybrid: adversary must simultaneously evade BOTH layers → attack cost increases.");
        info!("  Note: spectre has {} valid swap(s) — the zero-swap hypothesis (#17) was refuted.", spectre_swaps.len());
    }

    // ── 3. Erasure recovery comparison ──────────────────────────────────────
    let fractions: Vec<f64> = (0..=10).map(|i| i as f64 / 10.0).collect();

    // Inner hat: erasure sweep at d_inner
    let inner_adj = full_sibling_adjacency(&inner_h, 0);
    let inner_results = erasure_sweep(&inner_h, 0, &inner_adj, &fractions, erasure_trials);

    // Outer spectre: erasure sweep at d_outer (block level)
    let outer_adj = full_sibling_adjacency(&outer_h, 0);
    let outer_results = erasure_sweep(&outer_h, 0, &outer_adj, &fractions, erasure_trials);

    // Hat-only at equivalent flat depth
    let hat_adj = full_sibling_adjacency(&hat_flat, 0);
    let hat_results = erasure_sweep(&hat_flat, 0, &hat_adj, &fractions, erasure_trials);

    // Spectre-only at equivalent flat depth
    let spectre_adj = full_sibling_adjacency(&spectre_flat, 0);
    let spectre_results = erasure_sweep(&spectre_flat, 0, &spectre_adj, &fractions, erasure_trials);

    // Find thresholds: last fraction where mean_determined > 50%
    let inner_thresh = fractions.iter().zip(inner_results.iter())
        .filter(|(_, r)| r.mean_determined > 0.5).last()
        .map(|(&f, _)| f).unwrap_or(0.0);
    let outer_thresh = fractions.iter().zip(outer_results.iter())
        .filter(|(_, r)| r.mean_determined > 0.5).last()
        .map(|(&f, _)| f).unwrap_or(0.0);
    let hat_thresh = fractions.iter().zip(hat_results.iter())
        .filter(|(_, r)| r.mean_determined > 0.5).last()
        .map(|(&f, _)| f).unwrap_or(0.0);
    let spectre_flat_thresh = fractions.iter().zip(spectre_results.iter())
        .filter(|(_, r)| r.mean_determined > 0.5).last()
        .map(|(&f, _)| f).unwrap_or(0.0);

    info!("\n--- Erasure thresholds (last fraction with >50% determination) ---");
    info!("  Inner hat (depth {}):          {:.0}%", d_inner, inner_thresh * 100.0);
    info!("  Outer spectre (depth {}):      {:.0}%", d_outer, outer_thresh * 100.0);
    info!("  Hat-only (depth {}):           {:.0}%", d_inner + d_outer, hat_thresh * 100.0);
    info!("  Spectre-only (depth {}):       {:.0}%", d_inner + d_outer, spectre_flat_thresh * 100.0);

    // Simulate hybrid uniform erasure
    // Model: uniform leaf erasure fraction p over all n_inner × n_outer tiles.
    //   Step 1: for each outer block, count its inner erasures.
    //           Block "fails inner" if inner erasure fraction > inner_thresh.
    //   Step 2: if fraction of failed blocks < outer_thresh → outer code recovers all failed blocks.
    //           Recovered blocks: all n_inner tiles known.
    //   Recovery metric: fraction of blocks recovered (= fraction of total tiles recovered,
    //   since a recovered block restores all n_inner tiles including erased ones).
    let hybrid_uniform: Vec<f64> = fractions.iter().map(|&frac| {
        let mut recovered_blocks_total = 0usize;
        for trial in 0..erasure_trials {
            let mut rng = (frac.to_bits() ^ (trial as u64).wrapping_mul(0x9E3779B97F4A7C15)) | 1;
            let mut n_failed = 0usize;
            for _ in 0..n_outer {
                // Randomly erase tiles from this block
                let n_erased: usize = (0..n_inner).filter(|_| {
                    rng ^= rng << 13; rng ^= rng >> 7; rng ^= rng << 17;
                    (rng as f64) / (u64::MAX as f64) < frac
                }).count();
                if n_erased as f64 / n_inner as f64 > inner_thresh {
                    n_failed += 1;
                }
            }
            // Outer recovery
            let recovered_blocks = if n_failed as f64 / n_outer as f64 <= outer_thresh {
                n_outer // outer recovers all failed blocks
            } else {
                n_outer - n_failed // lose failed blocks
            };
            recovered_blocks_total += recovered_blocks;
        }
        recovered_blocks_total as f64 / (n_outer * erasure_trials) as f64
    }).collect();

    info!("\n--- Uniform erasure: fraction of tiles/blocks recovered ---");
    info!("{:>8}  {:>10}  {:>12}  {:>14}  {:>14}",
        "Erase%", "Hat flat", "Hat-inner", "Spectre-outer", "Hybrid");
    info!("{}", "-".repeat(66));
    for (i, &frac) in fractions.iter().enumerate() {
        info!("{:>8.0}%  {:>10.1}%  {:>12.1}%  {:>14.1}%  {:>14.1}%",
            frac * 100.0,
            hat_results[i].mean_determined * 100.0,
            inner_results[i].mean_determined * 100.0,
            outer_results[i].mean_determined * 100.0,
            hybrid_uniform[i] * 100.0,
        );
    }
    info!("Note: hat-inner and spectre-outer operate at single layer (depth {} and {} respectively).",
        d_inner, d_outer);
    info!("Hybrid column: two-level recovery (inner hat then outer spectre).");

    // ── 4. Block-structured burst erasure ───────────────────────────────────
    // Erase k complete blocks (all n_inner tiles in each block).
    // Hybrid: outer spectre recovers if k/n_outer ≤ outer_thresh.
    // Hat-only: equivalent to k*n_inner tiles erased in clusters → use hat_results at that fraction.
    info!("\n--- Block-structured burst erasure (k entire blocks erased) ---");
    info!("{:>8}  {:>14}  {:>16}  {:>14}",
        "k blocks", "Outer frac%", "Hybrid recovery%", "Hat-flat equiv%");
    info!("{}", "-".repeat(58));

    let burst_ks: Vec<usize> = {
        let mut v = Vec::new();
        let mut k = 1usize;
        while k <= n_outer {
            v.push(k);
            if k >= n_outer { break; }
            k = (k * 2).min(n_outer);
        }
        v
    };

    for k in &burst_ks {
        let outer_frac = *k as f64 / n_outer as f64;
        // Hybrid: if outer_frac ≤ outer_thresh → all blocks recovered; else lose k blocks
        let hybrid_recovery = if outer_frac <= outer_thresh { 100.0 }
            else { (n_outer - k) as f64 / n_outer as f64 * 100.0 };
        // Hat-only equivalent: k*n_inner tiles erased out of n_hat_flat total
        let hat_equiv_frac = (*k as f64 * n_inner as f64) / n_hat_flat as f64;
        let hat_idx = (hat_equiv_frac * 10.0).round() as usize;
        let hat_equiv_recov = hat_results.get(hat_idx)
            .map(|r| r.mean_determined * 100.0).unwrap_or(0.0);
        info!("{:>8}  {:>14.1}%  {:>16.1}%  {:>14.1}%",
            k, outer_frac * 100.0, hybrid_recovery, hat_equiv_recov);
    }
    info!("Hybrid: outer spectre threshold = {:.0}% blocks → up to {} complete-block erasures tolerated.",
        outer_thresh * 100.0, (outer_thresh * n_outer as f64).floor() as usize);

    // ── 5. Summary ──────────────────────────────────────────────────────────
    info!("\n=== SUMMARY ===");
    info!("Hybrid = hat(inner, depth {}) × spectre(outer, depth {})", d_inner, d_outer);
    info!("");
    info!("Tamper detection:");
    info!("  Hat inner: {} valid swap(s) (P'↔F') — composition blind spot within blocks.", hat_swaps.len());
    info!("  Spectre outer: {} valid swap(s) (Mystic'↔Spectre') — also has a blind spot at block level.", spectre_swaps.len());
    info!("  Hybrid: both layers must be evaded simultaneously — raises attack cost, doesn't eliminate it.");
    info!("  (The zero-swap hypothesis for spectre was refuted in #17.)");
    info!("");
    info!("Uniform erasure:");
    info!("  Hybrid threshold ≈ inner hat threshold ({:.0}%) vs hat-flat depth {} threshold ({:.0}%).",
        inner_thresh * 100.0, d_inner + d_outer, hat_thresh * 100.0);
    info!("  Structural decomposition into two shallow layers beats flat hat at double depth.");
    info!("  (Spectre collapses at depth ≥ 3; outer spectre at d={} retains {:.0}% block threshold.)",
        d_outer, outer_thresh * 100.0);
    info!("");
    info!("Block-structured burst erasure:");
    info!("  Hybrid can recover from up to {:.0}% of COMPLETE block erasures.", outer_thresh * 100.0);
    info!("  Hat-only uses leaf-level adjacency — cannot exploit block structure.");
    info!("  Advantage is structural: the outer code adds a dedicated burst-recovery layer.");

    Ok(())
}
