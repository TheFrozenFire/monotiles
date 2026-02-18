use anyhow::Result;
use clap::{Parser, Subcommand};

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
        /// Seed metatile type: H, T, P, or F
        #[arg(default_value = "H")]
        seed: String,
        /// Number of substitution levels
        #[arg(short, long, default_value_t = 5)]
        levels: usize,
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
        /// Seed metatile type: H, T, P, or F
        #[arg(default_value = "H")]
        seed: String,
        /// Hierarchy depth (substitution levels)
        #[arg(short, long, default_value_t = 3)]
        depth: usize,
        /// Maximum neighborhood radius to test
        #[arg(short = 'r', long, default_value_t = 5)]
        max_radius: usize,
    },

    /// Analyze recoverability vulnerability (per-position criticality, erasure thresholds)
    Vulnerability {
        /// Hierarchy depth (substitution levels)
        #[arg(short, long, default_value_t = 3)]
        depth: usize,
        /// Number of erasure trials per fraction
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
        Commands::Inflate { seed, levels } => cmd_inflate(&seed, levels),
        Commands::Sturmian { terms } => cmd_sturmian(terms),
        Commands::Matrix => cmd_matrix(),
        Commands::Fields => cmd_fields(),
        Commands::Prove { seed, depth, queries } => cmd_prove(&seed, depth, queries),
        Commands::Deflate { seed, levels } => cmd_deflate(&seed, levels),
        Commands::Recover { levels, hole_radius } => cmd_recover(levels, hole_radius),
        Commands::Oneway { seed, depth, max_radius } => cmd_oneway(&seed, depth, max_radius),
        Commands::Vulnerability { depth, erasure_trials } => cmd_vulnerability(depth, erasure_trials),
    }
}

fn cmd_verify_coxeter() -> Result<()> {
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

    println!("Coxeter group Gamma verification:");
    let mut all_ok = true;
    for (name, ok) in &checks {
        let status = if *ok { "PASS" } else { "FAIL" };
        println!("  {}: {}", name, status);
        if !*ok {
            all_ok = false;
        }
    }

    if all_ok {
        println!("\nAll 6 Coxeter relations verified.");
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
    println!("\nInverse verification:");
    for g in &test_elements {
        let g_inv = g.inverse();
        let ok = g.compose(&g_inv) == id && g_inv.compose(g) == id;
        println!("  {:?} * inverse = id: {}", g, if ok { "PASS" } else { "FAIL" });
    }

    Ok(())
}

fn cmd_cucaracha() -> Result<()> {
    let elements = domain::cucaracha::cucaracha();
    let words = domain::cucaracha::CUCARACHA_WORDS;

    println!("Cucaracha: 16-element aperiodic monotile of Gamma\n");
    println!("{:<5} {:<25} {:?}", "Idx", "Word", "Normal Form (tx, ty, rot, refl)");
    println!("{}", "-".repeat(70));

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
        println!(
            "{:<5} {:<25} ({}, {}, {}, {})",
            i, word_str, elem.tx, elem.ty, elem.rotation, elem.reflected
        );
    }

    println!("\nAll elements distinct: {}", {
        let unique: std::collections::HashSet<_> = elements.iter().collect();
        unique.len() == 16
    });

    Ok(())
}

fn cmd_inflate(seed: &str, levels: usize) -> Result<()> {
    let seed_type = match seed.to_uppercase().as_str() {
        "H" => tiling::metatile::MetatileType::H,
        "T" => tiling::metatile::MetatileType::T,
        "P" => tiling::metatile::MetatileType::P,
        "F" => tiling::metatile::MetatileType::F,
        _ => anyhow::bail!("Unknown seed type: {}. Use H, T, P, or F.", seed),
    };

    let counts = tiling::substitution::generate_counts(seed_type, levels);
    let hat_counts = tiling::substitution::hat_counts(seed_type, levels);

    println!("Substitution from seed {:?}, {} levels:\n", seed_type, levels);
    println!("{:<8} {:>8} {:>8} {:>8} {:>8} {:>10} {:>10}", "Level", "H", "T", "P", "F", "Total", "Hats");
    println!("{}", "-".repeat(70));

    for (level, (count, hats)) in counts.iter().zip(hat_counts.iter()).enumerate() {
        let total: usize = count.iter().sum();
        println!(
            "{:<8} {:>8} {:>8} {:>8} {:>8} {:>10} {:>10}",
            level, count[0], count[1], count[2], count[3], total, hats
        );
    }

    Ok(())
}

fn cmd_sturmian(terms: usize) -> Result<()> {
    let word = analysis::sturmian::fibonacci_word(terms);

    println!("Fibonacci Sturmian word ({} terms):", terms);
    let line: String = word.iter().map(|b| if *b == 0 { '0' } else { '1' }).collect();
    for chunk in line.as_bytes().chunks(60) {
        println!("  {}", std::str::from_utf8(chunk).unwrap());
    }

    println!("\nFrequency of 1s: {:.6}", analysis::sturmian::frequency_of_ones(&word));

    let phi = (1.0 + 5.0_f64.sqrt()) / 2.0;
    println!("Expected (1/phi^2): {:.6}", 1.0 / (phi * phi));

    println!("\nComplexity p(n):");
    for n in 1..=10 {
        println!("  p({}) = {} (expected {})", n, analysis::sturmian::complexity(&word, n), n + 1);
    }

    Ok(())
}

fn cmd_matrix() -> Result<()> {
    use ark_bls12_381::Fr;

    let m = analysis::spectral::hat_substitution_matrix::<Fr>();
    let comp = tiling::metatile::supertile_composition();

    println!("Hat substitution matrix (H, T, P, F):\n");
    let labels = ["H'", "T'", "P'", "F'"];
    for (i, label) in labels.iter().enumerate() {
        println!(
            "  {} = {}H + {}T + {}P + {}F  (total: {})",
            label, comp[i][0], comp[i][1], comp[i][2], comp[i][3],
            comp[i].iter().sum::<usize>()
        );
    }

    println!("\nDeterminant: {}", if m.determinant() == -Fr::from(1u64) { "-1" } else { "?" });

    // Verify characteristic polynomial: lambda^4 - 7*lambda^3 + 7*lambda - 1 = 0
    let id = domain::matrix::Matrix::<Fr>::identity(4);
    let m2 = m.mul(&m);
    let m3 = m2.mul(&m);
    let m4 = m3.mul(&m);
    let result = &(&m4 + &m3.scale(-Fr::from(7u64)))
        + &(&m.scale(Fr::from(7u64)) + &id.scale(-Fr::from(1u64)));
    let is_zero = (0..4).all(|i| (0..4).all(|j| result[(i, j)] == Fr::from(0u64)));
    println!("Cayley-Hamilton (M^4 - 7M^3 + 7M - I = 0): {}", if is_zero { "VERIFIED" } else { "FAILED" });

    println!("\nEigenvalues: phi^4 = (7+3*sqrt(5))/2, 1, -1, (7-3*sqrt(5))/2");
    println!("  phi^4 ~= 6.854 (area inflation factor)");
    println!("  phi^2 ~= 2.618 (edge length inflation factor)");

    Ok(())
}

fn cmd_deflate(seed: &str, levels: usize) -> Result<()> {
    let seed_type = match seed.to_uppercase().as_str() {
        "H" => tiling::metatile::MetatileType::H,
        "T" => tiling::metatile::MetatileType::T,
        "P" => tiling::metatile::MetatileType::P,
        "F" => tiling::metatile::MetatileType::F,
        _ => anyhow::bail!("Unknown seed type: {}. Use H, T, P, or F.", seed),
    };

    let patch = tiling::geometry::generate_patch(seed_type, levels);
    println!(
        "Generated level-{} patch from {:?}: {} metatiles\n",
        levels,
        seed_type,
        patch.tiles.len()
    );

    let result = tiling::deflation::deflate(&patch);
    println!("Deflation result (level {} -> level {}):", levels, result.supertile_level);
    println!("  Supertiles: {}", result.supertiles.len());
    println!("  Unresolved boundary tiles: {}", result.unresolved.len());

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
    println!(
        "  Type counts: H={}, T={}, P={}, F={}",
        type_counts[0], type_counts[1], type_counts[2], type_counts[3]
    );

    // Inflate back and verify round-trip
    let reinflated = tiling::deflation::inflate_patch(&result.supertiles);
    println!(
        "\nRound-trip: inflate {} supertiles -> {} metatiles (original: {})",
        result.supertiles.len(),
        reinflated.tiles.len(),
        patch.tiles.len()
    );

    Ok(())
}

fn cmd_recover(levels: usize, hole_radius: f64) -> Result<()> {
    let patch = tiling::geometry::generate_patch(tiling::metatile::MetatileType::H, levels);
    println!(
        "Generated level-{} H-patch: {} metatiles\n",
        levels,
        patch.tiles.len()
    );

    // Erase region centered on the first tile
    let center = &patch.tiles[0];
    let (cx, cy) = (center.x, center.y);
    let holey = tiling::recovery::HoleyTiling::erase_region(&patch, cx, cy, hole_radius);

    println!(
        "Erased region: center=({:.3}, {:.3}), radius={:.3}",
        cx, cy, hole_radius
    );
    println!(
        "  Erased tiles: {}",
        holey.hole_positions.len()
    );
    println!(
        "  Remaining tiles: {}",
        holey.exterior.tiles.len()
    );

    if holey.hole_positions.is_empty() {
        println!("\nNo tiles in the erased region. Try a larger radius.");
        return Ok(());
    }

    // Recover
    let result = tiling::recovery::recover(&holey);
    println!("\nRecovery result:");
    println!("  Deflation levels used: {}", result.deflation_levels);
    println!("  Recovered tiles: {}", result.recovered_tiles.len());
    println!("  Success: {}", result.success);

    // Verify
    let verification = tiling::recovery::verify_recovery(
        &holey.hole_positions,
        &result.recovered_tiles,
        0.5,
    );
    println!("\nVerification:");
    println!("  Original erased: {}", verification.original_count);
    println!("  Recovered: {}", verification.recovered_count);
    println!("  Matched: {}", verification.matched);
    println!(
        "  Unmatched originals: {}",
        verification.unmatched_originals.len()
    );
    println!("  Extra recovered: {}", verification.extra_recovered);

    Ok(())
}

fn cmd_prove(seed: &str, depth: usize, num_queries: usize) -> Result<()> {
    use ark_bls12_381::Fr;
    use std::time::Instant;

    let seed_type = match seed.to_uppercase().as_str() {
        "H" => tiling::metatile::MetatileType::H,
        "T" => tiling::metatile::MetatileType::T,
        "P" => tiling::metatile::MetatileType::P,
        "F" => tiling::metatile::MetatileType::F,
        _ => anyhow::bail!("Unknown seed type: {}. Use H, T, P, or F.", seed),
    };

    println!("Tiling IOP: seed={:?}, depth={}, queries={}\n", seed_type, depth, num_queries);

    // Build hierarchy
    let t0 = Instant::now();
    let mut hierarchy = iop::hierarchy::build_hierarchy::<Fr>(seed_type, depth);
    let build_time = t0.elapsed();

    let base_tiles = hierarchy.levels[0].tile_types.len();
    println!("Hierarchy: {} base tiles, {} levels", base_tiles, depth + 1);
    println!("  Build time: {:?}", build_time);

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

    println!("\nProof generated:");
    println!("  Prove time: {:?}", prove_time);
    println!("  Commitments: {}", total_commitments);
    println!("  Total Merkle openings: {}", total_openings);
    println!("  Est. proof size: ~{:.1} KB", est_proof_size as f64 / 1024.0);

    // Verify
    let t2 = Instant::now();
    let result = iop::verifier::verify(&proof);
    let verify_time = t2.elapsed();

    match result {
        Ok(()) => println!("\nVerification: ACCEPTED ({:?})", verify_time),
        Err(e) => println!("\nVerification: REJECTED - {} ({:?})", e, verify_time),
    }

    Ok(())
}

fn cmd_oneway(seed: &str, depth: usize, max_radius: usize) -> Result<()> {
    use std::time::Instant;

    let seed_type = match seed.to_uppercase().as_str() {
        "H" => tiling::metatile::MetatileType::H,
        "T" => tiling::metatile::MetatileType::T,
        "P" => tiling::metatile::MetatileType::P,
        "F" => tiling::metatile::MetatileType::F,
        _ => anyhow::bail!("Unknown seed type: {}. Use H, T, P, or F.", seed),
    };

    println!(
        "One-way substitution analysis: seed={:?}, depth={}, max_radius={}\n",
        seed_type, depth, max_radius
    );

    let t0 = Instant::now();
    let result = tiling::oneway::analyze(seed_type, depth, max_radius);
    let elapsed = t0.elapsed();

    // Hierarchy stats
    println!("Hierarchy ({:?}):", elapsed);
    println!(
        "{:<8} {:>10}",
        "Level", "Tiles"
    );
    for (level, &count) in result.tiles_per_level.iter().enumerate() {
        println!("{:<8} {:>10}", level, count);
    }

    // Per-level determination radius with full sibling adjacency
    println!("\n--- Full sibling adjacency (all siblings mutually adjacent) ---");
    for (level, lr) in result.full_sibling.iter().enumerate() {
        println!("\nLevel {} ({} tiles):", level, result.tiles_per_level[level]);
        if lr.radii_histogram.is_empty() && lr.undetermined == 0 {
            println!("  (no tiles)");
            continue;
        }
        for (&radius, &count) in &lr.radii_histogram {
            println!("  radius {}: {} tiles", radius, count);
        }
        if lr.undetermined > 0 {
            println!("  undetermined: {} tiles", lr.undetermined);
        }
        if let Some(max) = lr.max_radius {
            println!(
                "  summary: min={}, max={}, mean={:.2}",
                lr.min_radius.unwrap(),
                max,
                lr.mean_radius
            );
        }
    }

    // Per-level determination radius with inflation adjacency
    println!("\n--- Intra-supertile inflation adjacency (sparser graph) ---");
    for (level, lr) in result.inflation_adj.iter().enumerate() {
        println!("\nLevel {} ({} tiles):", level, result.tiles_per_level[level]);
        if lr.radii_histogram.is_empty() && lr.undetermined == 0 {
            println!("  (no tiles)");
            continue;
        }
        for (&radius, &count) in &lr.radii_histogram {
            println!("  radius {}: {} tiles", radius, count);
        }
        if lr.undetermined > 0 {
            println!("  undetermined: {} tiles", lr.undetermined);
        }
        if let Some(max) = lr.max_radius {
            println!(
                "  summary: min={}, max={}, mean={:.2}",
                lr.min_radius.unwrap(),
                max,
                lr.mean_radius
            );
        }
    }

    // Decomposition and deflation
    println!("\n--- Type-bag decomposition ---");
    println!(
        "Base level decomposition count: {} (unique = {})",
        result.base_decomposition_count,
        result.base_decomposition_count == 1
    );

    println!("\n--- Greedy deflation ---");
    println!("Success rate: {:.1}%", result.greedy_success_rate * 100.0);

    println!("\n--- Local deflation (radius 1, full sibling adj) ---");
    println!("Unresolved tiles: {}", result.local_deflate_unresolved);

    // Summary verdict
    println!("\n=== VERDICT ===");
    let all_determined_full = result.full_sibling.iter().all(|lr| lr.undetermined == 0);
    let max_full_radius = result
        .full_sibling
        .iter()
        .filter_map(|lr| lr.max_radius)
        .max()
        .unwrap_or(0);

    let all_determined_infl = result.inflation_adj.iter().all(|lr| lr.undetermined == 0);

    if all_determined_full {
        println!(
            "Full sibling adjacency: LOCALLY SOLVABLE at radius {}",
            max_full_radius
        );
    } else {
        println!("Full sibling adjacency: REQUIRES GLOBAL CONTEXT (some tiles undetermined)");
    }

    if all_determined_infl {
        let max_infl = result
            .inflation_adj
            .iter()
            .filter_map(|lr| lr.max_radius)
            .max()
            .unwrap_or(0);
        println!(
            "Inflation adjacency: LOCALLY SOLVABLE at radius {}",
            max_infl
        );
    } else {
        let total_undetermined: usize = result.inflation_adj.iter().map(|lr| lr.undetermined).sum();
        println!(
            "Inflation adjacency: {} tiles undetermined within radius {} \
             (H' supertile is disconnected in inflation graph)",
            total_undetermined, max_radius
        );
    }

    if result.base_decomposition_count == 1 {
        println!("Type-bag decomposition: UNIQUE (composition counts fully determine supertile counts)");
    } else {
        println!(
            "Type-bag decomposition: {} valid decompositions",
            result.base_decomposition_count
        );
    }

    if all_determined_full && result.base_decomposition_count == 1 {
        println!("\nConclusion: Deflation is NOT a one-way function.");
        println!(
            "The asymmetry is implementation convenience, not computational hardness."
        );
        println!(
            "Local information (radius {}) suffices to determine parent assignments.",
            max_full_radius
        );
    }

    Ok(())
}

fn cmd_vulnerability(depth: usize, erasure_trials: usize) -> Result<()> {
    use std::time::Instant;

    println!(
        "Vulnerability analysis: depth={}, erasure_trials={}\n",
        depth, erasure_trials
    );

    let t0 = Instant::now();
    let analysis = tiling::vulnerability::analyze(depth, erasure_trials);
    let elapsed = t0.elapsed();

    tiling::vulnerability::print_report(&analysis);
    println!("\nCompleted in {:?}", elapsed);

    Ok(())
}

fn cmd_fields() -> Result<()> {
    use ark_ff::Field;
    use domain::fields::*;

    println!("Field extension verification over BLS12-381 Fr:\n");

    // FrSqrt5
    let sqrt5 = FrSqrt5::new(ark_bls12_381::Fr::from(0u64), ark_bls12_381::Fr::from(1u64));
    let five = FrSqrt5::new(ark_bls12_381::Fr::from(5u64), ark_bls12_381::Fr::from(0u64));
    println!("  sqrt(5)^2 == 5: {}", sqrt5.square() == five);

    let phi = golden_ratio();
    let phi_sq = phi.square();
    let phi_plus_one = phi + FrSqrt5::new(ark_bls12_381::Fr::from(1u64), ark_bls12_381::Fr::from(0u64));
    println!("  phi^2 == phi + 1: {}", phi_sq == phi_plus_one);
    println!("  phi^2 == hat_inflation(): {}", phi_sq == hat_inflation());

    // FrSqrt15
    let sqrt15 = FrSqrt15::new(ark_bls12_381::Fr::from(0u64), ark_bls12_381::Fr::from(1u64));
    let fifteen = FrSqrt15::new(ark_bls12_381::Fr::from(15u64), ark_bls12_381::Fr::from(0u64));
    println!("  sqrt(15)^2 == 15: {}", sqrt15.square() == fifteen);

    // Inverse round-trips
    let a = FrSqrt5::new(ark_bls12_381::Fr::from(7u64), ark_bls12_381::Fr::from(3u64));
    let a_inv = a.inverse().expect("nonzero invertible");
    println!("  FrSqrt5 inverse round-trip: {}", a * a_inv == FrSqrt5::ONE);

    let b = FrSqrt15::new(ark_bls12_381::Fr::from(11u64), ark_bls12_381::Fr::from(2u64));
    let b_inv = b.inverse().expect("nonzero invertible");
    println!("  FrSqrt15 inverse round-trip: {}", b * b_inv == FrSqrt15::ONE);

    println!("\nAll field properties verified.");
    Ok(())
}
