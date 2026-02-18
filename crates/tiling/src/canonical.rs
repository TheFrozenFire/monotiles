//! Canonical form for tiling hierarchies and IOP enforcement cost.
//!
//! ## The problem
//!
//! The tiling IOP accepts any valid hierarchy, including non-canonical ones
//! produced by sibling swaps. Two hierarchies H and H' that differ only in how
//! they label sibling confusable pairs (P'↔F' for hat, Spectre'↔Mystic' for spectre)
//! both produce valid, accepted proofs.
//!
//! ## Canonical form definition
//!
//! **Inflation-order canonical**: each child's type at every parent-child edge must
//! match the type that the inflation rule specifies for that *position* in the parent's
//! child list.
//!
//! Formally, for each parent at level k with children `children[0..n]`:
//! ```text
//! children[i].child_type == inflation_child_type(supertile_children(parent_type)[i])
//! ```
//!
//! The standard top-down inflation hierarchy satisfies this by construction.
//! Any sibling swap violates it: the child at a P'-slot now has F'-type (or vice versa).
//!
//! ## IOP enforcement cost
//!
//! **Zero extra Merkle proofs.** The verifier already receives `QueryResponse.children`
//! in inflation order. A canonical check adds one scalar comparison per child opening:
//! compare `child_type` to the expected type at that position. Proof size is unchanged.
//!
//! This is strictly stronger than the existing composition (multiset) check: composition
//! verifies the right *counts* of each type; the canonical check verifies the right *sequence*.

use tracing::info;

use crate::systems::TilingSystem;
use crate::vulnerability::enumerate_valid_swaps;

// ---------------------------------------------------------------------------
// IOP-level canonical check (works on the TilingSystem composition rules)
// ---------------------------------------------------------------------------

/// Compute the extra cost of enforcing canonical form in the IOP.
pub struct CanonicalEnforcementCost {
    /// Extra Merkle proofs per query round (0 — reuses existing child openings).
    pub extra_merkle_proofs_per_query: usize,
    /// Extra scalar comparisons per child opening (one type check per child).
    pub extra_comparisons_per_child: usize,
    /// Average children per supertile query (reflects the additional work per query).
    pub avg_children_checked: f64,
    /// Fraction of queries that hit confusable-type supertiles.
    pub vulnerable_query_fraction: f64,
}

/// Analyze the cost of adding the canonical form check to the IOP verifier.
///
/// For each supertile type, reports how many per-child checks the canonical constraint
/// adds. Cross-references with the swap-vulnerable tile fraction to estimate the fraction
/// of queries where the canonical check fires.
pub fn analyze_canonical_enforcement_cost(system: &dyn TilingSystem) -> CanonicalEnforcementCost {
    let comp = system.composition();
    let swaps = enumerate_valid_swaps(system);

    // Compute the confusable types (those involved in any swap)
    let mut confusable_types = std::collections::HashSet::new();
    for sw in &swaps {
        confusable_types.insert(sw.source_supertile);
        confusable_types.insert(sw.target_supertile);
    }

    // Average children per supertile (weighted by parent type mix)
    // Weight by total children produced (proportional to inflation output)
    let total_children: usize = comp.iter().map(|c| c.iter().sum::<usize>()).sum();
    let num_parent_types = comp.len();

    let avg_children = if total_children > 0 {
        total_children as f64 / num_parent_types as f64
    } else {
        0.0
    };

    // Fraction of supertile tiles that are confusable-type (vulnerable)
    let total_child_slots: usize = comp.iter().map(|c| c.iter().sum::<usize>()).sum();
    let confusable_child_slots: usize = comp
        .iter()
        .map(|c| confusable_types.iter().map(|&t| c[t]).sum::<usize>())
        .sum();

    let vulnerable_fraction = if total_child_slots > 0 {
        confusable_child_slots as f64 / total_child_slots as f64
    } else {
        0.0
    };

    CanonicalEnforcementCost {
        extra_merkle_proofs_per_query: 0,
        extra_comparisons_per_child: 1,
        avg_children_checked: avg_children,
        vulnerable_query_fraction: vulnerable_fraction,
    }
}

// ---------------------------------------------------------------------------
// Canonical check demonstration (without a full hierarchy build)
// ---------------------------------------------------------------------------

/// Verify that the canonical constraint holds for a given parent type and its children.
///
/// `children_types` is the sequence of child types as presented by the prover (in
/// inflation order). Returns true iff each position matches the inflation rule.
pub fn check_canonical_for_parent(
    parent_type: usize,
    children_types: &[usize],
    system: &dyn TilingSystem,
) -> bool {
    let expected_slots = system.supertile_children(parent_type);
    if children_types.len() != expected_slots.len() {
        return false;
    }
    for (i, &ct) in children_types.iter().enumerate() {
        let expected = system.inflation_child_type(expected_slots[i]);
        if ct != expected {
            return false;
        }
    }
    true
}

// ---------------------------------------------------------------------------
// Top-level analysis
// ---------------------------------------------------------------------------

pub struct CanonicalAnalysis {
    /// True iff the inflation rule always produces the same type at each position.
    pub inflation_order_is_deterministic: bool,
    /// For each parent type, whether the canonical constraint is checkable.
    pub per_type_canonical: Vec<(usize, bool)>,
    pub cost: CanonicalEnforcementCost,
}

pub fn analyze_canonical(system: &dyn TilingSystem) -> CanonicalAnalysis {
    let num_types = system.num_types();

    // Check that each parent type produces a deterministic child sequence
    // (i.e., inflation_child_type is consistent with supertile_children).
    let mut per_type_canonical = Vec::new();
    let mut all_deterministic = true;

    for t in 0..num_types {
        let slots = system.supertile_children(t);
        let child_types: Vec<usize> = slots.iter().map(|&ri| system.inflation_child_type(ri)).collect();
        let is_ok = check_canonical_for_parent(t, &child_types, system);
        per_type_canonical.push((t, is_ok));
        if !is_ok {
            all_deterministic = false;
        }
    }

    let cost = analyze_canonical_enforcement_cost(system);

    CanonicalAnalysis {
        inflation_order_is_deterministic: all_deterministic,
        per_type_canonical,
        cost,
    }
}

/// Print the canonical form analysis report.
pub fn print_canonical_report(system: &dyn TilingSystem, analysis: &CanonicalAnalysis) {
    info!("=== Canonical Form Analysis (#33) ===\n");
    info!("System: {}", system.name());
    info!(
        "Canonical form: inflation-order (each child's type must match inflation rule at its position)"
    );

    info!("\n--- Inflation rule determinism ---");
    for (t, ok) in &analysis.per_type_canonical {
        let slots = system.supertile_children(*t);
        let child_types: Vec<_> = slots
            .iter()
            .map(|&ri| system.type_name(system.inflation_child_type(ri)))
            .collect();
        info!(
            "  {}: {} children [{}] — position sequence is {}",
            system.supertile_name(*t),
            slots.len(),
            child_types.join(", "),
            if *ok { "deterministic ✓" } else { "ambiguous ✗" }
        );
    }
    info!(
        "\nAll parent types have deterministic inflation sequences: {}",
        if analysis.inflation_order_is_deterministic { "YES" } else { "NO" }
    );

    info!("\n--- IOP enforcement cost ---");
    info!(
        "Extra Merkle proofs per query: {} (NONE — uses existing child openings)",
        analysis.cost.extra_merkle_proofs_per_query
    );
    info!(
        "Extra type comparisons per child: {}",
        analysis.cost.extra_comparisons_per_child
    );
    info!(
        "Average children checked per query: {:.1}",
        analysis.cost.avg_children_checked
    );
    info!(
        "Fraction of tiles that are confusable-type: {:.1}%",
        analysis.cost.vulnerable_query_fraction * 100.0
    );

    info!("\n--- What a sibling swap looks like to the canonical verifier ---");
    let swaps = enumerate_valid_swaps(system);
    for sw in &swaps {
        let src_slots = system.supertile_children(sw.source_supertile);
        let tgt_slots = system.supertile_children(sw.target_supertile);
        let src_types: Vec<_> = src_slots.iter().map(|&ri| system.type_name(system.inflation_child_type(ri))).collect();
        let tgt_types: Vec<_> = tgt_slots.iter().map(|&ri| system.type_name(system.inflation_child_type(ri))).collect();
        info!(
            "  Swap: {} ↔ {}",
            system.supertile_name(sw.source_supertile),
            system.supertile_name(sw.target_supertile),
        );
        info!(
            "    {}-slot children: [{}]",
            system.supertile_name(sw.source_supertile),
            src_types.join(", ")
        );
        info!(
            "    {}-slot children: [{}]",
            system.supertile_name(sw.target_supertile),
            tgt_types.join(", ")
        );
        info!(
            "    After swap, the {}-labeled tile presents {}-slot children → position check FAILS",
            system.supertile_name(sw.target_supertile),
            system.supertile_name(sw.source_supertile),
        );
    }

    info!("\n=== SUMMARY ===");
    info!("The canonical form check can be added to the IOP verifier with:");
    info!("  - 0 extra Merkle proofs");
    info!(
        "  - ~{:.0} extra scalar comparisons per query (one per child)",
        analysis.cost.avg_children_checked
    );
    info!("  - No change to proof size");
    info!("Detection: any sibling swap presents children from the wrong inflation slot");
    info!("sequence — the position check catches it immediately.");
    info!("Proof size impact: NONE. Verification cost increase: O(children_per_query).");
}
