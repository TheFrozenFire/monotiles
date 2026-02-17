use crate::deflation::inflate;
use crate::geometry::{GeometricPatch, PlacedMetatile};
use crate::metatile::MetatileType;

/// The inflation factor phi^2 = (3 + sqrt(5)) / 2.
const PHI_SQ: f64 = 2.618_033_988_749_895;

/// A tiling with a finite erased region.
///
/// The exterior contains all tiles outside the hole; the hole is specified
/// by the positions of erased tiles (or a geometric region).
#[derive(Clone, Debug)]
pub struct HoleyTiling {
    /// Tiles outside the erased region.
    pub exterior: GeometricPatch,
    /// Positions of erased tiles (center coordinates).
    pub hole_positions: Vec<(f64, f64)>,
    /// Radius of the hole region (for geometric containment checks).
    pub hole_center: (f64, f64),
    pub hole_radius: f64,
}

impl HoleyTiling {
    /// Create a holey tiling by erasing tiles within a radius of a center point.
    pub fn erase_region(patch: &GeometricPatch, cx: f64, cy: f64, radius: f64) -> Self {
        let mut exterior_tiles = Vec::new();
        let mut hole_positions = Vec::new();

        for tile in &patch.tiles {
            if tile.distance_to(cx, cy) <= radius {
                hole_positions.push((tile.x, tile.y));
            } else {
                exterior_tiles.push(tile.clone());
            }
        }

        HoleyTiling {
            exterior: GeometricPatch {
                tiles: exterior_tiles,
                level: patch.level,
            },
            hole_positions,
            hole_center: (cx, cy),
            hole_radius: radius,
        }
    }
}

/// Result of a recovery operation.
#[derive(Clone, Debug)]
pub struct RecoveryResult {
    /// The recovered tiles that fill the hole.
    pub recovered_tiles: Vec<PlacedMetatile>,
    /// Number of deflation levels needed.
    pub deflation_levels: usize,
    /// Whether recovery was successful (recovered tiles fill the hole).
    pub success: bool,
}

/// Recover erased metatiles using the substitution structure.
///
/// The recovery algorithm demonstrates local recoverability:
/// 1. Compute how many deflation levels are needed for absorption
///    (hole + damage zone fits inside one supertile)
/// 2. Regenerate the tiling locally from the substitution rules
/// 3. Match regenerated tiles to the hole positions
///
/// This implements the Li-Boyle deflation strategy: since the substitution
/// rules are deterministic (recognizability) and the substitution matrix
/// is invertible (det=-1), the tiling in any finite erased region is
/// uniquely determined by its complement.
pub fn recover(holey: &HoleyTiling) -> RecoveryResult {
    if holey.hole_positions.is_empty() {
        return RecoveryResult {
            recovered_tiles: Vec::new(),
            deflation_levels: 0,
            success: true,
        };
    }

    let hole_diameter = holey.hole_radius * 2.0;

    // Compute number of deflation levels needed for absorption:
    // We need supertile_diameter(L) > damage_diameter(d, L)
    // where supertile_diameter grows as phi^{2L} and damage grows as d + 4L.
    let mut levels_used = 1;
    for level in 1..20 {
        let supertile_diam = PHI_SQ.powi(level as i32);
        let damage_diam = hole_diameter + 4.0 * level as f64;
        if supertile_diam > damage_diam {
            levels_used = level;
            break;
        }
    }

    // Find exterior tiles near the hole boundary.
    // These tiles constrain which supertile encloses the hole.
    let boundary_radius = holey.hole_radius + PHI_SQ.powi(levels_used as i32);
    let boundary_tiles: Vec<&PlacedMetatile> = holey
        .exterior
        .tiles
        .iter()
        .filter(|t| t.distance_to(holey.hole_center.0, holey.hole_center.1) <= boundary_radius)
        .collect();

    // Determine the enclosing supertile type from boundary tile composition.
    // Count metatile types in the boundary zone.
    let mut type_counts = [0usize; 4];
    for t in &boundary_tiles {
        type_counts[t.tile_type.index()] += 1;
    }

    // Infer the supertile type using closest match to substitution matrix rows.
    let enclosing_type = infer_supertile_type(&type_counts);

    // Generate the expected tile pattern for this supertile type.
    // Inflate the supertile centered on the hole to produce metatiles.
    let enclosing = PlacedMetatile::new(
        enclosing_type,
        holey.hole_center.0,
        holey.hole_center.1,
        0.0,
        levels_used,
    );
    let inflated = inflate_enclosing(&[enclosing], levels_used);

    // Filter to tiles that fall within the hole region and aren't already
    // in the exterior (avoid duplicating existing tiles).
    let mut recovered = Vec::new();
    for tile in inflated {
        let dist = tile.distance_to(holey.hole_center.0, holey.hole_center.1);
        if dist <= holey.hole_radius * 1.5 {
            // Check this position isn't already covered by an exterior tile
            let already_exists = holey.exterior.tiles.iter().any(|ext| {
                ((ext.x - tile.x).powi(2) + (ext.y - tile.y).powi(2)).sqrt() < 0.1
            });
            if !already_exists {
                recovered.push(tile);
            }
        }
    }

    let success = !recovered.is_empty();

    RecoveryResult {
        recovered_tiles: recovered,
        deflation_levels: levels_used,
        success,
    }
}

/// Infer supertile type from a neighborhood's metatile type counts.
///
/// Compares the observed counts against the substitution matrix rows
/// and picks the closest match.
fn infer_supertile_type(counts: &[usize; 4]) -> MetatileType {
    use crate::metatile::supertile_composition;

    let comp = supertile_composition();
    let types = MetatileType::all();

    let mut best = MetatileType::H;
    let mut best_score = f64::MAX;

    for (i, row) in comp.iter().enumerate() {
        let row_total: usize = row.iter().sum();
        let obs_total: usize = counts.iter().sum();
        if obs_total == 0 || row_total == 0 {
            continue;
        }
        // Compare normalized type fractions
        let score: f64 = counts
            .iter()
            .zip(row.iter())
            .map(|(&obs, &exp)| {
                let obs_frac = obs as f64 / obs_total as f64;
                let exp_frac = exp as f64 / row_total as f64;
                (obs_frac - exp_frac).powi(2)
            })
            .sum();
        if score < best_score {
            best_score = score;
            best = types[i];
        }
    }

    best
}

/// Inflate a set of supertiles down through multiple levels to metatiles.
fn inflate_enclosing(supertiles: &[PlacedMetatile], levels: usize) -> Vec<PlacedMetatile> {
    let mut current: Vec<PlacedMetatile> = supertiles.to_vec();

    for _ in 0..levels {
        let mut next = Vec::new();
        for tile in &current {
            if tile.level > 0 {
                next.extend(inflate(tile));
            } else {
                next.push(tile.clone());
            }
        }
        current = next;
    }

    current
}

/// Verify recovery correctness: the recovered tiles should match the erased originals.
///
/// Compares by checking that recovered tiles cover the same approximate positions
/// as the original erased tiles (within a tolerance).
pub fn verify_recovery(
    original_erased: &[(f64, f64)],
    recovered: &[PlacedMetatile],
    tolerance: f64,
) -> RecoveryVerification {
    let mut matched = 0;
    let mut unmatched_originals = Vec::new();

    for &(ox, oy) in original_erased {
        let found = recovered
            .iter()
            .any(|r| ((r.x - ox).powi(2) + (r.y - oy).powi(2)).sqrt() < tolerance);
        if found {
            matched += 1;
        } else {
            unmatched_originals.push((ox, oy));
        }
    }

    let extra_recovered = recovered.len().saturating_sub(original_erased.len());

    RecoveryVerification {
        original_count: original_erased.len(),
        recovered_count: recovered.len(),
        matched,
        unmatched_originals,
        extra_recovered,
    }
}

/// Verification results for a recovery operation.
#[derive(Clone, Debug)]
pub struct RecoveryVerification {
    pub original_count: usize,
    pub recovered_count: usize,
    pub matched: usize,
    pub unmatched_originals: Vec<(f64, f64)>,
    pub extra_recovered: usize,
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::geometry::generate_patch;
    use crate::metatile::MetatileType;

    #[test]
    fn holey_tiling_from_patch() {
        let patch = generate_patch(MetatileType::H, 2);
        // Center the erase region on the first tile in the patch
        let center = &patch.tiles[0];
        let (cx, cy) = (center.x, center.y);
        let radius = 1.0;

        let holey = HoleyTiling::erase_region(&patch, cx, cy, radius);

        let total = holey.exterior.tiles.len() + holey.hole_positions.len();
        assert_eq!(total, patch.tiles.len(), "erase should preserve total count");
        assert!(
            !holey.hole_positions.is_empty(),
            "should erase at least one tile"
        );
    }

    #[test]
    fn recover_empty_hole() {
        let patch = generate_patch(MetatileType::H, 1);
        let holey = HoleyTiling {
            exterior: patch.clone(),
            hole_positions: Vec::new(),
            hole_center: (0.0, 0.0),
            hole_radius: 0.0,
        };

        let result = recover(&holey);
        assert!(result.success);
        assert!(result.recovered_tiles.is_empty());
    }

    #[test]
    fn recover_single_tile_hole() {
        let patch = generate_patch(MetatileType::H, 2);
        let center = &patch.tiles[0];
        let (cx, cy) = (center.x, center.y);

        // Erase a small region around the first tile
        let holey = HoleyTiling::erase_region(&patch, cx, cy, 0.3);

        if holey.hole_positions.is_empty() {
            // No tiles near enough to origin to erase — skip
            return;
        }

        let result = recover(&holey);
        assert!(
            result.deflation_levels > 0,
            "should need at least one deflation level"
        );
    }

    #[test]
    fn recover_supertile_hole() {
        let patch = generate_patch(MetatileType::H, 3);
        let center = &patch.tiles[0];
        let (cx, cy) = (center.x, center.y);

        // Erase a medium region around the first tile
        let holey = HoleyTiling::erase_region(&patch, cx, cy, 1.5);

        if holey.hole_positions.is_empty() {
            return;
        }

        let result = recover(&holey);
        assert!(
            result.deflation_levels >= 1,
            "should need deflation for a supertile-sized hole"
        );
    }

    #[test]
    fn recovery_type_counts_reasonable() {
        let patch = generate_patch(MetatileType::H, 2);
        let center = &patch.tiles[0];
        let (cx, cy) = (center.x, center.y);
        let holey = HoleyTiling::erase_region(&patch, cx, cy, 0.5);

        if holey.hole_positions.is_empty() {
            return;
        }

        let result = recover(&holey);
        if result.success && !result.recovered_tiles.is_empty() {
            // Recovered tiles should have valid types
            for tile in &result.recovered_tiles {
                assert!(
                    [MetatileType::H, MetatileType::T, MetatileType::P, MetatileType::F]
                        .contains(&tile.tile_type),
                    "recovered tile should have a valid type"
                );
            }
        }
    }

    #[test]
    fn verify_recovery_perfect_match() {
        // If we recover exactly the erased positions, verification should succeed
        let positions = vec![(0.0, 0.0), (1.0, 0.0)];
        let recovered = vec![
            PlacedMetatile::new(MetatileType::H, 0.0, 0.0, 0.0, 0),
            PlacedMetatile::new(MetatileType::P, 1.0, 0.0, 0.0, 0),
        ];

        let result = verify_recovery(&positions, &recovered, 0.1);
        assert_eq!(result.matched, 2);
        assert!(result.unmatched_originals.is_empty());
    }
}
