use crate::geometry::{GeometricPatch, PlacedMetatile};
use crate::metatile::MetatileType;

/// The inflation factor phi^2 = (3 + sqrt(5)) / 2.
const PHI_SQ: f64 = 2.618_033_988_749_895;

/// A tile in a deflation-aware tiling: carries its supertile assignment.
#[derive(Clone, Debug)]
pub struct DeflationTile {
    pub tile: PlacedMetatile,
    /// Which supertile this tile belongs to (if assigned during deflation).
    pub supertile_id: Option<usize>,
}

/// Result of a deflation operation.
#[derive(Clone, Debug)]
pub struct DeflationResult {
    /// The supertile-level tiles after composition.
    pub supertiles: Vec<PlacedMetatile>,
    /// Tiles near the boundary that couldn't be composed into supertiles.
    pub unresolved: Vec<PlacedMetatile>,
    /// The level of the supertiles (input level + 1).
    pub supertile_level: usize,
}

/// Deflate a geometric patch: group nearby metatiles into supertiles.
///
/// Uses spatial clustering: metatiles within a supertile occupy a region
/// of diameter ~phi^2 at each level. We cluster by dividing the plane into
/// cells of this size and grouping tiles that fall into the same cell.
///
/// Tiles that can't be cleanly assigned (near cell boundaries) are returned
/// as unresolved.
pub fn deflate(patch: &GeometricPatch) -> DeflationResult {
    if patch.tiles.is_empty() {
        return DeflationResult {
            supertiles: Vec::new(),
            unresolved: Vec::new(),
            supertile_level: patch.level + 1,
        };
    }

    let cell_size = PHI_SQ.powi(patch.level as i32 + 1);
    let boundary_margin = cell_size * 0.15;

    let mut clusters: std::collections::HashMap<(i64, i64), Vec<&PlacedMetatile>> =
        std::collections::HashMap::new();
    let mut unresolved = Vec::new();

    for tile in &patch.tiles {
        let cell_x = (tile.x / cell_size).floor() as i64;
        let cell_y = (tile.y / cell_size).floor() as i64;

        // Check if tile is near a cell boundary
        let frac_x = (tile.x / cell_size) - cell_x as f64;
        let frac_y = (tile.y / cell_size) - cell_y as f64;
        let margin = boundary_margin / cell_size;

        if frac_x < margin || frac_x > (1.0 - margin) || frac_y < margin || frac_y > (1.0 - margin)
        {
            unresolved.push(tile.clone());
        } else {
            clusters.entry((cell_x, cell_y)).or_default().push(tile);
        }
    }

    // Convert clusters to supertiles
    let supertiles: Vec<PlacedMetatile> = clusters
        .into_iter()
        .map(|((_cx, _cy), tiles)| {
            let avg_x = tiles.iter().map(|t| t.x).sum::<f64>() / tiles.len() as f64;
            let avg_y = tiles.iter().map(|t| t.y).sum::<f64>() / tiles.len() as f64;
            let avg_angle = tiles.iter().map(|t| t.angle).sum::<f64>() / tiles.len() as f64;

            // Determine supertile type from child composition
            let st_type = infer_supertile_type(&tiles);

            PlacedMetatile::new(st_type, avg_x, avg_y, avg_angle, patch.level + 1)
        })
        .collect();

    DeflationResult {
        supertiles,
        unresolved,
        supertile_level: patch.level + 1,
    }
}

/// Infer the supertile type from its children's type composition.
fn infer_supertile_type(children: &[&PlacedMetatile]) -> MetatileType {
    let mut counts = [0usize; 4];
    for child in children {
        counts[child.tile_type.index()] += 1;
    }

    let comp = crate::metatile::supertile_composition();

    // Find the best matching supertile type
    let mut best = MetatileType::H;
    let mut best_dist = usize::MAX;

    for (i, row) in comp.iter().enumerate() {
        let dist: usize = counts
            .iter()
            .zip(row.iter())
            .map(|(a, b)| (*a as isize - *b as isize).unsigned_abs())
            .sum();
        if dist < best_dist {
            best_dist = dist;
            best = MetatileType::all()[i];
        }
    }

    best
}

/// Inflate a single supertile back to its constituent metatiles.
///
/// Given a supertile at some position, produce the metatiles it contains
/// by applying the substitution rules at the appropriate scale.
pub fn inflate(supertile: &PlacedMetatile) -> Vec<PlacedMetatile> {
    let comp = crate::metatile::supertile_composition();
    let row = comp[supertile.tile_type.index()];
    let types = MetatileType::all();

    let scale = 1.0 / PHI_SQ;
    let mut children = Vec::new();
    let mut idx = 0;

    for (type_idx, &count) in row.iter().enumerate() {
        let child_type = types[type_idx];
        let total: usize = row.iter().sum();

        for k in 0..count {
            let angle_step = std::f64::consts::TAU / total as f64;
            let child_angle = supertile.angle + angle_step * idx as f64;
            let radius = scale * 0.5;

            let cx = supertile.x + radius * child_angle.cos();
            let cy = supertile.y + radius * child_angle.sin();

            children.push(PlacedMetatile::new(
                child_type,
                cx,
                cy,
                supertile.angle + angle_step * k as f64,
                supertile.level - 1,
            ));
            idx += 1;
        }
    }

    children
}

/// Inflate an entire patch of supertiles to metatiles.
pub fn inflate_patch(supertiles: &[PlacedMetatile]) -> GeometricPatch {
    let level = supertiles
        .first()
        .map(|t| t.level.saturating_sub(1))
        .unwrap_or(0);

    let tiles: Vec<PlacedMetatile> = supertiles.iter().flat_map(|st| inflate(st)).collect();

    GeometricPatch { tiles, level }
}

/// Verify the deflation-inflation round-trip property.
///
/// For a clean (no holes) patch, deflate then inflate should recover
/// at least as many tiles as the original (possibly more due to
/// supertile boundary effects). The type composition should be preserved.
pub fn verify_roundtrip(patch: &GeometricPatch) -> RoundtripResult {
    let original_counts = patch.type_counts();
    let original_total = patch.tiles.len();

    let deflation = deflate(patch);
    let reinflated = inflate_patch(&deflation.supertiles);

    // Tiles from inflation + unresolved should approximate original
    let recovered_total = reinflated.tiles.len() + deflation.unresolved.len();

    RoundtripResult {
        original_total,
        original_counts,
        supertile_count: deflation.supertiles.len(),
        unresolved_count: deflation.unresolved.len(),
        reinflated_total: reinflated.tiles.len(),
        recovered_total,
    }
}

/// Results of a deflation-inflation round-trip test.
#[derive(Clone, Debug)]
pub struct RoundtripResult {
    pub original_total: usize,
    pub original_counts: [usize; 4],
    pub supertile_count: usize,
    pub unresolved_count: usize,
    pub reinflated_total: usize,
    pub recovered_total: usize,
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::geometry::generate_patch;

    #[test]
    fn deflate_empty_patch() {
        let patch = GeometricPatch {
            tiles: Vec::new(),
            level: 0,
        };
        let result = deflate(&patch);
        assert!(result.supertiles.is_empty());
        assert!(result.unresolved.is_empty());
    }

    #[test]
    fn deflate_level_one_patch() {
        let patch = generate_patch(MetatileType::H, 1);
        assert_eq!(patch.tiles.len(), 10);

        let result = deflate(&patch);
        // After deflation, we should have some supertiles and possibly some unresolved
        let total = result.supertiles.len() + result.unresolved.len();
        assert!(total > 0, "deflation should produce some output");
    }

    #[test]
    fn inflate_produces_correct_counts() {
        let supertile = PlacedMetatile::new(MetatileType::H, 0.0, 0.0, 0.0, 1);
        let children = inflate(&supertile);
        assert_eq!(children.len(), 10); // H' = 3H + 1T + 3P + 3F = 10
    }

    #[test]
    fn inflate_type_composition() {
        for seed in MetatileType::all() {
            let supertile = PlacedMetatile::new(seed, 0.0, 0.0, 0.0, 1);
            let children = inflate(&supertile);

            let mut counts = [0usize; 4];
            for child in &children {
                counts[child.tile_type.index()] += 1;
            }

            let expected = crate::metatile::supertile_composition()[seed.index()];
            assert_eq!(
                counts, expected,
                "inflate({:?}) type counts should match substitution matrix",
                seed
            );
        }
    }

    #[test]
    fn roundtrip_level_two() {
        let patch = generate_patch(MetatileType::H, 2);
        let result = verify_roundtrip(&patch);

        // The recovered total should be in the same order of magnitude
        assert!(
            result.supertile_count > 0,
            "should produce some supertiles"
        );
    }

    #[test]
    fn inflate_patch_preserves_level() {
        let supertiles = vec![
            PlacedMetatile::new(MetatileType::H, 0.0, 0.0, 0.0, 2),
            PlacedMetatile::new(MetatileType::P, 5.0, 0.0, 0.0, 2),
        ];
        let result = inflate_patch(&supertiles);
        assert_eq!(result.level, 1);
        assert_eq!(result.tiles.len(), 10 + 5); // H'(10) + P'(5)
    }

    #[test]
    fn infer_supertile_type_exact() {
        // Create a mock set of children matching each supertile composition
        let comp = crate::metatile::supertile_composition();

        for (si, row) in comp.iter().enumerate() {
            let expected_type = MetatileType::all()[si];
            let mut children = Vec::new();
            for (ti, &count) in row.iter().enumerate() {
                for _ in 0..count {
                    children.push(PlacedMetatile::new(
                        MetatileType::all()[ti],
                        0.0,
                        0.0,
                        0.0,
                        0,
                    ));
                }
            }
            let refs: Vec<&PlacedMetatile> = children.iter().collect();
            assert_eq!(
                infer_supertile_type(&refs),
                expected_type,
                "should infer {:?} supertile",
                expected_type
            );
        }
    }
}
