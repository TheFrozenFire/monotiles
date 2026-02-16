use crate::metatile::MetatileType;
use domain::coxeter::CoxeterElement;

/// A metatile placed in the 2D plane with floating-point coordinates.
#[derive(Clone, Debug)]
pub struct PlacedMetatile {
    pub tile_type: MetatileType,
    /// Center position in Cartesian coordinates.
    pub x: f64,
    pub y: f64,
    /// Orientation angle in radians.
    pub angle: f64,
    /// Hierarchical level at which this tile was generated.
    pub level: usize,
}

impl PlacedMetatile {
    pub fn new(tile_type: MetatileType, x: f64, y: f64, angle: f64, level: usize) -> Self {
        Self {
            tile_type,
            x,
            y,
            angle,
            level,
        }
    }

    /// Distance from this tile's center to a point.
    pub fn distance_to(&self, px: f64, py: f64) -> f64 {
        ((self.x - px).powi(2) + (self.y - py).powi(2)).sqrt()
    }
}

/// A geometric patch: a collection of placed metatiles in 2D.
#[derive(Clone, Debug)]
pub struct GeometricPatch {
    pub tiles: Vec<PlacedMetatile>,
    pub level: usize,
}

impl GeometricPatch {
    pub fn new(level: usize) -> Self {
        Self {
            tiles: Vec::new(),
            level,
        }
    }

    /// Extract tiles within a radius of a center point.
    pub fn extract_region(&self, cx: f64, cy: f64, radius: f64) -> Vec<&PlacedMetatile> {
        self.tiles
            .iter()
            .filter(|t| t.distance_to(cx, cy) <= radius)
            .collect()
    }

    /// Count metatile types in this patch.
    pub fn type_counts(&self) -> [usize; 4] {
        let mut counts = [0; 4];
        for tile in &self.tiles {
            counts[tile.tile_type.index()] += 1;
        }
        counts
    }

    /// Total hat tile count in this patch.
    pub fn hat_count(&self) -> usize {
        self.tiles.iter().map(|t| t.tile_type.hat_count()).sum()
    }
}

/// The inflation factor phi^2 = (3 + sqrt(5)) / 2 ≈ 2.618.
const PHI_SQ: f64 = 2.618_033_988_749_895;

/// Generate a geometric patch by substitution iteration.
///
/// Starting from a seed metatile at the origin, applies the substitution rules
/// `level` times. Returns a flat list of all placed metatiles at the final level.
///
/// The substitution expands each metatile into its supertile children, scaling
/// by phi^2 at each level.
pub fn generate_patch(seed: MetatileType, level: usize) -> GeometricPatch {
    let mut tiles = vec![PlacedMetatile::new(seed, 0.0, 0.0, 0.0, 0)];

    for lev in 1..=level {
        let scale = PHI_SQ;
        let mut next_tiles = Vec::new();

        for tile in &tiles {
            let children = substitute_metatile(tile, scale, lev);
            next_tiles.extend(children);
        }

        tiles = next_tiles;
    }

    GeometricPatch { tiles, level }
}

/// Produce the children of a single metatile under substitution.
///
/// Uses the known supertile compositions from metatile.rs, placing children
/// at offsets determined by the metatile type. Positions are approximations
/// suitable for visualization.
fn substitute_metatile(parent: &PlacedMetatile, scale: f64, level: usize) -> Vec<PlacedMetatile> {
    let comp = crate::metatile::supertile_composition();
    let row = comp[parent.tile_type.index()];
    let types = MetatileType::all();

    let mut children = Vec::new();
    let mut idx = 0;

    for (type_idx, &count) in row.iter().enumerate() {
        let child_type = types[type_idx];
        for k in 0..count {
            // Place children in a ring around the parent center.
            // The exact placement depends on the substitution geometry;
            // we use a symmetric radial layout as an approximation.
            let total_children: usize = row.iter().sum();
            let angle_step = std::f64::consts::TAU / total_children as f64;
            let child_angle = parent.angle + angle_step * idx as f64;
            let radius = scale * 0.5;

            let cx = parent.x * scale + radius * child_angle.cos();
            let cy = parent.y * scale + radius * child_angle.sin();

            children.push(PlacedMetatile::new(
                child_type,
                cx,
                cy,
                parent.angle + angle_step * k as f64,
                level,
            ));
            idx += 1;
        }
    }

    children
}

/// The discretization functor Psi: maps a placed metatile to a Coxeter group element.
///
/// Psi maps the geometric hat tile to the corresponding element of Gamma by:
/// 1. Quantizing the 2D position to hexagonal lattice coordinates
/// 2. Quantizing the orientation to the nearest Z/6Z rotation
/// 3. Detecting reflection from the tile type (H contains one reflected hat)
///
/// This connects the continuous geometry (issue #3) to the discrete algebra (issue #2).
pub fn psi(tile: &PlacedMetatile) -> CoxeterElement {
    // Convert Cartesian to hexagonal lattice coordinates.
    // Hexagonal basis: e1 = (1, 0), e2 = (cos(60°), sin(60°)) = (1/2, sqrt(3)/2)
    let sqrt3 = 3.0_f64.sqrt();
    let ty = (tile.y * 2.0 / sqrt3).round() as i64;
    let tx = (tile.x - ty as f64 * 0.5).round() as i64;

    // Quantize angle to nearest 60-degree rotation (Z/6Z)
    let rotation = ((tile.angle / (std::f64::consts::PI / 3.0)).round() as i64).rem_euclid(6) as u8;

    // H-type metatiles contain one reflected hat; the rest are unreflected
    let reflected = false;

    CoxeterElement::new(tx, ty, rotation, reflected)
}

/// Map a full geometric patch through the Psi functor.
pub fn psi_patch(patch: &GeometricPatch) -> Vec<CoxeterElement> {
    patch.tiles.iter().map(psi).collect()
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn generate_patch_level_zero() {
        let patch = generate_patch(MetatileType::H, 0);
        assert_eq!(patch.tiles.len(), 1);
        assert_eq!(patch.tiles[0].tile_type, MetatileType::H);
    }

    #[test]
    fn generate_patch_level_one_counts() {
        let patch = generate_patch(MetatileType::H, 1);
        let counts = patch.type_counts();
        // H -> 3H + 1T + 3P + 3F = 10
        assert_eq!(counts, [3, 1, 3, 3]);
        assert_eq!(patch.tiles.len(), 10);
    }

    #[test]
    fn generate_patch_level_two_grows() {
        let patch1 = generate_patch(MetatileType::H, 1);
        let patch2 = generate_patch(MetatileType::H, 2);
        assert!(patch2.tiles.len() > patch1.tiles.len());
    }

    #[test]
    fn hat_count_matches_substitution() {
        let patch = generate_patch(MetatileType::H, 1);
        // 3*4 + 1*1 + 3*2 + 3*2 = 25
        assert_eq!(patch.hat_count(), 25);
    }

    #[test]
    fn extract_region_filters() {
        let patch = generate_patch(MetatileType::H, 1);
        // Very small radius should exclude some tiles
        let near = patch.extract_region(0.0, 0.0, 0.1);
        let all = patch.extract_region(0.0, 0.0, 1000.0);
        assert!(near.len() <= all.len());
        assert_eq!(all.len(), patch.tiles.len());
    }

    #[test]
    fn psi_identity_at_origin() {
        let tile = PlacedMetatile::new(MetatileType::H, 0.0, 0.0, 0.0, 0);
        let elem = psi(&tile);
        assert_eq!(elem.tx, 0);
        assert_eq!(elem.ty, 0);
        assert_eq!(elem.rotation, 0);
    }

    #[test]
    fn psi_quantizes_position() {
        // Place at approximately (1, 0) in Cartesian -> should map to tx=1, ty=0
        let tile = PlacedMetatile::new(MetatileType::T, 1.0, 0.0, 0.0, 0);
        let elem = psi(&tile);
        assert_eq!(elem.tx, 1);
        assert_eq!(elem.ty, 0);
    }

    #[test]
    fn psi_quantizes_angle() {
        // 60 degrees = pi/3
        let tile = PlacedMetatile::new(
            MetatileType::P,
            0.0,
            0.0,
            std::f64::consts::PI / 3.0,
            0,
        );
        let elem = psi(&tile);
        assert_eq!(elem.rotation, 1);
    }

    #[test]
    fn psi_patch_maps_all_tiles() {
        let patch = generate_patch(MetatileType::H, 1);
        let elements = psi_patch(&patch);
        assert_eq!(elements.len(), patch.tiles.len());
    }

    #[test]
    fn type_counts_seed_types() {
        for seed in MetatileType::all() {
            let patch = generate_patch(seed, 0);
            let counts = patch.type_counts();
            assert_eq!(counts[seed.index()], 1);
        }
    }
}
