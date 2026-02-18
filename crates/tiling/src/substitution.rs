use crate::metatile::{
    MetatileType, SUPERTILE_F_CHILDREN, SUPERTILE_H_CHILDREN, SUPERTILE_P_CHILDREN,
    SUPERTILE_T_CHILDREN,
};
use crate::systems::TilingSystem;

/// A patch of metatiles at a given hierarchical level.
#[derive(Clone, Debug)]
pub struct Patch {
    pub level: usize,
    pub tiles: Vec<PatchTile>,
}

/// A single tile within a patch, tracking its type and supertile ancestry.
#[derive(Clone, Debug)]
pub struct PatchTile {
    pub tile_type: MetatileType,
    pub child_index: usize,
}

/// Generate type counts at each level for a generic tiling system.
///
/// Starting from a single tile of type `seed`, applies the substitution
/// matrix `levels` times. Returns `levels + 1` count vectors.
pub fn generate_counts_system(
    system: &dyn TilingSystem,
    seed: usize,
    levels: usize,
) -> Vec<Vec<usize>> {
    let num_types = system.num_types();
    let composition = system.composition();
    let mut history = Vec::with_capacity(levels + 1);

    let mut counts = vec![0usize; num_types];
    counts[seed] = 1;
    history.push(counts);

    for _ in 0..levels {
        let prev = history.last().unwrap();
        let mut next = vec![0usize; num_types];

        for i in 0..num_types {
            if prev[i] == 0 {
                continue;
            }
            for j in 0..num_types {
                next[j] += prev[i] * composition[i][j];
            }
        }

        history.push(next);
    }

    history
}

/// Generate type counts at each level for the hat tiling system.
pub fn generate_counts(seed: MetatileType, level: usize) -> Vec<[usize; 4]> {
    let mut history = Vec::with_capacity(level + 1);

    let mut counts = [0usize; 4];
    counts[seed.index()] = 1;
    history.push(counts);

    if level == 0 {
        return history;
    }

    let composition = crate::metatile::supertile_composition();

    for _ in 0..level {
        let prev = *history.last().unwrap();
        let mut next = [0usize; 4];

        for i in 0..4 {
            if prev[i] == 0 {
                continue;
            }
            for j in 0..4 {
                next[j] += prev[i] * composition[i][j];
            }
        }

        history.push(next);
    }

    history
}

/// Total hat count at each level.
pub fn hat_counts(seed: MetatileType, level: usize) -> Vec<usize> {
    let hat_per_type = [4, 1, 2, 2]; // H, T, P, F
    generate_counts(seed, level)
        .iter()
        .map(|counts| {
            counts
                .iter()
                .zip(hat_per_type.iter())
                .map(|(c, h)| c * h)
                .sum()
        })
        .collect()
}

/// Compute which child indices belong to the specified supertile type.
pub fn children_of(supertile: MetatileType) -> &'static [usize] {
    match supertile {
        MetatileType::H => SUPERTILE_H_CHILDREN,
        MetatileType::T => SUPERTILE_T_CHILDREN,
        MetatileType::P => SUPERTILE_P_CHILDREN,
        MetatileType::F => SUPERTILE_F_CHILDREN,
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn level_zero_is_seed() {
        let counts = generate_counts(MetatileType::H, 0);
        assert_eq!(counts.len(), 1);
        assert_eq!(counts[0], [1, 0, 0, 0]);
    }

    #[test]
    fn level_one_from_h() {
        let counts = generate_counts(MetatileType::H, 1);
        assert_eq!(counts.len(), 2);
        assert_eq!(counts[1], [3, 1, 3, 3]);
    }

    #[test]
    fn level_one_from_t() {
        let counts = generate_counts(MetatileType::T, 1);
        assert_eq!(counts[1], [1, 0, 0, 0]);
    }

    #[test]
    fn counts_grow_monotonically() {
        let counts = generate_counts(MetatileType::H, 5);
        for i in 1..counts.len() {
            let total_prev: usize = counts[i - 1].iter().sum();
            let total_curr: usize = counts[i].iter().sum();
            assert!(total_curr > total_prev, "level {} didn't grow", i);
        }
    }

    #[test]
    fn hat_count_level_zero() {
        assert_eq!(hat_counts(MetatileType::H, 0), vec![4]);
        assert_eq!(hat_counts(MetatileType::T, 0), vec![1]);
        assert_eq!(hat_counts(MetatileType::P, 0), vec![2]);
        assert_eq!(hat_counts(MetatileType::F, 0), vec![2]);
    }

    #[test]
    fn hat_count_level_one() {
        let hats = hat_counts(MetatileType::H, 1);
        assert_eq!(hats[1], 25);
    }

    #[test]
    fn generic_matches_hat_specific() {
        use crate::systems::hat::HatSystem;
        let system = HatSystem::new();
        for seed in MetatileType::all() {
            let hat_counts = generate_counts(seed, 5);
            let generic_counts = generate_counts_system(&system, seed.index(), 5);
            for (level, (h, g)) in hat_counts.iter().zip(generic_counts.iter()).enumerate() {
                assert_eq!(
                    &h[..],
                    &g[..],
                    "seed {:?} level {} mismatch",
                    seed,
                    level
                );
            }
        }
    }
}
