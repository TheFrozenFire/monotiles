use crate::metatile::{MetatileType, SUPERTILE_F_CHILDREN, SUPERTILE_H_CHILDREN,
    SUPERTILE_P_CHILDREN, SUPERTILE_T_CHILDREN};

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
    /// Index of this tile in the parent's child list (0-28 for level-1).
    pub child_index: usize,
}

/// Generate a level-n supertile by iterating the substitution from a seed.
///
/// Starting from a single metatile of the given type, apply the substitution
/// n times to produce a hierarchical patch. Returns the metatile type counts
/// at each level.
///
/// The substitution rule: one H metatile inflates into a patch of 29 metatiles,
/// grouped into H'(10) + T'(1) + P'(5) + F'(6) = 22 core + 7 boundary.
pub fn generate_counts(seed: MetatileType, level: usize) -> Vec<[usize; 4]> {
    let mut history = Vec::with_capacity(level + 1);

    // Level 0: the seed
    let mut counts = [0usize; 4];
    counts[seed.index()] = 1;
    history.push(counts);

    if level == 0 {
        return history;
    }

    // The substitution matrix M where M[i][j] = number of type-j metatiles
    // in the supertile of type i.
    let composition = crate::metatile::supertile_composition();

    for _ in 0..level {
        let prev = *history.last().unwrap();
        let mut next = [0usize; 4];

        // Each type-i supertile contributes composition[i][j] metatiles of type j
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
        // H inflates to H'(3H+1T+3P+3F)
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
        // H' = 3H + 1T + 3P + 3F = 3*4 + 1*1 + 3*2 + 3*2 = 25 hats
        assert_eq!(hats[1], 25);
    }
}
