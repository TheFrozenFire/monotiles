/// The four metatile types in the hat tiling system.
///
/// Each metatile represents a cluster of hat tiles:
/// - H: hexagon, 4 hats (1 reflected + 3 unreflected)
/// - T: equilateral triangle, 1 unreflected hat
/// - P: parallelogram, 2 unreflected hats
/// - F: pentagonal triskelion leg, 2 unreflected hats
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum MetatileType {
    H,
    T,
    P,
    F,
}

impl MetatileType {
    /// Number of hat tiles contained in this metatile.
    pub fn hat_count(self) -> usize {
        match self {
            MetatileType::H => 4,
            MetatileType::T => 1,
            MetatileType::P => 2,
            MetatileType::F => 2,
        }
    }

    /// All four metatile types in canonical order.
    pub fn all() -> [MetatileType; 4] {
        [MetatileType::H, MetatileType::T, MetatileType::P, MetatileType::F]
    }

    /// Index of this type in the canonical ordering.
    pub fn index(self) -> usize {
        match self {
            MetatileType::H => 0,
            MetatileType::T => 1,
            MetatileType::P => 2,
            MetatileType::F => 3,
        }
    }
}

/// Edge labels used in metatile matching rules.
///
/// Edges are signed: matching requires opposite signs to be adjacent.
/// The L edge is undirected (symmetric).
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum EdgeLabel {
    A,
    B,
    X,
    F,
    L,
}

/// Edge direction/sign for matching rules.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum EdgeSign {
    Plus,
    Minus,
}

impl EdgeSign {
    pub fn flip(self) -> Self {
        match self {
            EdgeSign::Plus => EdgeSign::Minus,
            EdgeSign::Minus => EdgeSign::Plus,
        }
    }
}

/// A signed edge for matching rules.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub struct SignedEdge {
    pub label: EdgeLabel,
    pub sign: EdgeSign,
}

impl SignedEdge {
    pub fn new(label: EdgeLabel, sign: EdgeSign) -> Self {
        Self { label, sign }
    }

    /// Check if this edge matches (can be adjacent to) another edge.
    /// A+ matches A-, B+ matches B-, etc. L matches L (undirected).
    pub fn matches(&self, other: &Self) -> bool {
        self.label == other.label
            && match self.label {
                EdgeLabel::L => true, // L is undirected
                _ => self.sign != other.sign,
            }
    }
}

/// A placed metatile in a patch: type, orientation, and position.
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct Metatile {
    pub tile_type: MetatileType,
    /// Rotation index (0..5 for 60-degree increments).
    pub orientation: u8,
    /// Position in hexagonal lattice coordinates.
    pub position: (i64, i64),
}

impl Metatile {
    pub fn new(tile_type: MetatileType, orientation: u8, position: (i64, i64)) -> Self {
        Self {
            tile_type,
            orientation: orientation % 6,
            position,
        }
    }
}

/// The 29-child inflation rules, derived from the hat metatile substitution.
///
/// Each rule describes how to place one child metatile relative to existing children:
/// - `Seed(type)`: place the first child at the origin
/// - `Adjacent { parent, vertex, child_type, child_vertex }`: place child_type
///   adjacent to parent at the specified vertices
/// - `Bridge { parent_a, vertex_a, parent_b, vertex_b, child_type, child_vertex }`:
///   place using two reference parents
#[derive(Clone, Debug)]
pub enum InflationRule {
    Seed(MetatileType),
    Adjacent {
        parent: usize,
        vertex: usize,
        child_type: MetatileType,
        child_vertex: usize,
    },
    Bridge {
        parent_a: usize,
        vertex_a: usize,
        parent_b: usize,
        vertex_b: usize,
        child_type: MetatileType,
        child_vertex: usize,
    },
}

/// The 29 inflation rules extracted from the hat tiling substitution.
///
/// These rules place 29 metatiles starting from a single H seed, building outward
/// by adjacency. The constructMetatiles step then groups subsets of these 29 children
/// into the four supertile types H', T', P', F'.
pub fn inflation_rules() -> Vec<InflationRule> {
    use InflationRule::*;
    use MetatileType::*;
    vec![
        Seed(H),                                                                      // 0: H
        Adjacent { parent: 0, vertex: 0, child_type: P, child_vertex: 2 },            // 1: P
        Adjacent { parent: 1, vertex: 0, child_type: H, child_vertex: 2 },            // 2: H
        Adjacent { parent: 2, vertex: 0, child_type: P, child_vertex: 2 },            // 3: P
        Adjacent { parent: 3, vertex: 0, child_type: H, child_vertex: 2 },            // 4: H
        Adjacent { parent: 4, vertex: 4, child_type: P, child_vertex: 2 },            // 5: P
        Adjacent { parent: 0, vertex: 4, child_type: F, child_vertex: 3 },            // 6: F
        Adjacent { parent: 2, vertex: 4, child_type: F, child_vertex: 3 },            // 7: F
        Bridge { parent_a: 4, vertex_a: 1, parent_b: 3, vertex_b: 2, child_type: F, child_vertex: 0 }, // 8: F
        Adjacent { parent: 8, vertex: 3, child_type: H, child_vertex: 0 },            // 9: H
        Adjacent { parent: 9, vertex: 2, child_type: P, child_vertex: 0 },            // 10: P
        Adjacent { parent: 10, vertex: 2, child_type: H, child_vertex: 0 },           // 11: H
        Adjacent { parent: 11, vertex: 4, child_type: P, child_vertex: 2 },           // 12: P
        Adjacent { parent: 12, vertex: 0, child_type: H, child_vertex: 2 },           // 13: H
        Adjacent { parent: 13, vertex: 0, child_type: F, child_vertex: 3 },           // 14: F
        Adjacent { parent: 14, vertex: 2, child_type: F, child_vertex: 1 },           // 15: F
        Adjacent { parent: 15, vertex: 3, child_type: H, child_vertex: 4 },           // 16: H
        Adjacent { parent: 8, vertex: 2, child_type: F, child_vertex: 1 },            // 17: F
        Adjacent { parent: 17, vertex: 3, child_type: H, child_vertex: 0 },           // 18: H
        Adjacent { parent: 18, vertex: 2, child_type: P, child_vertex: 0 },           // 19: P
        Adjacent { parent: 19, vertex: 2, child_type: H, child_vertex: 2 },           // 20: H
        Adjacent { parent: 20, vertex: 4, child_type: F, child_vertex: 3 },           // 21: F
        Adjacent { parent: 20, vertex: 0, child_type: P, child_vertex: 2 },           // 22: P
        Adjacent { parent: 22, vertex: 0, child_type: H, child_vertex: 2 },           // 23: H
        Adjacent { parent: 23, vertex: 4, child_type: F, child_vertex: 3 },           // 24: F
        Adjacent { parent: 23, vertex: 0, child_type: F, child_vertex: 3 },           // 25: F
        Adjacent { parent: 16, vertex: 0, child_type: P, child_vertex: 2 },           // 26: P
        Bridge { parent_a: 9, vertex_a: 4, parent_b: 0, vertex_b: 2, child_type: T, child_vertex: 2 }, // 27: T
        Adjacent { parent: 4, vertex: 0, child_type: F, child_vertex: 3 },            // 28: F
    ]
}

/// Child indices belonging to each supertile type after inflation.
///
/// After building the 29-child patch via `inflation_rules()`, these index sets
/// identify which children form each level-1 supertile. 22 of the 29 children
/// are assigned; the remaining 7 are boundary children shared with neighbors.
pub const SUPERTILE_H_CHILDREN: &[usize] = &[0, 9, 16, 27, 26, 6, 1, 8, 10, 15];
pub const SUPERTILE_T_CHILDREN: &[usize] = &[11];
pub const SUPERTILE_P_CHILDREN: &[usize] = &[7, 2, 3, 4, 28];
pub const SUPERTILE_F_CHILDREN: &[usize] = &[21, 20, 22, 23, 24, 25];

/// The 7 boundary children not assigned to any supertile.
///
/// These children are shared with neighboring supertiles during inflation.
/// Together with the 22 assigned children, they account for all 29 inflation children.
pub const BOUNDARY_CHILDREN: &[usize] = &[5, 12, 13, 14, 17, 18, 19];

/// Count the metatile types within each supertile.
///
/// Returns a 4x4 array where result[i][j] = number of metatiles of type j
/// in supertile of type i.
pub fn supertile_composition() -> [[usize; 4]; 4] {
    let rules = inflation_rules();

    let child_type = |idx: usize| -> MetatileType {
        match &rules[idx] {
            InflationRule::Seed(t) => *t,
            InflationRule::Adjacent { child_type, .. } => *child_type,
            InflationRule::Bridge { child_type, .. } => *child_type,
        }
    };

    let mut counts = [[0usize; 4]; 4];
    let supertile_children: [&[usize]; 4] = [
        SUPERTILE_H_CHILDREN,
        SUPERTILE_T_CHILDREN,
        SUPERTILE_P_CHILDREN,
        SUPERTILE_F_CHILDREN,
    ];

    for (super_idx, children) in supertile_children.iter().enumerate() {
        for &child_idx in *children {
            let t = child_type(child_idx);
            counts[super_idx][t.index()] += 1;
        }
    }

    counts
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn inflation_rules_count() {
        assert_eq!(inflation_rules().len(), 29);
    }

    #[test]
    fn supertile_children_cover_correctly() {
        // Total assigned children
        let total = SUPERTILE_H_CHILDREN.len()
            + SUPERTILE_T_CHILDREN.len()
            + SUPERTILE_P_CHILDREN.len()
            + SUPERTILE_F_CHILDREN.len();
        assert_eq!(total, 22); // 7 boundary children are unassigned

        // No duplicate assignments
        let mut all: Vec<usize> = Vec::new();
        all.extend_from_slice(SUPERTILE_H_CHILDREN);
        all.extend_from_slice(SUPERTILE_T_CHILDREN);
        all.extend_from_slice(SUPERTILE_P_CHILDREN);
        all.extend_from_slice(SUPERTILE_F_CHILDREN);
        all.sort();
        let len = all.len();
        all.dedup();
        assert_eq!(all.len(), len, "duplicate child assignments");
    }

    #[test]
    fn supertile_composition_values() {
        let comp = supertile_composition();
        //           H  T  P  F
        // H' =    [ 3, 1, 3, 3 ]  (10 children)
        // T' =    [ 1, 0, 0, 0 ]  (1 child)
        // P' =    [ 2, 0, 1, 2 ]  (5 children)
        // F' =    [ 2, 0, 1, 3 ]  (6 children)
        assert_eq!(comp[0], [3, 1, 3, 3]);
        assert_eq!(comp[1], [1, 0, 0, 0]);
        assert_eq!(comp[2], [2, 0, 1, 2]);
        assert_eq!(comp[3], [2, 0, 1, 3]);
    }

    #[test]
    fn supertile_child_counts() {
        assert_eq!(SUPERTILE_H_CHILDREN.len(), 10);
        assert_eq!(SUPERTILE_T_CHILDREN.len(), 1);
        assert_eq!(SUPERTILE_P_CHILDREN.len(), 5);
        assert_eq!(SUPERTILE_F_CHILDREN.len(), 6);
    }

    #[test]
    fn boundary_and_assigned_children_cover_all_29() {
        // The 22 assigned + 7 boundary children must account for all 29 inflation children
        let mut all: Vec<usize> = Vec::new();
        all.extend_from_slice(SUPERTILE_H_CHILDREN);
        all.extend_from_slice(SUPERTILE_T_CHILDREN);
        all.extend_from_slice(SUPERTILE_P_CHILDREN);
        all.extend_from_slice(SUPERTILE_F_CHILDREN);
        all.extend_from_slice(BOUNDARY_CHILDREN);
        all.sort();
        all.dedup();
        assert_eq!(all.len(), 29, "should have exactly 29 unique children");
        assert_eq!(all, (0..29).collect::<Vec<_>>(), "should cover indices 0..28");
    }

    #[test]
    fn edge_matching() {
        let a_plus = SignedEdge::new(EdgeLabel::A, EdgeSign::Plus);
        let a_minus = SignedEdge::new(EdgeLabel::A, EdgeSign::Minus);
        let b_plus = SignedEdge::new(EdgeLabel::B, EdgeSign::Plus);
        let l = SignedEdge::new(EdgeLabel::L, EdgeSign::Plus);
        let l2 = SignedEdge::new(EdgeLabel::L, EdgeSign::Minus);

        assert!(a_plus.matches(&a_minus));
        assert!(a_minus.matches(&a_plus));
        assert!(!a_plus.matches(&a_plus));
        assert!(!a_plus.matches(&b_plus));
        assert!(l.matches(&l2)); // L is undirected
    }

    #[test]
    fn hat_counts() {
        assert_eq!(MetatileType::H.hat_count(), 4);
        assert_eq!(MetatileType::T.hat_count(), 1);
        assert_eq!(MetatileType::P.hat_count(), 2);
        assert_eq!(MetatileType::F.hat_count(), 2);
    }
}
