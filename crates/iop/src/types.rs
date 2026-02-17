use ark_ff::Field;
use tiling::metatile::MetatileType;

/// Reference from a parent tile to one of its children in the hierarchy.
#[derive(Clone, Debug)]
pub struct ChildRef {
    /// Index of this child in the parent's level (level k-1).
    pub child_index: usize,
    /// Metatile type of this child.
    pub child_type: MetatileType,
}

/// Oracle values and structure for a single level of the tiling hierarchy.
#[derive(Clone, Debug)]
pub struct LevelOracle<F: Field> {
    pub level: usize,
    /// Field element assigned to each tile at this level.
    pub values: Vec<F>,
    /// Metatile type of each tile at this level.
    pub tile_types: Vec<MetatileType>,
    /// For each tile at this level, its children at the level below.
    /// Empty for level 0 (base).
    pub children: Vec<Vec<ChildRef>>,
}

/// The full hierarchical tiling structure from base (level 0) to top (level depth).
#[derive(Clone, Debug)]
pub struct TilingHierarchy<F: Field> {
    /// Levels from 0 (base tiles) to depth (single root).
    pub levels: Vec<LevelOracle<F>>,
    pub seed: MetatileType,
    pub depth: usize,
}

/// Per-round folding challenge with one random field element per metatile type.
#[derive(Clone, Debug)]
pub struct FoldingChallenge<F: Field> {
    pub r_h: F,
    pub r_t: F,
    pub r_p: F,
    pub r_f: F,
}

impl<F: Field> FoldingChallenge<F> {
    /// Get the challenge coefficient for a given metatile type.
    pub fn for_type(&self, t: MetatileType) -> F {
        match t {
            MetatileType::H => self.r_h,
            MetatileType::T => self.r_t,
            MetatileType::P => self.r_p,
            MetatileType::F => self.r_f,
        }
    }
}

/// Merkle commitment to a single level's oracle values.
#[derive(Clone, Debug)]
pub struct LevelCommitment {
    pub root: [u8; 32],
    pub num_leaves: usize,
    pub level: usize,
}

/// Commitments to all levels of the tiling hierarchy.
#[derive(Clone, Debug)]
pub struct TilingCommitment {
    pub level_commitments: Vec<LevelCommitment>,
    pub depth: usize,
}

/// Merkle inclusion proof for a single leaf.
#[derive(Clone, Debug)]
pub struct MerkleProof {
    pub leaf_index: usize,
    /// Sibling hashes along the path from leaf to root.
    pub path: Vec<[u8; 32]>,
}

/// Opening of a single child tile: its value and Merkle proof.
#[derive(Clone, Debug)]
pub struct ChildOpening<F: Field> {
    pub child_index: usize,
    pub child_type: MetatileType,
    pub value: F,
    pub proof: MerkleProof,
}

/// A query response for one supertile at one level: the supertile value and all child openings.
#[derive(Clone, Debug)]
pub struct QueryResponse<F: Field> {
    pub level: usize,
    pub supertile_index: usize,
    pub supertile_type: MetatileType,
    pub supertile_value: F,
    pub supertile_proof: MerkleProof,
    pub children: Vec<ChildOpening<F>>,
}

/// The complete IOP proof: commitments, challenges, query responses, and final values.
#[derive(Clone, Debug)]
pub struct TilingProof<F: Field> {
    pub commitment: TilingCommitment,
    pub challenges: Vec<FoldingChallenge<F>>,
    /// queries[round][query_index] = QueryResponse for that round/query.
    pub queries: Vec<Vec<QueryResponse<F>>>,
    /// Values at the top level (should be a single tile for depth > 0).
    pub final_values: Vec<F>,
}
