use ark_ff::Field;

/// Reference from a parent tile to one of its children in the hierarchy.
#[derive(Clone, Debug)]
pub struct ChildRef {
    /// Index of this child in the parent's level (level k-1).
    pub child_index: usize,
    /// Type index of this child (system-dependent).
    pub child_type: usize,
}

/// Oracle values and structure for a single level of the tiling hierarchy.
#[derive(Clone, Debug)]
pub struct LevelOracle<F: Field> {
    pub level: usize,
    /// Field element assigned to each tile at this level.
    pub values: Vec<F>,
    /// Type index of each tile at this level (system-dependent).
    pub tile_types: Vec<usize>,
    /// For each tile at this level, its children at the level below.
    /// Empty for level 0 (base).
    pub children: Vec<Vec<ChildRef>>,
}

/// The full hierarchical tiling structure from base (level 0) to top (level depth).
#[derive(Clone, Debug)]
pub struct TilingHierarchy<F: Field> {
    /// Levels from 0 (base tiles) to depth (single root).
    pub levels: Vec<LevelOracle<F>>,
    /// Type index of the seed tile at the top level.
    pub seed: usize,
    pub depth: usize,
}

/// Per-round folding challenge: one random field element per tile type.
#[derive(Clone, Debug)]
pub struct FoldingChallenge<F: Field> {
    /// coeffs[i] is the challenge coefficient for tile type i.
    pub coeffs: Vec<F>,
}

impl<F: Field> FoldingChallenge<F> {
    /// Get the challenge coefficient for a given type index.
    pub fn for_type(&self, type_idx: usize) -> F {
        self.coeffs[type_idx]
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
    pub child_type: usize,
    pub value: F,
    pub proof: MerkleProof,
}

/// A query response for one supertile at one level: the supertile value and all child openings.
#[derive(Clone, Debug)]
pub struct QueryResponse<F: Field> {
    pub level: usize,
    pub supertile_index: usize,
    pub supertile_type: usize,
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
    /// Supertile composition rules: composition[type_idx] = counts per child type.
    /// Used by the verifier to check child type distributions.
    pub composition: Vec<Vec<usize>>,
}
