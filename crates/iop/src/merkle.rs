use ark_ff::Field;

use crate::types::MerkleProof;

/// Binary Merkle tree over Blake3, committing to (type, value) leaves.
#[derive(Clone, Debug)]
pub struct MerkleTree {
    /// All nodes in the tree. nodes[0] is unused; nodes[1] is the root.
    /// For a tree with `n` leaves (padded to next power of 2):
    ///   leaves are at indices n..2n
    ///   internal nodes at indices 1..n
    nodes: Vec<[u8; 32]>,
    /// Number of real (non-padding) leaves.
    num_leaves: usize,
    /// Number of leaves after padding to next power of 2.
    padded_size: usize,
}

/// Hash a leaf: Blake3(0x01 || type_byte || value_bytes).
fn hash_leaf<F: Field>(tile_type: usize, value: &F) -> [u8; 32] {
    let mut hasher = blake3::Hasher::new();
    hasher.update(&[0x01]); // leaf domain separator
    hasher.update(&[tile_type as u8]);
    // Serialize the field element
    let mut buf = Vec::new();
    ark_serialize::CanonicalSerialize::serialize_compressed(value, &mut buf)
        .expect("field serialization");
    hasher.update(&buf);
    *hasher.finalize().as_bytes()
}

/// Hash an internal node: Blake3(0x02 || left || right).
fn hash_node(left: &[u8; 32], right: &[u8; 32]) -> [u8; 32] {
    let mut hasher = blake3::Hasher::new();
    hasher.update(&[0x02]); // internal node domain separator
    hasher.update(left);
    hasher.update(right);
    *hasher.finalize().as_bytes()
}

/// Hash for padding leaves (all zeros).
fn zero_hash() -> [u8; 32] {
    [0u8; 32]
}

impl MerkleTree {
    /// Build a Merkle tree from (type, value) leaves.
    pub fn build<F: Field>(leaves: &[(usize, F)]) -> Self {
        assert!(!leaves.is_empty(), "cannot build tree from empty leaves");

        let num_leaves = leaves.len();
        let padded_size = num_leaves.next_power_of_two();
        let total_nodes = 2 * padded_size;

        let mut nodes = vec![[0u8; 32]; total_nodes];

        // Hash leaves into positions padded_size..2*padded_size
        for (i, (t, v)) in leaves.iter().enumerate() {
            nodes[padded_size + i] = hash_leaf(*t, v);
        }
        // Padding leaves get zero hash
        for i in num_leaves..padded_size {
            nodes[padded_size + i] = zero_hash();
        }

        // Build internal nodes bottom-up
        for i in (1..padded_size).rev() {
            nodes[i] = hash_node(&nodes[2 * i], &nodes[2 * i + 1]);
        }

        Self {
            nodes,
            num_leaves,
            padded_size,
        }
    }

    /// Root hash of the tree.
    pub fn root(&self) -> [u8; 32] {
        self.nodes[1]
    }

    /// Number of real (non-padding) leaves.
    pub fn num_leaves(&self) -> usize {
        self.num_leaves
    }

    /// Generate a Merkle inclusion proof for the leaf at `index`.
    pub fn open(&self, index: usize) -> MerkleProof {
        assert!(index < self.num_leaves, "leaf index out of bounds");

        let mut path = Vec::new();
        let mut pos = self.padded_size + index;

        while pos > 1 {
            // Sibling is the other child of the same parent
            let sibling = pos ^ 1;
            path.push(self.nodes[sibling]);
            pos >>= 1; // move to parent
        }

        MerkleProof {
            leaf_index: index,
            path,
        }
    }

    /// Verify a Merkle proof against a root hash.
    pub fn verify<F: Field>(
        root: &[u8; 32],
        proof: &MerkleProof,
        tile_type: usize,
        value: &F,
        num_leaves: usize,
    ) -> bool {
        let padded_size = num_leaves.next_power_of_two();
        let mut hash = hash_leaf(tile_type, value);
        let mut pos = padded_size + proof.leaf_index;

        for sibling_hash in &proof.path {
            hash = if pos & 1 == 0 {
                // Current node is left child
                hash_node(&hash, sibling_hash)
            } else {
                // Current node is right child
                hash_node(sibling_hash, &hash)
            };
            pos >>= 1;
        }

        hash == *root
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use ark_bls12_381::Fr;

    #[test]
    fn single_leaf_tree() {
        let leaves = vec![(0usize, Fr::from(42u64))];
        let tree = MerkleTree::build(&leaves);
        assert_eq!(tree.num_leaves(), 1);

        let proof = tree.open(0);
        assert!(MerkleTree::verify(&tree.root(), &proof, 0usize, &Fr::from(42u64), 1));
    }

    #[test]
    fn wrong_value_rejected() {
        let leaves = vec![(0usize, Fr::from(42u64))];
        let tree = MerkleTree::build(&leaves);
        let proof = tree.open(0);

        assert!(!MerkleTree::verify(
            &tree.root(),
            &proof,
            0usize,
            &Fr::from(99u64),
            1
        ));
    }

    #[test]
    fn wrong_type_rejected() {
        let leaves = vec![(0usize, Fr::from(42u64))];
        let tree = MerkleTree::build(&leaves);
        let proof = tree.open(0);

        assert!(!MerkleTree::verify(
            &tree.root(),
            &proof,
            1usize,
            &Fr::from(42u64),
            1
        ));
    }

    #[test]
    fn multi_leaf_openings() {
        let leaves: Vec<_> = (0..4usize)
            .enumerate()
            .map(|(i, t)| (t, Fr::from((i + 1) as u64)))
            .collect();

        let tree = MerkleTree::build(&leaves);

        for (i, (t, v)) in leaves.iter().enumerate() {
            let proof = tree.open(i);
            assert!(
                MerkleTree::verify(&tree.root(), &proof, *t, v, leaves.len()),
                "proof failed for leaf {}",
                i
            );
        }
    }

    #[test]
    fn non_power_of_two_leaves() {
        // 5 leaves should pad to 8
        let leaves: Vec<_> = (0..5).map(|i| (0usize, Fr::from(i as u64))).collect();

        let tree = MerkleTree::build(&leaves);
        assert_eq!(tree.padded_size, 8);

        for i in 0..5 {
            let proof = tree.open(i);
            assert!(MerkleTree::verify(
                &tree.root(),
                &proof,
                0usize,
                &Fr::from(i as u64),
                5
            ));
        }
    }

    #[test]
    fn deterministic_root() {
        let leaves: Vec<_> = (0..3).map(|i| (2usize, Fr::from(i as u64))).collect();

        let tree1 = MerkleTree::build(&leaves);
        let tree2 = MerkleTree::build(&leaves);
        assert_eq!(tree1.root(), tree2.root());
    }
}
