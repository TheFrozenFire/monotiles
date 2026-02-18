use ark_ff::PrimeField;

use crate::types::FoldingChallenge;

/// Fiat-Shamir transcript using Blake3 as the hash function.
///
/// Absorbs commitments and squeezes challenges deterministically,
/// converting an interactive oracle proof to non-interactive.
#[derive(Clone, Debug)]
pub struct Transcript {
    hasher: blake3::Hasher,
}

impl Transcript {
    /// Create a new transcript with a domain-separation label.
    pub fn new(label: &[u8]) -> Self {
        let mut hasher = blake3::Hasher::new();
        hasher.update(b"tiling-iop-v1:");
        hasher.update(label);
        Self { hasher }
    }

    /// Absorb a Merkle root commitment.
    pub fn absorb_commitment(&mut self, root: &[u8; 32]) {
        self.hasher.update(b"commit:");
        self.hasher.update(root);
    }

    /// Squeeze a folding challenge (one field element per tile type).
    pub fn squeeze_challenge<F: PrimeField>(&mut self, num_types: usize) -> FoldingChallenge<F> {
        let coeffs = (0..num_types)
            .map(|i| {
                let label = format!("r_{}", i);
                self.squeeze_field_element(label.as_bytes())
            })
            .collect();
        FoldingChallenge { coeffs }
    }

    /// Squeeze a random query index in [0, max).
    pub fn squeeze_query_index(&mut self, max: usize) -> usize {
        self.hasher.update(b"query:");
        let hash = self.hasher.finalize();
        let bytes = hash.as_bytes();
        // Use first 8 bytes as u64, then reduce modulo max
        let val = u64::from_le_bytes(bytes[..8].try_into().unwrap());
        // Re-absorb to advance state
        self.hasher.update(hash.as_bytes());
        (val % max as u64) as usize
    }

    /// Squeeze a single field element from the transcript.
    fn squeeze_field_element<F: PrimeField>(&mut self, label: &[u8]) -> F {
        self.hasher.update(label);
        let hash = self.hasher.finalize();
        // Re-absorb the hash output to advance the state
        self.hasher.update(hash.as_bytes());
        // Interpret hash bytes as a field element (reduces mod p)
        F::from_le_bytes_mod_order(hash.as_bytes())
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use ark_bls12_381::Fr;

    #[test]
    fn deterministic_challenges() {
        let root = [0xABu8; 32];

        let mut t1 = Transcript::new(b"test");
        t1.absorb_commitment(&root);
        let c1: FoldingChallenge<Fr> = t1.squeeze_challenge(4);

        let mut t2 = Transcript::new(b"test");
        t2.absorb_commitment(&root);
        let c2: FoldingChallenge<Fr> = t2.squeeze_challenge(4);

        assert_eq!(c1.coeffs, c2.coeffs);
    }

    #[test]
    fn different_labels_different_challenges() {
        let root = [0xABu8; 32];

        let mut t1 = Transcript::new(b"label-a");
        t1.absorb_commitment(&root);
        let c1: FoldingChallenge<Fr> = t1.squeeze_challenge(4);

        let mut t2 = Transcript::new(b"label-b");
        t2.absorb_commitment(&root);
        let c2: FoldingChallenge<Fr> = t2.squeeze_challenge(4);

        assert_ne!(c1.coeffs[0], c2.coeffs[0]);
    }

    #[test]
    fn different_commitments_different_challenges() {
        let mut t1 = Transcript::new(b"test");
        t1.absorb_commitment(&[0x11u8; 32]);
        let c1: FoldingChallenge<Fr> = t1.squeeze_challenge(4);

        let mut t2 = Transcript::new(b"test");
        t2.absorb_commitment(&[0x22u8; 32]);
        let c2: FoldingChallenge<Fr> = t2.squeeze_challenge(4);

        assert_ne!(c1.coeffs[0], c2.coeffs[0]);
    }

    #[test]
    fn challenges_are_nonzero() {
        let mut t = Transcript::new(b"test");
        t.absorb_commitment(&[0x42u8; 32]);
        let c: FoldingChallenge<Fr> = t.squeeze_challenge(4);

        for coeff in &c.coeffs {
            assert_ne!(*coeff, Fr::from(0u64));
        }
    }

    #[test]
    fn query_indices_in_range() {
        let mut t = Transcript::new(b"test");
        t.absorb_commitment(&[0x42u8; 32]);

        for _ in 0..20 {
            let idx = t.squeeze_query_index(100);
            assert!(idx < 100);
        }
    }

    #[test]
    fn different_num_types_different_challenges() {
        let root = [0xABu8; 32];

        let mut t1 = Transcript::new(b"test");
        t1.absorb_commitment(&root);
        let c1: FoldingChallenge<Fr> = t1.squeeze_challenge(2);

        let mut t2 = Transcript::new(b"test");
        t2.absorb_commitment(&root);
        let c2: FoldingChallenge<Fr> = t2.squeeze_challenge(4);

        // 2-type challenge coeffs match the first 2 of 4-type challenge
        assert_eq!(c1.coeffs[0], c2.coeffs[0]);
        assert_eq!(c1.coeffs[1], c2.coeffs[1]);
        assert_eq!(c1.coeffs.len(), 2);
        assert_eq!(c2.coeffs.len(), 4);
    }
}
