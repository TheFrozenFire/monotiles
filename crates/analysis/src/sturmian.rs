/// Generate the lower mechanical Sturmian word s_{alpha,rho}(n) = floor((n+1)*alpha + rho) - floor(n*alpha + rho).
///
/// A Sturmian word has complexity p(n) = n + 1 for all n, making it the
/// simplest aperiodic infinite word. The slope alpha determines the frequency
/// of 1s (which equals alpha for irrational alpha).
///
/// For the hat tiling, the relevant slope is alpha = (5 - sqrt(5))/10 = 1/(1 + tau^2)
/// where tau = (1+sqrt(5))/2 is the golden ratio.
pub fn sturmian_word(alpha: f64, rho: f64, n: usize) -> Vec<u8> {
    (0..n)
        .map(|k| {
            let curr = ((k + 1) as f64 * alpha + rho).floor();
            let prev = (k as f64 * alpha + rho).floor();
            (curr - prev) as u8
        })
        .collect()
}

/// Generate the Fibonacci word: the Sturmian word with slope 1/phi^2 = (3 - sqrt(5))/2.
///
/// This is the most studied Sturmian word, intimately connected to the golden ratio
/// and Penrose/hat tiling frequencies.
pub fn fibonacci_word(n: usize) -> Vec<u8> {
    let phi = (1.0 + 5.0_f64.sqrt()) / 2.0;
    let alpha = 1.0 / (phi * phi); // = 2 - phi = (3 - sqrt(5))/2
    sturmian_word(alpha, 0.0, n)
}

/// Generate central words (standard words) up to level n.
///
/// Central words are palindromic prefixes of the Sturmian characteristic word.
/// They are constructed by the recurrence:
/// - w_{-1} = "1", w_0 = "0"
/// - w_{n+1} = w_n^{d_n} w_{n-1}
///
/// where [0; d_1, d_2, ...] is the continued fraction expansion of alpha.
/// For the Fibonacci case (alpha = 1/phi^2), all d_i = 1.
pub fn central_words_fibonacci(n: usize) -> Vec<Vec<u8>> {
    let mut words = Vec::with_capacity(n + 2);

    // w_{-1} = "1"
    words.push(vec![1u8]);
    // w_0 = "0"
    words.push(vec![0u8]);

    // For Fibonacci: all partial quotients are 1, so w_{n+1} = w_n w_{n-1}
    for i in 0..n {
        let prev = words[i + 1].clone();
        let pprev = words[i].clone();
        let mut next = prev;
        next.extend_from_slice(&pprev);
        words.push(next);
    }

    words
}

/// General central words for continued fraction [0; d_1, d_2, ...].
///
/// w_{n+1} = w_n^{d_{n+1}} w_{n-1} (concatenation of d_{n+1} copies of w_n followed by w_{n-1}).
pub fn central_words(partial_quotients: &[usize]) -> Vec<Vec<u8>> {
    let mut words = Vec::with_capacity(partial_quotients.len() + 2);

    words.push(vec![1u8]); // w_{-1}
    words.push(vec![0u8]); // w_0

    for &d in partial_quotients {
        let w_n = words[words.len() - 1].clone();
        let w_n_minus_1 = words[words.len() - 2].clone();

        let mut next = Vec::new();
        for _ in 0..d {
            next.extend_from_slice(&w_n);
        }
        next.extend_from_slice(&w_n_minus_1);

        words.push(next);
    }

    words
}

/// Compute the complexity function p(n) for a finite word.
///
/// p(n) = number of distinct subwords (factors) of length n.
/// For a Sturmian word, p(n) = n + 1 for all n.
pub fn complexity(word: &[u8], n: usize) -> usize {
    if n == 0 || n > word.len() {
        return if n == 0 { 1 } else { 0 };
    }

    let mut factors: std::collections::HashSet<&[u8]> = std::collections::HashSet::new();
    for window in word.windows(n) {
        factors.insert(window);
    }
    factors.len()
}

/// Generate the hat tiling Sturmian word with slope (5 - sqrt(5))/10 = 1/(2 + phi).
///
/// This slope is the lower GAB root q- = (5-sqrt(5))/10, confirmed equal to the
/// continued fraction [0; 3, 1, 1, 1, ...] = 1/(2+phi). It is NOT the PF metatile
/// instance frequency f_H = 1/3; it is the Sturmian symbol density.
/// The continued fraction is [0; 3, 1, 1, 1, ...] = [0; 3, phi^{-1}].
pub fn hat_sturmian_word(n: usize) -> Vec<u8> {
    let alpha = (5.0 - 5.0_f64.sqrt()) / 10.0; // = 1/(1 + phi^2)
    sturmian_word(alpha, 0.0, n)
}

/// Generate central words for the hat tiling slope [0; 3, 1, 1, 1, ...].
///
/// The first partial quotient is 3, then all subsequent ones are 1 (golden continued fraction).
pub fn hat_central_words(levels: usize) -> Vec<Vec<u8>> {
    let mut pq = vec![3];
    pq.extend(std::iter::repeat_n(1, levels.saturating_sub(1)));
    central_words(&pq)
}

/// A Golden Sturmian Patch: a geometric realization of a Sturmian subword
/// as a linear strip of metatiles.
///
/// Each position in the Sturmian word maps to a metatile type:
/// - 0 → a "short" tile (P-type parallelogram)
/// - 1 → a "long" tile (H-type hexagon)
///
/// This provides the 1D combinatorial skeleton of the hat tiling.
#[derive(Clone, Debug)]
pub struct GoldenSturmianPatch {
    /// The Sturmian word defining the strip.
    pub word: Vec<u8>,
    /// The tile types assigned to each position.
    pub tiles: Vec<SturmianTile>,
}

/// A tile in a Sturmian strip.
#[derive(Clone, Debug, PartialEq)]
pub struct SturmianTile {
    /// 0 = short (P), 1 = long (H)
    pub tile_type: u8,
    /// Cumulative position along the strip.
    pub position: f64,
    /// Length of this tile.
    pub length: f64,
}

/// Generate a Golden Sturmian Patch from a Sturmian word.
///
/// Maps the binary word to a strip where:
/// - 0 → tile of length 1 (short, corresponding to P-type)
/// - 1 → tile of length phi (long, corresponding to H-type)
pub fn golden_sturmian_patch(word: &[u8]) -> GoldenSturmianPatch {
    let phi = (1.0 + 5.0_f64.sqrt()) / 2.0;
    let mut tiles = Vec::with_capacity(word.len());
    let mut pos = 0.0;

    for &symbol in word {
        let length = if symbol == 0 { 1.0 } else { phi };
        tiles.push(SturmianTile {
            tile_type: symbol,
            position: pos,
            length,
        });
        pos += length;
    }

    GoldenSturmianPatch {
        word: word.to_vec(),
        tiles,
    }
}

impl GoldenSturmianPatch {
    /// Total length of the patch strip.
    pub fn total_length(&self) -> f64 {
        self.tiles.iter().map(|t| t.length).sum()
    }

    /// Ratio of long tiles to total tiles, converging to 1/phi^2 for Sturmian words.
    pub fn long_tile_ratio(&self) -> f64 {
        if self.tiles.is_empty() {
            return 0.0;
        }
        let long_count = self.tiles.iter().filter(|t| t.tile_type == 1).count();
        long_count as f64 / self.tiles.len() as f64
    }
}

/// Generate the exact Fibonacci word via morphism iteration.
///
/// Uses the Fibonacci morphism sigma: 0 -> 01, 1 -> 0.
/// After n iterations starting from "0", the word has length F(n+1)
/// where F is the Fibonacci sequence (1, 1, 2, 3, 5, 8, 13, 21, 34, ...).
///
/// The counts are always consecutive Fibonacci numbers:
/// - count of 0s = F(n), count of 1s = F(n-1)
/// - This is exact, not approximate — the counts ARE Fibonacci numbers,
///   not just approximately golden-ratio distributed.
pub fn fibonacci_word_exact(iterations: usize) -> Vec<u8> {
    let mut word = vec![0u8];
    for _ in 0..iterations {
        let mut next = Vec::with_capacity(word.len() * 2);
        for &symbol in &word {
            match symbol {
                0 => { next.push(0); next.push(1); }
                1 => { next.push(0); }
                _ => unreachable!(),
            }
        }
        word = next;
    }
    word
}

/// Compute the frequency of symbol 1 in a word.
pub fn frequency_of_ones(word: &[u8]) -> f64 {
    if word.is_empty() {
        return 0.0;
    }
    let count = word.iter().filter(|&&b| b == 1).count();
    count as f64 / word.len() as f64
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn fibonacci_word_prefix() {
        let w = fibonacci_word(13);
        // Lower mechanical Sturmian word with slope 1/phi^2 and offset 0
        assert_eq!(&w[..13], &[0, 0, 1, 0, 0, 1, 0, 1, 0, 0, 1, 0, 0]);
    }

    #[test]
    fn fibonacci_word_frequency_approaches_one_over_phi_sq() {
        let phi = (1.0 + 5.0_f64.sqrt()) / 2.0;
        let expected = 1.0 / (phi * phi); // frequency of 1s

        let w = fibonacci_word(10000);
        let freq = frequency_of_ones(&w);
        assert!((freq - expected).abs() < 0.01);
    }

    #[test]
    fn sturmian_complexity_is_n_plus_one() {
        let w = fibonacci_word(100);
        for n in 1..=20 {
            assert_eq!(
                complexity(&w, n),
                n + 1,
                "complexity({}) should be {} for Sturmian word",
                n,
                n + 1
            );
        }
    }

    #[test]
    fn central_words_fibonacci_lengths() {
        let words = central_words_fibonacci(8);
        // Fibonacci sequence: 1, 1, 2, 3, 5, 8, 13, 21, 34, 55
        let expected_lens = [1, 1, 2, 3, 5, 8, 13, 21, 34, 55];
        for (i, word) in words.iter().enumerate() {
            assert_eq!(
                word.len(),
                expected_lens[i],
                "word {} length mismatch",
                i
            );
        }
    }

    #[test]
    fn central_words_fibonacci_recurrence() {
        let words = central_words_fibonacci(6);
        // Verify the recurrence: w_{n+1} = w_n ++ w_{n-1} for Fibonacci (all d_i = 1)
        for i in 0..6 {
            let mut expected = words[i + 1].clone();
            expected.extend_from_slice(&words[i]);
            assert_eq!(
                words[i + 2], expected,
                "recurrence failed at level {}",
                i + 2
            );
        }
    }

    #[test]
    fn general_central_words_with_partial_quotients() {
        // Silver ratio: [0; 2, 2, 2, ...]
        let words = central_words(&[2, 2, 2]);
        // w_{-1} = "1", w_0 = "0"
        // w_1 = "00" + "1" = "001"
        // w_2 = "001001" + "0" = "0010010"
        assert_eq!(words[0], vec![1]);
        assert_eq!(words[1], vec![0]);
        assert_eq!(words[2], vec![0, 0, 1]);
        assert_eq!(words[3], vec![0, 0, 1, 0, 0, 1, 0]);
    }

    #[test]
    fn complexity_of_periodic_word() {
        // Periodic word "010101..." has p(n) = 2 for all n >= 1
        let word: Vec<u8> = (0..100).map(|i| (i % 2) as u8).collect();
        assert_eq!(complexity(&word, 1), 2);
        assert_eq!(complexity(&word, 2), 2);
        assert_eq!(complexity(&word, 5), 2);
    }

    #[test]
    fn complexity_boundary_cases() {
        let word = vec![0, 1, 0];
        assert_eq!(complexity(&word, 0), 1);
        assert_eq!(complexity(&word, 4), 0); // longer than word
    }

    #[test]
    fn hat_sturmian_word_is_sturmian() {
        let w = hat_sturmian_word(100);
        // Sturmian: complexity p(n) = n + 1
        for n in 1..=10 {
            assert_eq!(complexity(&w, n), n + 1, "hat Sturmian complexity({}) failed", n);
        }
    }

    #[test]
    fn hat_sturmian_frequency_correct() {
        let w = hat_sturmian_word(10000);
        let freq = frequency_of_ones(&w);
        let expected = (5.0 - 5.0_f64.sqrt()) / 10.0; // ~0.2764
        assert!((freq - expected).abs() < 0.01, "freq={}, expected={}", freq, expected);
    }

    #[test]
    fn hat_central_words_first_is_triple() {
        let words = hat_central_words(3);
        // w_1 = w_0^3 w_{-1} = "000" + "1" = "0001" (d_1 = 3)
        assert_eq!(words[2], vec![0, 0, 0, 1]);
    }

    #[test]
    fn fibonacci_word_exact_lengths_are_fibonacci() {
        // fibonacci_word_exact(n) has length F(n+1)
        // F sequence: 1, 1, 2, 3, 5, 8, 13, 21, 34, 55
        let expected_lens = [1, 2, 3, 5, 8, 13, 21, 34, 55];
        for (n, &expected) in expected_lens.iter().enumerate() {
            let w = fibonacci_word_exact(n);
            assert_eq!(w.len(), expected, "fibonacci_word_exact({}) should have length {}", n, expected);
        }
    }

    #[test]
    fn fibonacci_word_exact_counts_are_fibonacci_numbers() {
        // In fibonacci_word_exact(n), the counts of 0s and 1s are
        // consecutive Fibonacci numbers — this is exact, not approximate.
        //
        // n=7: length 34, with exactly 21 zeros and 13 ones.
        // (13, 21, 34) are three consecutive Fibonacci numbers.
        let w = fibonacci_word_exact(7);
        let ones = w.iter().filter(|&&b| b == 1).count();
        let zeros = w.iter().filter(|&&b| b == 0).count();
        assert_eq!(w.len(), 34);
        assert_eq!(zeros, 21, "exact Fibonacci count: 21 zeros");
        assert_eq!(ones, 13, "exact Fibonacci count: 13 ones");
    }

    #[test]
    fn fibonacci_word_exact_is_sturmian() {
        // The morphism word is the *characteristic* Sturmian word c_alpha,
        // which differs from the mechanical word s_{alpha,0} by a shift.
        // Both have identical complexity and frequency properties.
        let w = fibonacci_word_exact(7);
        for n in 1..=10 {
            assert_eq!(
                complexity(&w, n), n + 1,
                "morphism Fibonacci word should have Sturmian complexity"
            );
        }
    }

    #[test]
    fn golden_sturmian_patch_lengths() {
        let word = vec![0, 1, 0, 0, 1];
        let patch = golden_sturmian_patch(&word);
        assert_eq!(patch.tiles.len(), 5);

        // Total length: 1 + phi + 1 + 1 + phi = 3 + 2*phi
        let phi = (1.0 + 5.0_f64.sqrt()) / 2.0;
        let expected_len = 3.0 + 2.0 * phi;
        assert!((patch.total_length() - expected_len).abs() < 1e-10);
    }

    #[test]
    fn golden_sturmian_patch_positions_monotonic() {
        let w = fibonacci_word(20);
        let patch = golden_sturmian_patch(&w);
        for i in 1..patch.tiles.len() {
            assert!(
                patch.tiles[i].position > patch.tiles[i - 1].position,
                "positions should be strictly increasing"
            );
        }
    }

    #[test]
    fn golden_sturmian_patch_ratio_converges() {
        let w = fibonacci_word(1000);
        let patch = golden_sturmian_patch(&w);
        let phi = (1.0 + 5.0_f64.sqrt()) / 2.0;
        let expected = 1.0 / (phi * phi);
        assert!(
            (patch.long_tile_ratio() - expected).abs() < 0.01,
            "long tile ratio should approach 1/phi^2"
        );
    }
}
