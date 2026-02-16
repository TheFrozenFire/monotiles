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
}
