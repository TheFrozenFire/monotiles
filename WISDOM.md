# Wisdom: What We Learned from Formalizing the Hat Tiling

Insights gained from implementing the hat monotile theory in Rust and then formalizing it in ROCQ (Coq). These are things the paper doesn't emphasize, the code doesn't surface, and informal reasoning glosses over.

## Eigenvector Conventions Matter

The Perron-Frobenius eigenvector for the hat substitution matrix is a **left** eigenvector (v^T M = λ v^T), not a right eigenvector (Mv = λv). The Rust spectral code computed left eigenvectors silently. When we naively tried to verify Mv = λv in ROCQ, it failed.

For non-symmetric matrices, left and right eigenvectors are genuinely different vectors. This is the kind of sign/convention error that can hide in floating-point code indefinitely.

## det(M) = -1 Is Structural

The substitution matrix has determinant exactly -1, placing it in GL(4,Z) — it has an integer inverse. The characteristic polynomial factors as:

```
λ⁴ - 7λ³ + 7λ - 1 = (λ - 1)(λ + 1)(λ² - 7λ + 1)
```

The palindromic structure (coefficients 1, -7, 0, 7, -1) reflects a duality between the Perron and anti-Perron eigenvalues. The Rust spectral code treats these as "two roots of a quadratic" — the algebraic structure explaining *why* they pair up is invisible in floating-point.

## The 22/7 Boundary Split

Of the 29 children in an H-inflation, exactly 22 are assigned to supertile types and 7 are boundary (shared with neighboring supertiles). The boundary indices [5, 12, 13, 14, 17, 18, 19] aren't highlighted in the paper — they fell out of comparing the `SUPERTILE_*_CHILDREN` constants against the full child list. The formalization forced us to account for every single child.

## The Eigenvector Has Clean Algebraic Form

Over Z[√5], the Perron eigenvector scaled by 2 to clear denominators is:

```
2v = [(2, 0), (7, -3), (-12, 6), (9, -3)]
```

where (a, b) represents a + b√5. The component sum is (6, 0) = 6 — a pure integer. This means the normalized frequency vector sums to 3, and the actual metatile frequencies are rational linear combinations of φ. The Rust code had floats; you'd never notice this structure.

## The Hat Tiling's Continued Fraction Creates Different Combinatorics

The hat tiling slope (5 - √5)/10 has continued fraction [0; 3, 1, 1, 1, ...]. The first partial quotient being 3 (not 1) means the central word lengths follow a generalized Fibonacci sequence starting from (1, 4):

```
Standard Fibonacci: 1, 1, 2, 3, 5, 8, 13, 21, 34, ...
Hat tiling:         1, 1, 4, 5, 9, 14, 23, 37, ...
```

The Rust code computed this numerically, but the algebraic distinction — and its consequences for word complexity — is invisible in floating-point.

## Aperiodicity Witnesses Are Specific

The Cucaracha's trivial stabilizer proof requires a concrete witness: under 60-degree rotation, tile `cuc_ba` maps to (0, 0, 2, 0) which is NOT in the cucaracha. Our first guess (`cuc_id`) was wrong — it maps to `cuc_ba` which IS in the cucaracha.

The Rust code checked this with a boolean loop over all tiles. The formalization forced us to find exactly *which* tile breaks the symmetry and *why*.

## Fibonacci Word Frequencies Are Exactly Fibonacci Numbers

In the length-34 Fibonacci word prefix: exactly 13 ones and 21 zeros. The triple (13, 21, 34) consists of three consecutive Fibonacci numbers. The Rust code verified that the *ratio* approaches 1/φ², but the exact integer structure is stronger: the counts are always consecutive Fibonacci numbers, not just approximately golden-ratio distributed.

## What Formalization Does and Doesn't Do

The formalization verified existing mathematics — we didn't discover new theorems. What it did was force precision at every joint between concepts:

- Eigenvalue conventions (left vs right)
- Boundary accounting (22 + 7 = 29)
- Algebraic number representations (Z[√5] with "times 2" scaling)
- Witness selection (which tile breaks symmetry)
- Integer vs floating-point structure (Fibonacci counts, palindromic polynomials)

These are exactly the places where bugs hide in computational code and where informal proofs wave their hands. The Rust code was correct, but the formalization explained *why* it was correct in ways the code alone couldn't.

## The Local-to-Global Gap Is All-or-Nothing

The gap between local indistinguishability and global rigidity in hierarchical substitution tilings closes as a **sharp phase transition**, not a gradual curve. At every hierarchical radius below the depth, advantage is ~0% — no tile can determine which seed generated its tiling. At radius = depth, advantage jumps to 100% in a single step.

This is because the substitution is **recursively self-similar**: the local structure within any finite subtree is fully determined by the subtree root's type, independent of what's above it in the hierarchy. Two tiles from different seeds but with the same ancestor chain up to level k are locally indistinguishable at radius k. Only when the chain reaches the seed (radius = depth) does the difference become visible.

The BFS-based type signature (used in one-way analysis) makes this even starker: with sibling adjacency, a tile can determine its immediate parent type at radius 1, but **cannot determine any higher ancestor** regardless of radius. The adjacency graph is disconnected at supertile boundaries, creating an absolute information barrier. The only way to see past this barrier is to observe the hierarchy itself — the ancestor type chain.

This means the local-to-global gap is **information-theoretic, not computational**. It's not that determining the seed is *hard* — it's that the information simply isn't present in any finite local neighborhood of the base tiling. The gap closes the instant you can see the seed, and not one step sooner.

## Mutual Information Reveals Partial Structure Before the Gap Closes

While the distinguishing advantage (fraction of tiles with seed-unique signatures) is 0 for all radii below depth, the **mutual information** between seed and signature is nonzero starting at radius 1-2. This is because the *distribution* of tiles across signatures varies by seed, even when no individual signature is unique.

For example, in the hat system at depth 3: seeing grandparent type T rules out P-seed and F-seed (they don't produce T-type level-2 tiles at that depth), concentrating probability on H-seed and T-seed. This partial information shows up as positive mutual information even though no tile can deterministically identify its seed.

The gap between "zero advantage" and "positive mutual information" is the difference between **deterministic** and **probabilistic** distinguishability. A Bayesian observer gains information before the gap closes; a deterministic algorithm cannot.
