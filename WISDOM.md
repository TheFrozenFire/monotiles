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

## Finite Patches Are Boundary-Dominated

Deflating a level-3 H-patch (442 metatiles) produces only 4 interior supertiles and **403 unresolved boundary tiles** — 91% of the patch. The interior is tiny compared to the boundary because a level-3 patch is only one supertile deep: its 10 level-0 children expand to 442 tiles, but only 4 of those children form complete supertiles when deflated one more level.

This means any experiment on deflation must account for boundary effects. Testing "can we deflate?" on a finite patch is misleading unless you distinguish interior (easily deflatable) from boundary (inherently ambiguous without neighboring supertile context). The one-way analysis sidesteps this by working within the hierarchy itself, not on a geometric patch.

## Recovery Over-Generates by Design

Erasing 3 tiles from a 442-tile patch and running recovery produces **251 recovered tiles** — 83x the erasure size. All 3 erased tiles are correctly matched, but 248 are "extra." This isn't a bug: recovery works by deflating the surrounding context to identify the supertile structure, then re-inflating. It necessarily regenerates the entire supertile region, not just the erased tiles.

This has implications for any error-correcting code built on tiling recovery: the correction granularity is the supertile, not the individual tile. You can't surgically fix one tile without regenerating its entire neighborhood.

## Type-Bag Confusability Follows from Subset Relations

The P'↔F' swap (the only valid single-tile swap in the hat system) exists because F' = P' + 1F at the type-bag level. The child multisets are:

```
P' = {2H, 1P, 2F}  (5 children)
F' = {2H, 1P, 3F}  (6 children)
```

P's bag is a sub-multiset of F's bag. Any supertile type whose bag is a sub-multiset of another's creates a potential swap. The hat system has exactly one such pair. The spectre system (2 types, no subset relations between their child bags) has **zero** confusable pairs.

This means confusability is a property of the substitution matrix's column structure, not of the geometry. You can predict all confusable pairs from the matrix alone without generating any tiles.

## H-Supertile Identification Requires Only One T-Tile

The minimum determining set for H' is a single tile: the T at position 3. This works because T-type children appear **only** in H-supertiles (the T' row of the substitution matrix is [1, 0, 0, 0]). Seeing any T-child immediately identifies the parent as H.

In contrast, P' and F' require all their children because they differ by only one F-tile and share all other child types. The determining set size is controlled by the confusability structure, not the supertile size.
