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

P's bag is a sub-multiset of F's bag. Any supertile type whose bag is a sub-multiset of another's creates a potential swap. The hat system has exactly one such pair.

Counterintuitively, the spectre system also has exactly one confusable pair: Mystic'↔Spectre'. Their child bags are:

```
Mystic'  = {6 Spectre, 1 Mystic}  (7 children)
Spectre' = {7 Spectre, 1 Mystic}  (8 children)
```

Mystic's bag is a sub-multiset of Spectre's bag, differing by one Spectre tile. The assumption that a 2-type system would be simpler breaks down at the supertile level: the substitution rules create the sub-multiset relation even though the base tiles are homogeneous.

This means confusability is a property of the substitution matrix's column structure, not of the geometry or the number of base tile types. You can predict all confusable pairs from the matrix alone without generating any tiles.

## H-Supertile Identification Requires Only One T-Tile

The minimum determining set for H' is a single tile: the T at position 3. This works because T-type children appear **only** in H-supertiles (the T' row of the substitution matrix is [1, 0, 0, 0]). Seeing any T-child immediately identifies the parent as H.

In contrast, P' and F' require all their children because they differ by only one F-tile and share all other child types. The determining set size is controlled by the confusability structure, not the supertile size.

## Spectre's Dependency Structure Stabilizes at Depth 2, but Erasure Behavior Does Not

The spectre dependency graph (edges-per-tile, degree-0 fraction, max chain length) reaches a fixed point at depth 2 and does not change at depths 3 or 4. You might expect erasure behavior to similarly stabilize — but it doesn't. The plateau level keeps falling geometrically (100% → 87% → 42% → 7.5%) even as the local graph structure is constant.

The reason: erasure is a *global* propagation process, not a local one. Even though each tile's immediate neighborhood looks the same at every depth, the *number of hierarchy levels* a missing tile's absence must propagate through grows with depth. At depth 4 there are four levels of supertile ambiguity stacked above any erased tile; at depth 1 there is only one. The local structure is the same; the global cascade depth is not.

This is a general principle: when analyzing hierarchical structures, local graph properties (degree, connectivity) do not predict global erasure behavior. You need to measure at multiple depths to characterize the asymptotic regime.

## The Correcting/Detecting Spectrum Is Algebraic, Not Geometric

Hat and hat-turtle produce identical vulnerability results to the decimal place — same erasure threshold, same dependency graph, same confusable pairs, same minimum determining sets. They use different tile shapes (hat vs turtle) but share the same substitution matrix.

This means the correcting/detecting spectrum is a property of the **substitution matrix algebra**, not of the geometric tile shape. If you want to move a tiling system along the spectrum, you need to change the substitution rules — how many children each supertile type has, and what types they are. Changing the geometric realization of the same rules changes nothing.

The practical implication: testing additional geometric variants of hat (there are others in the literature) will not give new data points. To explore the spectrum, you need substitution systems with genuinely different matrix structures — different numbers of types, different child counts, different confusability patterns.

## Hat and Spectre Are Complementary Codes, Not Competing Ones

The erasure experiments (#17) initially looked like "hat good, spectre bad." But they're measuring complementary properties.

**Hat is a correcting code.** Its erasure resilience (~60-70% threshold) comes from structural heterogeneity: H' and T' are identifiable from a single child, acting as anchor types that bootstrap recovery of surrounding P'/F' tiles. The dependency graph is sparse (84% of tiles self-determined). This is structurally analogous to LDPC codes: sparse bipartite check graph, anchor nodes that seed iterative decoding, graceful degradation with a high threshold.

**Spectre is a detecting code.** Its 7-regular dependency graph means any single tile change immediately violates 7 sibling constraints, each of which cascades further. No anchor types exist — there are no cheap positions that an adversary can answer without maintaining full consistency. The detection sensitivity is uniform across the tiling. This is useful for tamper-evidence and integrity checking, where you want *any* modification to be caught, not necessarily recovered from.

The root cause is **type-level diversity**. More types with heterogeneous compositions create anchors — tiles whose type is uniquely diagnostic. Fewer types with similar compositions create uniformity — no tile is easier or harder to fake than any other. These are opposite design goals that serve opposite purposes.

**Implications for the IOP construction.** Hat-based IOPs favor efficiency: the prover can commit cheaply to H'/T' supertiles (one consistent child suffices) and the verifier's queries are faster to answer. Spectre-based IOPs favor soundness: a cheating prover has no cheap positions, every query requires a fully consistent fake hierarchy, and the avalanche structure means a single inconsistency is detectable from many query positions. If soundness is the binding constraint, spectre may be the stronger foundation despite worse erasure resilience.

**The no-reflection property compounds this.** Hat requires mirror tiles — a valid hat tiling admits local chirality choices. A prover constructing a fake hat hierarchy has some freedom to vary chirality locally without invalidating the hierarchy. Spectre tiles without reflections: every tile is the same handedness, and the orientation constraints are globally consistent. This removes a degree of freedom that a cheating prover could otherwise exploit. Spectre's geometric rigidity translates directly to commitment rigidity.

**The plateau behavior hints at a threshold access structure.** Spectre's determined% collapses from 100% to ~50% at just 10% erasure, then holds flat (~38-44%) through 20-70% erasure. This is not gradual degradation — it is a sharp threshold followed by a stable floor. Compared to secret sharing: you need ~90% of tiles to determine the hierarchy; below that you immediately lose roughly half of all type information and further loss changes little. Whether this threshold can be sharpened and the floor driven toward zero (making it a true (k,n) threshold structure) is an open question.

## Sibling Swaps Have Zero Cascade Cost — By a Combinatorial Identity (#32)

When you discover that a confusable sibling pair exists (two supertiles of types A and B sharing a parent, where B = A + 1 tile of `differing_type`), the natural next question is: does swapping their labels cascade upward? Do you have to relabel their parent too?

The answer is no, and the reason is a combinatorial identity so simple it's easy to miss.

**The swap operation.** A and B are siblings — children of the same parent P. B's composition is A's composition plus one extra tile of `differing_type`. To convert A→B and B→A: move one `differing_type` tile from B's child set to A's child set. A now has B's old composition, so it gets relabeled B. B now has A's old composition, so it gets relabeled A.

**Why the parent is unaffected.** Before the swap, P's child list contains (among other things) one instance of type A and one instance of type B. After the swap, P's child list contains one instance of type B (formerly A) and one instance of type A (formerly B). The *multiset* of child types is unchanged — it still has one A and one B. P's composition hasn't changed, so P's type doesn't change, so P's parent is unaffected, and so on all the way up.

**The identity.** Swapping two labeled elements in a multiset preserves the multiset. This is not a property of tilings specifically — it's true of any labeled collection. The cascade cost is zero because the swap is a permutation of labels on a fixed child set, not an addition or removal of elements.

**Why this is non-obvious.** It feels like changing two children's types should change the parent's composition, because "composition" tracks type counts. But the swap is symmetric: A loses one child and gains one child of the same net effect on the parent's count of A-labeled children (−1 becomes a B), and the parent's count of B-labeled children (+1 a new B, but −1 because B lost a label to A). The +1 and −1 cancel exactly.

**The practical implication.** This means the modification distance for sibling swaps is determined entirely by the structure at the level of the swapped pair, not by the density of dependencies above them. No matter how deeply entangled the hierarchy is above level k, a sibling swap at level k costs exactly 1 and propagates zero levels upward. The dense cascade structure of spectre (which gives it superior tamper detection against *random* erasure) provides no defense against this *adversarial* one-move attack on the combinatorial structure.

## Rust, ROCQ, and CAS Are Three Different Tools for Three Different Jobs

After building a substantial body of experimental findings and then reasoning about which open questions to pursue formally, the project falls into a clear three-way division that is easy to blur unless you think about it explicitly.

**Rust is the laboratory.** It runs experiments, measures behaviors at specific parameters, and produces data. The erasure sweeps, swap counts, proof size curves, and convergence observations are all Rust work. Rust answers "what happens at depth 3 with 100 trials?" It does not answer "does this hold for all depths?"

**ROCQ is the proof archive.** It takes the cleanest claims from the laboratory and establishes them as theorems that hold universally — not just for the depths and seeds we tested. ROCQ proves by structural induction, case analysis, and algebraic identity. It cannot run an erasure sweep, but it can prove that the local-to-global gap is zero below radius = depth for *every* depth, which the Rust experiments can only confirm for depths 3–6.

**A CAS (PARI/GP, SageMath, Magma) is the calculator.** It computes Galois groups, class numbers, Smith normal forms, discriminants, and zeta functions. These are one-shot algebraic computations — not experiments, not proofs. The results can then be recorded as facts (in RESEARCH.md) and optionally verified in ROCQ.

### Which open issues belong where

**ROCQ-primary** (the value is a universal formal proof, not a measurement):
- **#55** Smith normal form of the substitution matrices — Mathcomp's SNF algorithm gives a certified computation
- **#54** Exact closed form of spectre swap density — an algebraic identity certifiable in ROCQ
- Formalizing the cascade cost = 0 argument (#35 content) — two-case induction, ideal for ROCQ
- Formalizing canonical form uniqueness (#33 content) — structural induction on the inflation rule
- Formalizing the gap sharpness (#6/#16 content) — depth induction, establishes the universal claim
- Formalizing the bimodal cost landscape (#43) — extends the cascade proof to all non-sibling modifications
- The commitment scheme security proof (#44) — binding reduces to hash collision; hiding follows from the gap

**CAS-then-record** (algebraic number theory computations, results go to RESEARCH.md):
- **#49** Characteristic polynomial coefficients and Galois group — PARI `galoisinit`
- **#52** Number field invariants: discriminant, class number, unit group — PARI `bnfinit`
- **#56** Zeta function rational form and Mahler measure — symbolic computation from eigenvalues

**Rust-primary** (scale, measurement, iteration):
- **#40** Spectre threshold at depth 5–6 — needs large tile counts
- **#39** Semantic geometric IOP — needs implementation and measurement
- **#42** Fuzzy extractor erasure characterization — needs noise model experiments
- **#51** Spectral gap empirical validation — matrix powers, Frobenius norm decay
- **#53** Coordinate ring extraction — data extraction from the running tiling system

**Hybrid** (Rust or CAS for computation, ROCQ for the formal consequence):
- **#50** Pisot/Salem classification — CAS computes conjugate magnitudes; ROCQ verifies the exact polynomial has all other roots inside the unit circle
- **#43** Non-malleable code — Rust experiments on cost-2 modification outputs; ROCQ proves the bimodal landscape universally

### The key dependency

**#49 is the algebraic foundation.** The characteristic polynomial coefficients, minimal polynomial, and Galois group unlock #50, #51, #52, and #56 in parallel. Almost every number-theoretic issue depends on having the exact eigenvalue fields established first. Do #49 in a CAS before investing in ROCQ formalization of downstream results.

### Why this matters for the project trajectory

The Rust findings establish *what is true* at practical scales. The ROCQ proofs establish *why it must always be true*. Without ROCQ, the cryptographic primitive constructions (#42–#48) rest on empirically observed properties that could fail at untested scales or parameters. With ROCQ formalization of the core structural lemmas (gap sharpness, canonical form uniqueness, bimodal cost landscape, zero cascade), the security proofs for those primitives become formal reductions rather than handwaving.
