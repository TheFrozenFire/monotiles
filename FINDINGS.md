# Findings: Experimental Results from Monotile Exploration

Empirical results from running experiments on the hat monotile and its algebraic structure. These are things we measured, not things we read.

---

## Table of Contents

- [Algebraic Foundations](#algebraic-foundations)
  - [Substitution Matrix Rows Predict Confusable Pairs (#18)](#substitution-matrix-rows-predict-confusable-pairs-18)
  - [Group Cryptography on Gamma = Z² ⋊ D₆ Is Not Viable (#8)](#group-cryptography-on-gamma--z--d-is-not-viable-8)
- [Erasure Resilience](#erasure-resilience)
  - [Deflation Is Not a One-Way Function (#5)](#deflation-is-not-a-one-way-function-5)
  - [Spectre vs Hat Erasure Resilience (#17)](#spectre-vs-hat-erasure-resilience-17)
  - [Spectre Erasure Plateau Collapses with Depth (#23)](#spectre-erasure-plateau-collapses-with-depth-23)
  - [Spectre Erasure Threshold Convergence at Depth 5–6 (#40)](#spectre-erasure-threshold-convergence-at-depth-56-40)
  - [Hat-Turtle Is Identical to Hat on the Correcting/Detecting Spectrum (#22)](#hat-turtle-is-identical-to-hat-on-the-correctingdetecting-spectrum-22)
  - [Concatenated Hat+Spectre Hybrid Code (#25)](#concatenated-hatspectre-hybrid-code-25)
- [Local-to-Global Gap and Ancestry](#local-to-global-gap-and-ancestry)
  - [The Local-to-Global Gap Is All-or-Nothing (#6)](#the-local-to-global-gap-is-all-or-nothing-6)
  - [Local-to-Global Gap Closes at Radius = Depth (#16)](#local-to-global-gap-closes-at-radius--depth-16)
  - [Cross-Supertile Adjacency Resolves Level-2 Ancestry (#13)](#cross-supertile-adjacency-resolves-level-2-ancestry-that-sibling-adjacency-cannot-13)
  - [Mutual Information Saturates After Level 1 for Hat, Immediately for Spectre (#15)](#mutual-information-saturates-after-level-1-for-hat-immediately-for-spectre-15)
  - [Joint Ancestor Knowledge Partially Restores Reconstruction Accuracy (#14)](#joint-ancestor-knowledge-partially-restores-reconstruction-accuracy-14)
  - [Minimum Useful Patch Size for Recovery (#19)](#minimum-useful-patch-size-for-recovery-19)
- [Sibling Swap Vulnerability](#sibling-swap-vulnerability)
  - [Minimum Modification Distance (#26)](#minimum-modification-distance-26)
  - [Geometric Modification Distance: Spectre Has Infinite, Hat Has 1 (#30)](#geometric-modification-distance-spectre-has-infinite-hat-has-1-30)
  - [Swap Opportunity Scaling with Depth (#29)](#swap-opportunity-scaling-with-depth-29)
  - [Non-Sibling Modification Cost Landscape (#35)](#non-sibling-modification-cost-landscape-35)
  - [Swap Density Convergence (#36)](#swap-density-convergence-36)
  - [Algebraic IOP Is Blind to Sibling Swaps (#31)](#algebraic-iop-is-blind-to-sibling-swaps-31)
  - [IOP Query Coverage of Swap-Vulnerable Positions (#34)](#iop-query-coverage-of-swap-vulnerable-positions-34)
  - [Steganographic Bit Channel in Sibling-Swap Ambiguity (#27)](#steganographic-bit-channel-in-sibling-swap-ambiguity-27)
- [IOP and Proof Construction](#iop-and-proof-construction)
  - [Tiling IOP Performance (#9)](#tiling-iop-performance-9)
  - [Spectre vs Hat IOP Soundness (#21)](#spectre-vs-hat-iop-soundness-21)
  - [IOP Proof Size Scaling Curve (#20)](#iop-proof-size-scaling-curve-20)
  - [IOP Tamper Detection Under Substitution Noise (#24)](#iop-tamper-detection-under-substitution-noise-24)
  - [Geometric Tile Placement: Position-as-Key Adds Only ~7% Proof Size Overhead (#28)](#geometric-tile-placement-position-as-key-adds-only-7-proof-size-overhead-28)
  - [IOP Canonical Form Defense: Zero-Cost Enforcement (#33)](#iop-canonical-form-defense-zero-cost-enforcement-33)
  - [Sparse Merkle Tree Commitment: Compact Key Has ~5-7 Hash Overhead, Enables Non-Membership Proofs (#37)](#sparse-merkle-tree-commitment-compact-key-has-5-7-hash-overhead-enables-non-membership-proofs-37)
  - [Semantic Geometric IOP: Spectre Adjacency Is Local, Hat Requires Cross-Supertile Openings (#39)](#semantic-geometric-iop-spectre-adjacency-is-local-hat-requires-cross-supertile-openings-39)
  - [Spectral Gap Ratio and Convergence Rates (#51)](#spectral-gap-ratio-and-convergence-rates-51)
- [Algebraic Number Theory (CAS Results)](#algebraic-number-theory-cas-results)
  - [Characteristic Polynomial, Minimal Polynomial, and Galois Group (#49)](#characteristic-polynomial-minimal-polynomial-and-galois-group-49)
  - [Pisot/Salem Classification of the Dominant Eigenvalues (#50)](#pisetsalem-classification-of-the-dominant-eigenvalues-50)
  - [Number Field Invariants of Q(λ_hat) and Q(λ_spe) (#52)](#number-field-invariants-of-λhat-and-λspe-52)
  - [Coordinate Ring of Tile Positions (#53)](#coordinate-ring-of-tile-positions-53)
  - [Exact Tile Frequencies and Swap Density Closed Forms (#54)](#exact-tile-frequencies-and-swap-density-closed-forms-54)
  - [Smith Normal Form of the Substitution Matrices (#55)](#smith-normal-form-of-the-substitution-matrices-55)
  - [Topological Entropy, Mahler Measure, and Substitution Zeta Function (#56)](#topological-entropy-mahler-measure-and-substitution-zeta-function-56)
  - [GAB Equation, Sturmian Slope, and Hat-Polykite Density (#57)](#gab-equation-sturmian-slope-and-hat-polykite-density-57)

---

## Algebraic Foundations

### Substitution Matrix Rows Predict Confusable Pairs (#18)

The substitution matrix rows predict confusable type pairs with no false positives or false negatives: a pair (A, B) is confusable iff their rows differ by exactly one unit vector.

#### Hat (4×4 matrix, order: H, T, P, F)

| Type | H | T | P | F |
|------|---|---|---|---|
| H'   | 3 | 1 | 3 | 3 |
| T'   | 1 | 0 | 0 | 0 |
| P'   | 2 | 0 | 1 | 2 |
| F'   | 2 | 0 | 1 | 3 |

Row differences for all pairs:

| Pair | Difference vector | Unit vector? | Confusable? |
|------|-------------------|--------------|-------------|
| H'↔T' | [2,1,3,3] | No | No |
| H'↔P' | [1,1,2,1] | No | No |
| H'↔F' | [1,1,2,0] | No | No |
| T'↔P' | [1,0,1,2] | No | No |
| T'↔F' | [1,0,1,3] | No | No |
| **P'↔F'** | **[0,0,0,1]** | **Yes (one F)** | **Yes ✓** |

Exactly one confusable pair predicted: P'↔F'. This matches the known vulnerability.

#### Spectre (2×2 matrix, order: Spectre, Mystic)

| Type | Spectre | Mystic |
|------|---------|--------|
| Spectre' | 7 | 1 |
| Mystic'  | 6 | 1 |

| Pair | Difference vector | Unit vector? | Confusable? |
|------|-------------------|--------------|-------------|
| **Spectre'↔Mystic'** | **[1,0]** | **Yes (one Spectre)** | **Yes ✓** |

#### Why this is the right condition

A sibling swap between supertile types A and B requires that a valid B can be constructed from A's children by moving exactly one child tile. Moving one child of type X changes A's row count for X by −1 and B's row count for X by +1. For both resulting compositions to remain valid supertile types, A's row after adding X must equal B's row, and B's row after removing X must equal A's row. This is exactly the unit-vector difference condition: `row_A + e_X = row_B`.

#### Corollary: hat-turtle

Hat-turtle delegates to hat's composition matrix, so it has the same single confusable pair P'↔F'. The prediction carries over unchanged.

#### Implication

Given the substitution matrix alone, one can enumerate all confusable pairs in O(n²) time (n = number of tile types) by checking all row pairs for unit-vector differences. No geometry or inflation rule walk needed.

---

### Group Cryptography on Gamma = Z² ⋊ D₆ Is Not Viable (#8)

We tested three candidate hard problems for the Cucaracha's Coxeter group Gamma, motivated by the question of whether the tiling constraint could inject hardness into an otherwise tractable group.

#### Cotiler Recovery

Given the cotiler group G_C (generated by pairwise quotients of tile positions), recover the cotiler C (up to translation).

| Size | Brute-force time | Solutions | Notes |
|------|-----------------|-----------|-------|
| 1 | 0.00 ms | 1 | Trivial |
| 2 | ~0.2 ms | 1-2 | Fast |
| 3 | ~3 ms | 3 | Fast |
| 4 | ~50 ms | 2-4 | Manageable |
| 5 | ~6,000 ms | 1-5 | Exponential blowup begins |
| 6 | >31,000 ms | budget exceeded (10M nodes) | Combinatorial explosion |

The bottleneck is C(candidates, n-1) where candidates grow as ~n²×4. At size 6, the candidate pool reaches ~136 elements, giving C(136, 5) ≈ 500M subsets to check.

**Coset decomposition doesn't help.** We implemented a coset-based algorithm that groups candidates by their Z² translation component and backtracks over translation classes (at most 12 D₆ decorations each). Result: ~1.0x speedup across all sizes. The translation classes are too numerous — there are roughly as many classes as individual candidates, so the grouping provides no reduction.

#### Region Decomposition (Exact Cover)

Given the covered cells (forgetting tile boundaries), recover which tiles placed them.

| Size | Mean time | Solutions | Notes |
|------|-----------|-----------|-------|
| 1-20 | 0.00-0.07 ms | always exactly 1 | Linear scaling |

Trivially easy at all tested sizes. The Cucaracha's shape is sufficiently constrained that backtracking with a most-constrained-cell heuristic finds the unique decomposition almost immediately.

#### Stabilizer Statistics

Compute the symmetry group of a random cotiler.

| Size | Trials | Trivial (|Stab|=1) | Threefold (|Stab|=3) |
|------|--------|-------------------|---------------------|
| 1-20 | 10 each | 100% | 0% |

All 200 random cotilers tested had trivial stabilizer. The threefold symmetry (rotation by 120°) that is theoretically possible never appeared in random growth.

#### Verdict

All three problems are easy or show only brute-force combinatorial hardness (not algebraic hardness). The virtually abelian structure of Gamma = Z² ⋊ D₆ makes group-theoretic hard problems (word problem, conjugacy problem) trivially solvable. The tiling constraint adds a geometric overlap check but does not create cryptographically useful hardness — it's an NP-style constraint satisfaction problem, not a one-way function.

The recovery scaling is exponential in cotiler size, but this is a consequence of naive subset enumeration over a polynomially-growing candidate pool, not of any deep algebraic structure. The coset comparison confirms this: exploiting the group's Z² ⋊ D₆ decomposition provides zero speedup because the hardness was never group-theoretic to begin with.

---

## Erasure Resilience

### Deflation Is Not a One-Way Function (#5)

The inflation/deflation asymmetry in the hat metatile substitution system does **not** constitute a computationally one-way function. Deflation is locally solvable.

#### Results (hat and spectre, depth 3)

| Analysis | Hat | Spectre |
|----------|-----|---------|
| Full sibling adjacency | All tiles determined, radius ≤ 1 | All tiles determined, radius ≤ 1 |
| Inflation adjacency | All tiles determined, radius ≤ 4 | All tiles determined, radius ≤ 1 |
| Type-bag decomposition | Always unique (det(M) = -1) | Always unique (det(M) = 1) |
| Greedy deflation | 100% assignment rate | 100% assignment rate |

The asymmetry between inflation (O(n) local rule application) and deflation (recovering supertile boundaries) is **implementation convenience, not computational hardness**. A radius-1 neighborhood in the full sibling adjacency graph suffices to determine parent assignments for every tile.

The hat's inflation adjacency graph requires radius 4 because H-supertiles are disconnected in this sparser graph — some children lack intra-supertile neighbors. But this is an artifact of the graph choice, not an inherent barrier. The spectre, with its simpler 2-type system, resolves everything at radius 1 even with inflation adjacency.

---

### Spectre vs Hat Erasure Resilience (#17)

The spectre system has **worse** erasure resilience than the hat, contradicting the hypothesis that fewer tile types would yield better tolerance.

#### Confusable pairs: both systems have exactly one

| Property | Hat | Spectre |
|----------|-----|---------|
| Tile types | 4 (H/T/P/F) | 2 (Spectre/Mystic) |
| Supertile types | 4 (H'/T'/P'/F') | 2 (Spectre'/Mystic') |
| Valid swaps | 1: P'(5) + 1F = F'(6) | 1: Mystic'(7) + 1Spectre = Spectre'(8) |
| Critical positions | 0/22 (0.0%) | 0/15 (0.0%) |

The hypothesis that spectre has zero confusable pairs was wrong. The sub-multiset relationship exists at the supertile level: Mystic' is a proper sub-multiset of Spectre', differing by one Spectre tile.

_See also [#18](#substitution-matrix-rows-predict-confusable-pairs-18): confusable pairs are exactly the unit-vector row differences in the substitution matrix._

#### Minimum determining sets

| Supertile | Children | Min det. set | Notes |
|-----------|----------|-------------|-------|
| **Hat H'** | 10 | **1** (pos 3, a T) | T only appears in H-supertiles |
| **Hat T'** | 1 | **1** (pos 0, an H) | Only 1 child total |
| Hat P' | 5 | 5 (all) | Confusable with F' |
| Hat F' | 6 | 6 (all) | Confusable with P' |
| Spectre Spectre' | 8 | **7** (all non-Mystic) | Confusable with Mystic' |
| Spectre Mystic' | 7 | **7** (all) | Confusable with Spectre' |

Hat has two "anchor" types (H', T') identifiable from a single child. Spectre has **no anchors** — both types require all children for determination.

#### Hat erasure threshold (depth 3, H-patch, 442 tiles)

Random erasure of base tiles from a depth-3 H-patch (442 tiles):

| Erasure % | Surviving % | Determined % |
|-----------|------------|-------------|
| 0% | 100.0% | 100.0% |
| 10% | 90.0% | 79.7% |
| 30% | 69.9% | 67.8% |
| 50% | 50.0% | 60.2% |
| 70% | 30.1% | 48.0% |
| 90% | 10.0% | 35.6% |

The "Determined %" exceeds "Surviving %" at erasure fractions above ~45% — meaning the hierarchical structure allows recovery of more tiles than survive the erasure. The phase transition to complete loss is at ~60-70% erasure.

#### Erasure sweep comparison (depth 3, 100 trials)

| Erasure % | Hat surviving | Hat determined | Spectre surviving | Spectre determined |
|-----------|-------------|---------------|-------------------|-------------------|
| 0% | 100.0% | 100.0% | 100.0% | 100.0% |
| 10% | 90.0% | 79.7% | 89.9% | 50.1% |
| 20% | 80.1% | 72.9% | 80.0% | 38.4% |
| 30% | 69.9% | 67.8% | 70.0% | 38.2% |
| 40% | 60.0% | 65.2% | 60.1% | 39.6% |
| 50% | 50.0% | 60.2% | 50.0% | 42.6% |
| 60% | 40.0% | 55.2% | 39.9% | 44.1% |
| 70% | 30.1% | 48.0% | 30.0% | 44.2% |
| 80% | 19.9% | 41.9% | 20.0% | 38.0% |
| 90% | 10.0% | 35.6% | 10.1% | 34.5% |

Hat degrades gracefully, with determined% exceeding surviving% above ~45% erasure. Spectre collapses immediately: 10% erasure destroys half of all type determination. The spectre determined% then plateaus around 38-44% through the mid-range, never exceeding surviving%.

**Phase transition**: Hat at ~60-70% erasure. Spectre at ~10-20% erasure.

#### Dependency graph comparison

| Metric | Hat | Spectre |
|--------|-----|---------|
| Base tiles (depth 3) | 442 | 496 |
| Total edges | 360 | 2,695 |
| Edges per tile | 0.81 | 5.43 |
| Has cycles | yes | yes |
| Max chain length | 4 | 8 |
| Max in-degree | 5 | 7 |
| Degree-0 tiles (self-determined) | 370 (83.7%) | 111 (22.4%) |
| High-degree tiles | 72 at degree 5 | 385 at degree 7 |

Hat's graph is sparse: 84% of tiles are self-determined (degree 0), with only 16% depending on siblings. Spectre's graph is dense: 78% of tiles depend on all 7 siblings, creating cascading failures under erasure.

#### Why fewer types means worse resilience

The counter-intuitive result comes from three reinforcing factors:

1. **No anchor types.** Hat's 4-type system includes H' and T', which are identifiable from a single child tile. These act as fixed recovery points — even heavy erasure leaves many anchors intact. Spectre's 2-type system has no such anchors; both types are mutually confusable.

2. **Universal confusability.** In hat, only P' and F' participate in the confusable pair (2 of 4 types). In spectre, *both* types participate (2 of 2 types). Every supertile boundary is vulnerable, not just some.

3. **Dense dependency cascades.** Spectre's larger supertile size (7-8 children vs 1-10 for hat) means each tile depends on more siblings. Losing one tile affects 7 others, which affect 7 more each. Hat's bimodal structure (most tiles at degree 0) contains cascades.

The hypothesis confused *type-level diversity* with *structural resilience*. Having more types with heterogeneous compositions creates natural anchoring points. Fewer types with homogeneous compositions means every boundary is equally fragile.

---

### Spectre Erasure Plateau Collapses with Depth (#23)

_Established in [#17](#spectre-vs-hat-erasure-resilience-17): spectre has no anchor types and collapses at the very first erasure step. This section shows how that collapse worsens with depth._

The spectre system's erasure resilience degrades sharply with hierarchy depth. The plateau level (determined% at mid-range erasure) falls geometrically, and the threshold location shifts toward lower erasure rates.

#### Erasure sweep by depth (spectre, 100 trials)

| Erasure % | Depth 1 (8 tiles) | Depth 2 (63 tiles) | Depth 3 (496 tiles) | Depth 4 (3905 tiles) |
|-----------|------------------|-------------------|--------------------|--------------------|
| 10% | 100.0% | 73.4% | 50.1% | 46.8% |
| 20% | 100.0% | 80.7% | 38.4% | 23.2% |
| 30% | 100.0% | 84.1% | 38.2% | 10.8% |
| 40% | 100.0% | 85.0% | 39.6% | 8.5% |
| 50% | 100.0% | 87.2% | 42.6% | 7.6% |
| 60% | 100.0% | 85.6% | 44.1% | 7.2% |
| 70% | 100.0% | 86.5% | 44.2% | 6.9% |
| 80% | 100.0% | 79.2% | 38.0% | 7.4% |
| 90% | 100.0% | 73.7% | 34.5% | 8.1% |
| Phase transition | ~90-100% | ~90-100% | ~10-20% | **~0-10%** |

#### Summary of structural metrics by depth

| Depth | Base tiles | Dep. edges | Edges/tile | Degree-0 % | Max chain |
|-------|-----------|-----------|-----------|-----------|-----------|
| 1 | 8 | 0 | 0.00 | 100% | 0 |
| 2 | 63 | 343 | 5.44 | 22.2% | 8 |
| 3 | 496 | 2,695 | 5.43 | 22.4% | 8 |
| 4 | 3,905 | 21,217 | 5.43 | 22.4% | 8 |

The dependency graph structure **stabilizes at depth 2**: edges-per-tile, degree-0 fraction, and max chain length are all constant from depth 2 onward. This is a fixed-point of the substitution structure.

#### Two anomalies worth noting

**Depth 1 is perfectly resilient.** At depth 1 (a single Spectre'/Mystic' supertile, 8 base tiles), the dependency graph has zero edges and every tile is degree-0. All tiles stay fully determined under any partial erasure (up to 90%). The tiling is trivially recoverable because there is only one supertile and all children collectively identify it.

**Depth 2 inverts the relationship.** Determined% *exceeds* surviving% across nearly the full erasure range (e.g., 87.2% determined at 50% erasure vs 49.2% surviving). The hierarchy does real recovery work — partial context is enough to reconstruct more than survives. This is the correcting-code regime. By depth 3 the relationship inverts, and by depth 4 it collapses entirely.

#### The threshold sharpens with depth

At depth 4, losing just 10% of tiles immediately reduces determined% to 46.8%; losing 20% drops it to 23.2%; from 30% onward it plateaus near 7-8%. The system is converging toward a **true threshold structure**: below a ~90% survival rate, almost nothing is determinable. This is the opposite of the error-correcting code property — it is an all-or-nothing information lock.

The plateau level progression (100% → 87% → 42% → 7.5%) is consistent with exponential decay per depth level. If the trend continues, depth 5 would yield a plateau near ~1-2%, and depth 6 near ~0%. A depth-5 or depth-6 spectre hierarchy would approach a true (k,n) threshold scheme where k ≈ 0.90n tiles are needed to determine anything at all.

---

### Hat-Turtle Is Identical to Hat on the Correcting/Detecting Spectrum (#22)

_See [#17](#spectre-vs-hat-erasure-resilience-17) for the hat baseline metrics (360 dep. graph edges, 83.7% degree-0, erasure threshold ~60-70%); hat-turtle matches all of them exactly._

Hat-turtle produces identical vulnerability results to hat on every measurable metric, to the decimal place.

| Metric | Hat | Hat-Turtle |
|--------|-----|------------|
| Valid swaps | 1: P'↔F' | 1: P'↔F' |
| Critical positions | 0/22 (0%) | 0/22 (0%) |
| Min det. set H' | 1 | 1 |
| Min det. set T' | 1 | 1 |
| Min det. set P' | 5 (all) | 5 (all) |
| Min det. set F' | 6 (all) | 6 (all) |
| Erasure threshold | ~60-70% | ~60-70% |
| Dep. graph edges | 360 | 360 |
| Max chain length | 4 | 4 |
| Degree-0 tiles | 370 (83.7%) | 370 (83.7%) |
| Base tiles (depth 3) | 442 | 442 |

The erasure sweep is also identical:

| Erasure % | Hat determined | Hat-Turtle determined |
|-----------|---------------|----------------------|
| 10% | 79.7% | 79.7% |
| 30% | 67.8% | 67.8% |
| 50% | 60.2% | 60.2% |
| 70% | 48.0% | 48.0% |
| 90% | 35.6% | 35.6% |

#### Interpretation

Hat and hat-turtle share the same substitution matrix — they differ only in the geometric shape of the base tile (hat vs turtle), not in the algebraic rules of how supertiles compose. The vulnerability analysis depends entirely on the substitution matrix (child type-bags, confusable pairs, dependency structure), not on tile geometry. Identical matrix → identical spectrum position.

**The correcting/detecting spectrum has only two points so far: {hat, hat-turtle} at one end and {spectre} at the other.** Hat-turtle does not give us a third data point between them — it confirms hat and hat-turtle are the same point. The spectrum is determined by substitution algebra, not tile shape. Testing additional geometric variants of the same substitution system will not move the needle.

---

### Spectre Erasure Threshold Convergence at Depth 5–6 (#40)

**Setup:** `cargo run --release -- vulnerability --depth 5 -S spectre --erasure-trials 100 --skip-graph` and `--depth 6`. Added `--skip-graph` flag to skip O(n²) dependency graph (30,744 and 242,047 tiles respectively; graph structure already known to stabilize at depth 2 from #23). Runtimes: depth 5 = 9s, depth 6 = 78s.

#### Erasure sweep at depths 5–6 (spectre, 100 trials)

| Erasure % | Depth 5 (30,744 tiles) | Depth 6 (242,047 tiles) |
|-----------|------------------------|------------------------|
| 0% | 100.0% | 100.0% |
| 10% | 46.6% | 46.5% |
| 20% | 22.7% | 22.7% |
| 30% | 10.1% | 10.0% |
| 40% | 3.9% | 3.9% |
| 50% | 1.4% | 1.3% |
| 60% | 1.7% | 0.3% |
| 70% | 1.2% | 0.2% |
| 80% | 1.4% | 0.2% |
| 90% | 1.1% | 0.2% |
| 100% | 0.0% | 0.0% |

#### Plateau progression across all depths

The "plateau" = the determined% floor at high erasure rates (50–90% erasure), where the curve flattens:

| Depth | Base tiles | Plateau (approx) | Depth-to-depth ratio |
|-------|-----------|-----------------|---------------------|
| 2 | 63 | ~87% | — |
| 3 | 496 | ~42% | 0.48 |
| 4 | 3,905 | ~7.5% | 0.18 |
| 5 | 30,744 | ~1.2% | 0.16 |
| 6 | 242,047 | ~0.2% | 0.17 |

The depth-to-depth ratio is converging to ~0.16–0.17 per level.

#### Key findings

1. **Depths 5 and 6 are nearly identical** across all erasure rates 0–40%. The erasure behavior has converged — further depth increases produce only marginal additional degradation.

2. **No sharp threshold emerges.** The hypothesis was that depth 5–6 would produce a sharp (k,n) threshold: "below ~90% survival, essentially nothing is determinable." This is **falsified**: at 10% erasure (90% survival), still 46.5% of surviving tiles are determined. The decay is gradual and exponential in erasure rate, not a sharp threshold.

3. **Asymptotic floor is ~0.2%, not 0.** From depth 6 onward, the plateau at high erasure rates stabilizes near 0.2%, not 0. This is the persistent "recoverable fraction" from structurally isolated tiles (the degree-0 fraction in the dependency graph = 22.4%, but at high erasure their chance of surviving as the unique representative is small).

4. **Convergence depth is 5–6.** The system reaches its asymptotic regime by depth 5–6. From the spectral gap analysis (#51), the spectre spectral gap gives convergence rate (4-√15)² ≈ 0.016 per level. But the OBSERVED plateau decay ratio (~0.16–0.17) is 10× larger than the spectral gap — the plateau decay is governed by a different mechanism (the geometric probability of complete sibling group survival, approximately (1-q)^8) not the spectral gap.

5. **What actually governs the plateau: group-survival probability.** At erasure rate q, a sibling group of 8 tiles survives intact with probability (1-q)^8. Only intact groups contribute to the plateau (ambiguous partial groups do not). At q=90% (10% survival): (0.1)^8 ≈ 0 → essentially no complete groups, matching the near-zero plateau. The decay ratio per depth level reflects the increasing compounding of partial groups, not the spectral gap.

#### What falsifies the hypothesis

The issue listed two falsification conditions:
- "The plateau level asymptotes above ~3%" — **partially confirmed**: asymptotes above 0% (~0.2%), but this is below 3%
- "The threshold location shifts to lower erasure rates" — **not confirmed**: the threshold (where determined% drops below 10%) stays near 30–40% erasure across depths 4–6

#### Conclusions

- The spectre erasure behavior converges by depth 5–6; no further degradation beyond depth 6.
- A sharp (k,n) threshold does NOT emerge — decay remains gradual.
- The plateau is ~0.2% at depth 6, making spectre effectively zero-resilience at depths ≥ 6 under any erasure above 30%.
- The depth-to-depth ratio (~0.17) is governed by sibling group-survival probability, not the spectral gap (0.016).
- The `--skip-graph` flag is needed for any vulnerability experiment at depth ≥ 5 (dependency graph is O(n²) in base tile count).

_See also: #23 (depths 1–4), #51 (spectral gap), #17 (no anchor types), #25 (hybrid code uses spectre at depth 2 only)._

---

### Concatenated Hat+Spectre Hybrid Code (#25)

_Established in [#17](#spectre-vs-hat-erasure-resilience-17): both hat and spectre have exactly 1 valid swap each (P'↔F' and Mystic'↔Spectre'). The original hypothesis that spectre has 0 valid swaps was refuted there._

**Hypothesis**: Concatenating hat (inner, erasure-correcting) and spectre (outer, tamper-detecting) into a hybrid code would improve both erasure resilience and tamper detection over either system alone.

**Experiment**: `cargo run --release -- hybrid-code --d-inner 2 --d-outer 2 --erasure-trials 100`. Inner code = hat at depth 2 (64 tiles/block); outer code = spectre at depth 2 (63 blocks). Baselines: hat-only at depth 4 and spectre-only at depth 4.

#### System sizes

| Configuration | Depth | Leaf tiles |
|--------------|-------|-----------|
| Hybrid (hat inner × spectre outer) | 2+2 | 4032 |
| Hat-only flat | 4 | 3025 |
| Spectre-only flat | 4 | 3905 |

#### Tamper detection: both layers have blind spots

**Refutes the original hypothesis.** Both hat and spectre have exactly 1 valid swap each:
- Hat (inner): P'↔F' — differ by 1 F-tile; composition check cannot distinguish within a block
- Spectre (outer): Mystic'↔Spectre' — Spectre' has 1 more Spectre child; composition check has the same blind spot at block level

The original hypothesis that spectre has 0 valid swaps was refuted by #17. The hybrid does not eliminate undetectable substitutions — it requires an adversary to simultaneously evade both layers, raising attack cost without removing the vulnerability.

#### Erasure thresholds

| Configuration | Erasure threshold (last fraction >50% determination) |
|--------------|------------------------------------------------------|
| Hat inner (depth 2) | 90% |
| Spectre outer (depth 2) | 90% |
| Hat-only flat (depth 4) | 40% |
| Spectre-only flat (depth 4) | 0% |

#### Uniform erasure recovery

| Erase% | Hat flat (d=4) | Hat inner (d=2) | Spectre outer (d=2) | Hybrid |
|--------|---------------|-----------------|---------------------|--------|
| 0% | 100.0% | 100.0% | 100.0% | 100.0% |
| 10% | 73.3% | 87.8% | 73.4% | **100.0%** |
| 20% | 63.5% | 86.5% | 80.7% | **100.0%** |
| 30% | 55.1% | 88.5% | 84.1% | **100.0%** |
| 40% | 50.4% | 86.7% | 85.0% | **100.0%** |
| 50% | 44.2% | 89.3% | 87.2% | **100.0%** |
| 60% | 37.9% | 84.8% | 85.6% | **100.0%** |
| 70% | 31.4% | 79.3% | 86.5% | **100.0%** |
| 80% | 24.3% | 74.6% | 79.2% | **100.0%** |
| 90% | 17.2% | 68.3% | 73.7% | **100.0%** |
| 100% | 0.0% | 0.0% | 0.0% | 0.0% |

The hybrid achieves 100% recovery at every uniform erasure fraction from 0–90%, dramatically outperforming hat-flat at depth 4 (which degrades immediately from 100% to 73.3% at 10% erasure).

#### Block-structured burst erasure recovery

| k blocks erased | Outer fraction | Hybrid recovery% | Hat-flat equiv% |
|----------------|---------------|-----------------|----------------|
| 1 | 1.6% | 100.0% | 100.0% |
| 2 | 3.2% | 100.0% | 100.0% |
| 4 | 6.3% | 100.0% | 73.3% |
| 8 | 12.7% | 100.0% | 63.5% |
| 16 | 25.4% | 100.0% | 55.1% |
| 32 | 50.8% | 100.0% | 31.4% |
| 63 | 100.0% | 0.0% | 0.0% |

Outer spectre threshold = 90% → up to 56 of 63 complete blocks can be erased and recovered. Hat-flat at depth 4 using leaf-level adjacency cannot exploit block structure; erasure of 32 blocks (50.8% outer fraction) reduces hat-flat to only 31.4% recovery.

#### Conclusions

1. **The zero-swap hypothesis for spectre was wrong.** Spectre has exactly 1 valid swap (Mystic'↔Spectre'), same as hat (P'↔F'). The hybrid does not give tamper-detection improvement — both layers have blind spots.

2. **The erasure advantage is real but structural, not compositional.** Keeping each layer at shallow depth (d=2) preserves both at 90% threshold. Concatenating them yields near-perfect recovery for uniform erasure up to 90%, vs hat-flat at depth 4 = 40%. The benefit is not "hat corrects, spectre detects" — it is that shallow layers outperform deep layers.

3. **Spectre depth collapse makes flat spectre useless at d=4.** Spectre-flat at depth 4 shows 0% threshold, consistent with [#23](#spectre-erasure-plateau-collapses-with-depth-23) on exponential depth collapse. The outer spectre at d=2 retains 90% threshold and is the reason the hybrid succeeds.

4. **Block-structured burst erasure is where the hybrid shines.** By maintaining a dedicated outer block-recovery layer, the hybrid recovers from complete-block erasures up to 50.8% outer fraction at 100% recovery, while hat-flat loses ground rapidly.

---

## Local-to-Global Gap and Ancestry

### The Local-to-Global Gap Is All-or-Nothing (#6)

The gap between local indistinguishability and global rigidity in hierarchical substitution tilings closes as a **sharp phase transition**, not a gradual curve.

#### Distinguishing advantage by radius (hat and spectre, depth 3)

| Radius | Hat Advantage | Spectre Advantage | Hat Normalized MI |
|--------|--------------|-------------------|-------------------|
| 0 | 0.0% | 0.0% | 0.000 |
| 1 | 0.0% | 0.0% | 0.001 |
| 2 | 1.0% | 0.0% | 0.055 |
| 3 (=depth) | **100.0%** | **100.0%** | **1.000** |

At every radius below depth, advantage is ~0%. At radius = depth, it jumps to 100% in a single step. Both hat and spectre exhibit identical transition behavior.

#### Why the transition is sharp

The substitution is **recursively self-similar**: the local structure within any finite subtree is fully determined by the subtree root's type, independent of what's above it in the hierarchy. Two tiles from different seeds but with the same ancestor chain up to level k are locally indistinguishable at radius k. Only when the chain reaches the seed does the difference become visible.

The BFS-based type signature makes this even starker: with sibling adjacency, a tile can determine its immediate parent type at radius 1, but **cannot determine any higher ancestor** regardless of radius. The adjacency graph is disconnected at supertile boundaries, creating an absolute information barrier.

#### Ancestry determination (hat, depth 3, seed H)

| Level | Relation | Determined | Fraction |
|-------|----------|------------|----------|
| 1 | Parent | 442/442 | 100% at radius 1 |
| 2 | Grandparent | 3/442 | 0.7% — nearly all undetermined |
| 3 | Seed | 442/442 | 100% (trivially, only one seed type) |

This demonstrates the BFS information barrier: sibling adjacency reveals parent type but nothing higher.

#### Mutual information reveals partial structure

While distinguishing advantage is 0 for radii < depth, **mutual information** is nonzero starting at radius 1-2. The *distribution* of tiles across signatures varies by seed even when no individual signature is unique. A Bayesian observer gains partial information before the gap closes; a deterministic algorithm cannot.

#### Connection to proximity gaps

The tiling gap is **dual** to the proximity gap in FRI/coding theory:
- **Proximity gap**: globally invalid → locally detectable (local tests are powerful)
- **Tiling gap**: globally different → locally undetectable until threshold (local observations are weak)

Both exhibit sharp transitions. The proximity gap makes the IOP verifier efficient; the tiling gap characterizes the cost of identification.

#### Implications

The gap is **not suitable as a smooth hardness assumption** like LWE. It's a binary property: either you can see the seed (trivially easy) or you can't (information-theoretically impossible). More like a one-time pad than a lattice problem — unconditional but non-tunable.

For the IOP construction, this is ideal: the hierarchical commitment is unconditionally binding within any finite radius, and efficiency comes from the proximity gap on the proof side.

---

### Local-to-Global Gap Closes at Radius = Depth (#16)

The local-to-global gap closing radius equals the hierarchy depth exactly, for both hat and spectre across all tested depths.

| System | depth 3 | depth 4 | depth 5 | depth 6 |
|--------|---------|---------|---------|---------|
| Hat | closes r=3 | closes r=4 | closes r=5 | closes r=6 |
| Spectre | closes r=3 | closes r=4 | closes r=5 | closes r=6 |

The pattern holds without exception: gap closing radius = depth.

**Interpretation**: to verify that a tile is globally consistent with the full hierarchy, you must propagate the check upward through all `depth` levels of the substitution hierarchy. At each level, the local neighborhood of valid context expands by one "supertile radius." A neighborhood of radius `depth` is exactly the smallest window that reaches the root — no smaller window can guarantee global consistency, and radius `depth` is always sufficient.

**Consequence for IOP**: this confirms that the query radius for the tiling IOP scales linearly with depth, not super-linearly. The IOP's depth × queries complexity matches the O(depth) closing radius.

---

### Cross-Supertile Adjacency Resolves Level-2 Ancestry That Sibling Adjacency Cannot (#13)

The local-to-global gap analysis was re-run with two adjacency models:
- **Full sibling**: tiles adjacent iff they share the same direct parent (supertile)
- **Cross-supertile**: tiles adjacent iff same parent (sibling) **or** their parents are inflation-adjacent within a shared grandparent supertile

The cross-supertile model reflects physical geometric adjacency: tiles on either side of a supertile boundary are connected.

#### Hat (depth 3, max_radius 6)

| Level | Sibling max_r | Cross max_r | Change |
|-------|--------------|-------------|--------|
| 1 (parent) | 1 | 1 | same |
| 2 (grandparent) | ? (undetermined at r=6) | 4 | **resolved** |
| 3 (root = seed type) | 0 | 0 | same |

**Full sibling**: 442/442 determined for level 1 and 3; only 3/442 determined for level 2 within max_radius=6. The remaining tiles cannot be identified by sibling-only BFS.

**Cross-supertile**: 442/442 determined for all three levels, including level 2 at max_radius=4.

#### Spectre (depth 3, max_radius 6)

| Level | Sibling max_r | Cross max_r | Change |
|-------|--------------|-------------|--------|
| 1 (parent) | 1 | ? (undetermined) | reversed |
| 2 (grandparent) | ? (undetermined) | 1 | **resolved** |
| 3 (root = seed type) | 0 | 0 | same |

An unexpected **inversion**: with sibling adjacency, level 1 is determined (r=1) but level 2 is not. With cross-supertile adjacency, level 2 is determined (r=1) but level 1 is not. This arises because spectre's 2-type system (Spectre/Mystic) is symmetric: when you can see across supertile boundaries you can identify the grandparent, but the added cross-supertile connectivity makes level-1 parents confusable between Spectre and Mystic supertiles.

#### Cross-seed distinguishing (both systems, both modes)

Cross-seed distinguishing uses hierarchical signature (ancestor chain depth), independent of adjacency. For both hat and spectre, the gap closes at hierarchical radius = depth = 3, regardless of adjacency model. The adjacency model only affects the BFS-based ancestry determination, not the hierarchical distinguishing.

#### Key finding

**Cross-supertile adjacency breaks the level-2 determination bottleneck.** With sibling-only adjacency, a tile's grandparent type is unresolvable within the tested radius for most tiles. Adding cross-supertile connections (inflation-adjacent neighboring supertiles) provides the missing context to determine the level-2 ancestor. The geometric boundary information that sibling adjacency lacks is exactly what is needed to resolve ambiguous ancestry.

---

### Mutual Information Saturates After Level 1 for Hat, Immediately for Spectre (#15)

How much does knowing an ancestor's type reduce uncertainty about a base tile's type? We compute H(base | ancestor at level k) via M^k row distributions (M = substitution matrix), then compare to the unconditional entropy H(base).

**Hat (4 types: H/T/P/F):**

Unconditional entropy: **1.762 bits** (stationary: H=50.0%, T=25.0%, P=12.5%, F=12.5%)

| Ancestor level | H(base \| ancestor) | MI gain (bits) | Best accuracy |
|---------------|---------------------|----------------|---------------|
| 1 (parent) | 1.548 | **0.214** | 43.4% |
| 2 (grandparent) | 1.762 | 0.000 | 38.2% |
| 3 | 1.768 | −0.006 | 38.2% |
| 4 | 1.768 | −0.006 | 38.2% |
| 5 | 1.768 | −0.006 | 38.2% |
| 6 | 1.768 | −0.006 | 38.2% |

**Spectre (2 types: Spectre/Mystic):**

Unconditional entropy: **0.549 bits** (stationary: Spectre=87.3%, Mystic=12.7%)

| Ancestor level | H(base \| ancestor) | MI gain (bits) | Best accuracy |
|---------------|---------------------|----------------|---------------|
| 1 (parent) | 0.549 | 0.000 | 87.3% |
| 2 (grandparent) | 0.549 | 0.000 | 87.3% |
| 3–6 | 0.549 | 0.000 | 87.3% |

#### Key findings

**Hat**: The immediate parent is the only informative ancestor (+0.214 bits, lifting accuracy from 38.2% to 43.4%). Grandparent and all higher ancestors provide zero marginal information — they are indistinguishable from the stationary distribution. Exception: a T'-parent means the base tile is always H (entropy = 0 bits, 100% accuracy), but T' is itself rare.

**Spectre**: No ancestor level provides ANY useful information. The base-tile distribution is already at stationary from the very first level. This follows from spectre's two-type symmetric structure: the substitution rule propagates identity quickly to the stationary distribution.

**Why MI saturates**: The substitution matrix M^k converges to the outer product of stationary×ones as k grows. After one multiplication (k=1 for hat, k=0 for spectre), the row distributions are already near-stationary, so higher ancestors carry no signal above the unconditional entropy.

---

### Joint Ancestor Knowledge Partially Restores Reconstruction Accuracy (#14)

Knowing BOTH a grandparent and parent simultaneously is more informative than either alone. We compute H(base | level-2 ancestor AND level-1 ancestor) jointly.

**Hat:**

| Scenario | H(base | ...) | Notes |
|---------|--------------|-------|
| No ancestry | 1.762 bits | Unconditional entropy |
| Level-2 ancestor only | 1.768 bits | No improvement (grandparent alone is noise) |
| Level-1 ancestor only | 1.548 bits | Parent alone: +0.214 bits MI |
| Level-2 AND level-1 | **0.224 bits** | Joint: **+1.544 bits MI** over grandparent alone |

The dramatic jump (from 1.768→0.224 bits) shows that knowing the parent in addition to the grandparent is hugely informative — even though the grandparent alone is useless. The parent provides strong conditioning; adding the grandparent context further constrains which inflations are compatible.

**Spectre:**

| Scenario | H(base | ...) | Notes |
|---------|--------------|-------|
| No ancestry | 0.549 bits | Unconditional entropy |
| Level-2 ancestor only | 0.549 bits | Grandparent alone: no improvement |
| Level-1 ancestor only | 0.549 bits | Parent alone: no improvement |
| Level-2 AND level-1 | **0.070 bits** | Joint: **+0.479 bits MI** over grandparent alone |

Even for spectre — where individual ancestor levels provide zero information — joint (level-2, level-1) knowledge still reduces entropy substantially. The joint distribution over compatible inflation chains narrows the base type more than either marginal can.

#### Reconstruction implications

- **Partial ancestry is not worthless**: even though grandparent type alone is random noise for base prediction, combining grandparent with parent provides a strong constraint on compatible inflation paths.
- **Tree-path context is the right query**: a tiling IOP that queries a ROOT→LEAF path carries more information per query than one that queries unrelated ancestor levels independently.
- **Hat vs Spectre**: hat has larger absolute MI values because its stationary distribution is more uniform (higher base entropy). Spectre's concentration at Spectre=87.3% means there's little entropy to reduce in the first place.

---

### Minimum Useful Patch Size for Recovery (#19)

Recovery succeeds perfectly (all erased tiles matched) only for holes of at most 3 tiles (radius ≤ 1.5). Beyond that threshold, recovery becomes partial.

#### Results (levels=3, hat H-patch, 442 total tiles)

| radius | erased | matched | unmatched | match rate |
|--------|--------|---------|-----------|-----------|
| 0.5 | 1 | 1 | 0 | 100% ✓ |
| 1.0 | 3 | 3 | 0 | 100% ✓ |
| 1.5 | 3 | 3 | 0 | 100% ✓ |
| 2.0 | 9 | 3 | 6 | 33% ✗ |
| 3.0 | 17 | 3 | 14 | 18% ✗ |
| 4.0 | 27 | 3 | 24 | 11% ✗ |
| 5.0 | 43 | 3 | 40 | 7% ✗ |

**The threshold is at 3 erased tiles.** The recovery algorithm (deflation-based) reliably reconstructs up to 3 contiguous missing tiles. At 9 or more, the hole is too large for the local deflation context to fully close.

**Depth independence**: the match rate does not depend on the `levels` parameter at the same radius — the recovery is determined by the geometric hole size, not the total patch size. The context (99%+ of tiles remaining) is always sufficient; the limit is the algorithm's local search radius.

**Extra recovered tiles**: the deflation-based recovery always regenerates a large superpatch (251 tiles at 3 levels of deflation). Only 1–3 of these overlap with the original hole positions. The rest are "bonus" tiles outside the erased region.

---

## Sibling Swap Vulnerability

Throughout this cluster: hat has 1 valid swap (P'↔F') and spectre has 1 (Mystic'↔Spectre'). Established in [#17](#spectre-vs-hat-erasure-resilience-17) and predicted by [#18](#substitution-matrix-rows-predict-confusable-pairs-18).

### Minimum Modification Distance (#26)

The minimum number of tile moves needed to transform one valid tiling hierarchy into a different valid tiling hierarchy. Specifically: how many tile parent-attribution changes suffice to produce an alternative globally-consistent hierarchy?

#### Setup

A "modification" is reassigning 1 tile from one supertile's children to another supertile's children (the tile's type is unchanged). A confusable pair (A, B) exists when B = A + 1 child of `differing_type`. Moving that 1 tile from B to A converts A→B and B→A simultaneously.

Base-tile type-change distance was also analyzed: can changing a base tile's type (e.g., H→F) produce a valid alternative hierarchy?

#### Results (depth 3)

| Metric | Hat | Spectre |
|--------|-----|---------|
| Confusable pair | P' ↔ F' (differ by 1 F child) | Mystic' ↔ Spectre' (differ by 1 Spectre child) |
| P' children / F' children | 5 / 6 | — |
| Mystic' children / Spectre' children | — | 7 / 8 |
| Base-tile type-change distance | **∞** (child count determines type uniquely) | **∞** (child count determines type uniquely) |
| Parent-attribution distance | **1** | **1** |
| Cascade cost at level 1 | 0 | 0 |
| Cascade cost at level 2 | 0 | 0 |
| Sibling pair instances (level 1) | 42 | 55 |
| Sibling pair instances (level 2) | 9 | 7 |
| Total instances | 51 | 62 |

#### Why base-tile type changes cannot work

Supertile types are uniquely determined by **child count**, not just composition multiset:
- P' always has exactly 5 children; F' always has exactly 6. No type change to existing children can add or remove a child.
- Mystic' always has 7 children; Spectre' always has 8. Same argument.

Therefore the base-tile type-change distance is infinite for both systems.

#### Why cascade cost is zero for sibling swaps

_The proof that cascade cost = 0 for sibling swaps is in [#35](#non-sibling-modification-cost-landscape-35). Summary: swapping two siblings preserves the parent's child-type multiset, so no cascade propagates upward._

#### Conclusion: hypothesis falsified

The issue hypothesized that spectre's dense cascade structure would force modification distance > 1. This is false. **Both hat and spectre have minimum modification distance 1** (1 parent-attribution change, 0 cascade cost), exploiting their respective confusable pairs.

The erasure resilience advantage measured in #17 (spectre survives more random erasures) is irrelevant for *adversarial* modifications. A coordinated adversary does not need to erase tiles; they need only identify any sibling confusable pair and move 1 tile. Both systems provide 51–62 such opportunities at depth 3.

The modification distance is determined solely by the existence of a confusable pair and the presence of sibling instances in the hierarchy — not by the dependency graph density.

---

### Geometric Modification Distance: Spectre Has Infinite, Hat Has 1 (#30)

The combinatorial modification distance analysis (#26) showed that both hat and spectre have parent-attribution distance = 1. Issue #29 asked whether imposing a geometric constraint changes this: the re-attributed tile must be **at the physical boundary** between the two supertiles, not just any sibling tile.

Only **boundary children** — inflation children not assigned to any supertile — can occupy shared boundaries between adjacent supertiles. The question reduces to: does any boundary child have the same type as the `differing_type` of a confusable pair?

#### Results (single inflation step, no depth parameter needed)

| Metric | Hat | Spectre |
|--------|-----|---------|
| Total inflation children | 29 | 15 |
| Boundary children (unassigned) | **7** | **0** |
| Confusable pair | P' ↔ F' (differ by 1 F child) | Mystic' ↔ Spectre' (differ by 1 Spectre child) |
| F-type boundary children | **2** (child #14, child #17) | N/A |
| Spectre-type boundary children | N/A | **0** |
| Geometric modification distance | **1** | **∞** |

#### How hat achieves geometric distance 1

Hat's 29 inflation children include 7 boundary tiles not owned by any supertile (H', T', P', F'). Among these 7:
- Children #14 and #17 are **F-type**.
- The confusable pair P' ↔ F' differs by exactly 1 F child.
- Therefore an adversary can re-attribute one of these F-type boundary tiles from a P'-supertile's "sphere" to an adjacent F'-supertile's "sphere" (or vice versa), converting the P' to F' and the F' to P' — at a cost of 1 boundary attribution change.

#### Why spectre has infinite geometric distance

Spectre's 15 inflation children are **all assigned** to Spectre' or Mystic' supertiles — there are no boundary tiles. Without any shared boundary tile at a Mystic'–Spectre' junction, no geometric attribution change is possible. Even though the combinatorial (parent-attribution) distance is 1, it requires a tile physically *inside* one supertile, which cannot be at the boundary.

#### Interpretation

The geometric constraint reveals a strict hierarchy of adversarial models:

| Model | Hat | Spectre |
|-------|-----|---------|
| Combinatorial (attribution only) | 1 | 1 |
| Geometric (boundary tiles only) | 1 | **∞** |

Spectre is **strictly more resistant** to geometrically-constrained adversaries. Hat's 7 boundary children — a structural "glue" artifact of its inflation rule — are its geometric weak point. Spectre eliminated this artifact: every inflation child is fully owned, leaving no ambiguous tile at shared boundaries.

This is a concrete separation: any adversary who must move a physically-present tile (rather than relabel an abstract child index) cannot attack spectre at cost 1. Hat remains vulnerable.

---

### Swap Opportunity Scaling with Depth (#29)

The number of sibling confusable-pair instances grows exponentially with hierarchy depth at a rate matching the dominant eigenvalue of the substitution matrix.

#### Hat (P'↔F' pair, seed=H)

| Depth | Level 1 | Level 2 | Level 3 | Level 4 | Level 5 | Total |
|-------|---------|---------|---------|---------|---------|-------|
| 2     | 9       | —       | —       | —       | —       | 9     |
| 3     | 42      | 9       | —       | —       | —       | 51    |
| 4     | 300     | 42      | 9       | —       | —       | 351   |
| 5     | 2,037   | 300     | 42      | 9       | —       | 2,388 |
| 6     | 13,974  | 2,037   | 300     | 42      | 9       | 16,362 |

Level-1 growth ratio: 300/42 ≈ 7.14, 2037/300 ≈ 6.79, 13974/2037 ≈ **6.86** → converges to the hat dominant eigenvalue (~6.86).

#### Spectre (Mystic'↔Spectre' pair, seed=Spectre)

| Depth | Level 1 | Level 2 | Level 3 | Level 4 | Level 5 | Total  |
|-------|---------|---------|---------|---------|---------|--------|
| 2     | 7       | —       | —       | —       | —       | 7      |
| 3     | 55      | 7       | —       | —       | —       | 62     |
| 4     | 433     | 55      | 7       | —       | —       | 495    |
| 5     | 3,409   | 433     | 55      | 7       | —       | 3,904  |
| 6     | 26,839  | 3,409   | 433     | 55      | 7       | 30,743 |

Level-1 growth ratio: 433/55 ≈ 7.87, 3409/433 ≈ 7.87, 26839/3409 ≈ **7.87** → converges to the spectre dominant eigenvalue (~7.87).

#### Key observations

**Telescoping structure.** The count at level k for depth d equals the count at level k for any depth d' > k. The per-level sequence is fixed; deeper hierarchies simply prepend a new, larger level-1 count. This means the "opportunity surface" is determined entirely by the substitution matrix, not by the total hierarchy depth.

**Eigenvalue-rate growth.** Both systems' swap counts grow at the dominant substitution eigenvalue rate. This makes structural sense: the number of confusable sibling pairs at level k is proportional to the number of supertile pairs at level k+1, which is proportional to the dominant eigenvector component scaled by λ^(depth−k).

**Modification distance is depth-independent.** Despite swap counts growing exponentially (from 9 at depth 2 to 16,362 at depth 6 for hat), the minimum modification distance remains 1 at all depths. Increasing depth adds attack surface, never hardens it.

**Spectre has more opportunities per level than hat.** At level 1, spectre has ~55% more instances than hat at depth 3 (55 vs 42) and ~92% more at depth 4 (433 vs 300). This reflects spectre's 8-child Spectre' supertile producing more sibling-pair opportunities per parent than hat's 5/6-child P'/F'.

---

### Non-Sibling Modification Cost Landscape (#35)

Are sibling swaps the unique cost-1 modifications? Yes. The modification distance landscape is bimodal: cost 1 for sibling swaps, cost ≥ 2 for everything else.

#### Proof that non-sibling modifications cost ≥ 2

A cost-1 modification moves one tile from supertile A to supertile B. Two cases:

**Case 1: A and B are siblings (same parent P).**
- A loses one child of `differing_type` → A's composition changes to B's old composition → A is relabeled B.
- B gains one child → B is relabeled A.
- P's child-type multiset: had one A and one B, now has one B and one A → **unchanged**. Cascade cost = 0. Total cost = 1.
- This is the sibling swap. Valid when A and B form a confusable pair.

**Case 2: A and B are not siblings (different parents P_A and P_B).**
- A's type changes (it lost a child) → P_A's child-type multiset changes (one fewer of A's old type, one more of A's new type) → P_A's composition changes → P_A's type may change → cascade cost ≥ 1. Total cost ≥ 2.

Therefore, the only cost-1 zero-cascade modifications are sibling swaps between confusable pairs. All other modifications cost at least 2.

#### Implications for the modification distance spectrum

| Modification type | Min cost | Min cascade | Example |
|-------------------|----------|-------------|---------|
| Sibling swap (confusable pair) | **1** | **0** | P'↔F' swap between siblings |
| Two independent sibling swaps | **2** | **0** | Two separate P'↔F' pairs swapped |
| Non-sibling type move | **2** | **≥1** | Move tile between non-adjacent supertiles |
| Root modification | **≥depth** | **depth** | Change the seed type propagates all the way down |

The landscape is gapped: there is no modification with cost strictly between 1 and 2. The set of reachable valid hierarchies from any given H is partitioned into: H itself (cost 0), and hierarchies at distance 1 (all sibling-swap variants, exponentially many of them), with a gap before any distance-2 modifications.

---

### Swap Density Convergence (#36)

The fraction of sibling pairs that are confusable (swap density) is a structural constant determined by the substitution rules — for hat it is exactly constant at all depths; for spectre it converges to a value determined by the dominant eigenvector.

#### Hat: exactly 1/5 at every level and every depth

For each supertile type in hat, the ratio (swap pairs from this parent) / (total sibling pairs from this parent) is:

| Parent type | Children (n) | P'×F' swap pairs | Total pairs C(n,2) | Density |
|-------------|-------------|-------------------|---------------------|---------|
| H' | 10 | 3×3 = 9 | 45 | **1/5** |
| T' | 1 | 0 | 0 | — |
| P' | 5 | 1×2 = 2 | 10 | **1/5** |
| F' | 6 | 1×3 = 3 | 15 | **1/5** |

Every non-trivial supertile type contributes exactly 20% swap-vulnerable pairs. Since the density is identical for all contributing types, the overall density is exactly 1/5 regardless of the mix of parent types at any level. This holds at **every level and every depth** — it is depth-independent and purely a function of the substitution rules.

Verified computationally: all levels at all depths 2–6 give exactly 0.2000.

#### Spectre: converges to (5+√15)/35 ≈ 25.35%

Spectre's two types have different local densities:

| Parent type | Children (n) | S×M swap pairs | Total pairs | Density |
|-------------|-------------|----------------|-------------|---------|
| Spectre' | 8 | 7×1 = 7 | 28 | 25.00% |
| Mystic' | 7 | 6×1 = 6 | 21 | 28.57% |

The overall density at each level depends on the S':M' ratio at the level above. This ratio converges to the left PF eigenvector ratio **(√15+3):1 ≈ 6.873:1** (the left eigenvector is (S:M) = (6:√15−3), so S/M = 6/(√15−3) = √15+3). Substituting r = √15+3:

**f\* = (7r+6)/(28r+21) = (7√15+27)/(28√15+105) = (5+√15)/35 ≈ 25.35%**

(Rationalization: multiply by (28√15−105)/(28√15−105); denominator = 784×15−105² = 735; numerator = 105+21√15 = 21(5+√15); so f\* = 21(5+√15)/735 = (5+√15)/35.)

Observed convergence: depth-2 level-1 = 25.00%, depth-3 level-1 = 25.35%, depth-4+ level-1 = 25.35% (converged to 4 decimal places — matches exact form).

_Note: an earlier version of this section incorrectly stated the eigenvector ratio as (3+2√3):1 ≈ 6.464 (Q(√3)). The correct ratio is (√15+3):1 ≈ 6.873 (Q(√15)). The two are numerically close (~0.4 apart) which is why the approximate 25.37% figure was plausible, but the exact closed form is (5+√15)/35, not (27+14√3)/(105+56√3). Corrected by CAS #54 (cas/54b_spectre_swap_exact.gp)._

#### Implication

Neither system's swap density decreases with depth. Hat is locked at exactly 20%; spectre converges immediately to ~25.4%. Increasing depth does not reduce the fraction of sibling pairs that are confusable. The defense against sibling swaps must be structural (canonicalization, issue #33), not parametric.

---

### Algebraic IOP Is Blind to Sibling Swaps (#31)

The tiling IOP accepts any valid hierarchy, including hierarchies produced by sibling swaps. Two distinct hierarchies H and H' — where H' is obtained by swapping a P'/F' sibling pair and reassigning one child — both produce valid, accepted proofs. The IOP cannot distinguish between them.

#### Test result

`iop_accepts_sibling_swapped_hierarchy` passes: the verifier accepts fresh proofs for both the original hierarchy and the sibling-swapped version. The two hierarchies differ at level 1 (different tile type assignments), confirming the swap genuinely changes the hierarchy.

#### Why the IOP cannot detect this

The IOP's soundness guarantee is: **for a given commitment, the prover cannot cheat**. It does NOT guarantee uniqueness of the committed hierarchy. The IOP verifies:
1. Merkle proofs for each queried supertile and its children
2. That child type counts match the claimed supertile composition
3. That the fold (linear combination of children by challenge) equals the committed supertile value

All three checks hold for H'. The swapped hierarchy is genuinely valid:
- H' has the same base values (level 0 unchanged)
- At level 1, A now has F'-composition children and B has P'-composition children
- Fold values at levels 1 and above are recomputed from scratch for H'
- All Merkle trees are rebuilt for H'

The prover generates a completely honest proof for H'. No check fails. **The IOP cannot enforce that a given base-level commitment corresponds to exactly one supertile labeling.**

#### Implication

The IOP proves "there exists a valid hierarchy consistent with this commitment." It does not prove "this is the unique canonical hierarchy for the underlying tiling." For applications that require canonical labeling (e.g., proving a specific spatial layout, or that two parties committed to the same hierarchy), the IOP must be augmented with a uniqueness argument. The geometric modification distance finding (#30) suggests spectre is harder to attack geometrically, but the algebraic IOP remains blind to algebraic swaps for both systems.

_See also [#33](#iop-canonical-form-defense-zero-cost-enforcement-33): the canonical form check eliminates this blindness at zero proof-size cost._

---

### IOP Query Coverage of Swap-Vulnerable Positions (#34)

A "swap-vulnerable" tile is one of P'- or F'-type (hat) or Spectre'/Mystic'-type (spectre) that has at least one confusable sibling. The probability that a random IOP query hits such a tile determines how often the verifier "sees" a swap if one occurred.

#### Hat: ~61.8% of tiles are swap-vulnerable

In the hat system, every P'- and F'-type tile has at least one confusable sibling (because every parent type that produces P' children also produces F' children, and vice versa). Only H'-type children of T'-type supertiles are non-vulnerable — but T' has only one H'-type child and no P'/F' children. So the vulnerable fraction equals the P'+F' fraction of all tiles.

| Depth | Level | Total tiles | Vulnerable | Fraction | Queries for 99% |
|-------|-------|-------------|------------|----------|-----------------|
| 3 | 1 | 64 | 39 | 60.9% | **5** |
| 3 | 2 | 10 | 6 | 60.0% | **5** |
| 4 | 1 | 442 | 273 | 61.8% | **5** |
| 5 | 1 | 3025 | 1869 | 61.8% | **5** |
| 6 | 1 | 20737 | 12816 | 61.8% | **5** |

Converges to ~61.8% (the P'+F' fraction of the dominant eigenvector). **5 queries per level give >99% probability of hitting a swap-vulnerable tile.**

#### Spectre: 100% of tiles are swap-vulnerable

Every Spectre'- and Mystic'-type tile has at least one sibling of the opposite type, because both Spectre' (7S+1M) and Mystic' (6S+1M) parents produce at least one child of each type. **Every query hits a swap-vulnerable tile.** A single query per level gives 100% coverage.

#### The IOP query count is already more than sufficient for coverage

With 8 queries per level (the default), the probability of missing ALL swap-vulnerable tiles across all levels of a depth-3 hierarchy is < 10⁻⁶. The IOP's existing query budget vastly exceeds what is needed to "see" the swapped positions. The problem is not query coverage — it is that seeing the swapped tile does not help, because the verifier accepts both hierarchies as valid. Coverage is necessary but not sufficient; a canonical form check is also needed.

_See also [#31](#algebraic-iop-is-blind-to-sibling-swaps-31): query coverage is a prerequisite for detection, but the IOP is blind to valid swaps regardless of coverage. Fix: [#33](#iop-canonical-form-defense-zero-cost-enforcement-33)._

---

### Steganographic Bit Channel in Sibling-Swap Ambiguity (#27)

Each sibling confusable pair (P'↔F' for hat, Spectre'↔Mystic' for spectre) is a 1-bit covert channel: canonical labeling encodes 0, swapped labeling encodes 1. The channel is undetectable by the pre-#33 IOP and completely closed by the #33 canonical check.

#### Channel capacity (depth 4, seed H/Spectre)

| System | Swap instances | Capacity (bits) | Capacity (bytes) | Growth rate per depth |
|--------|---------------|-----------------|------------------|-----------------------|
| Hat | 351 | 351 | 43 | ~6.9× (≈ λ_hat = 6.86) |
| Spectre | 495 | 495 | 61 | ~8.0× (≈ λ_spectre = 7.87) |

**Capacity by level (hat, depth 4):**

| Level | Instances | Bits |
|-------|-----------|------|
| 1 (base supertiles) | 300 | 300 |
| 2 | 42 | 42 |
| 3 | 9 | 9 |
| Total | 351 | 351 |

#### Encode/decode demonstration

Message `"hello"` (5 bytes = 40 bits) encoded in a depth-4 hat hierarchy:
- 40/351 = 11% of capacity used
- 21 swap operations applied (bits set to 1)
- Decoded: `"hello"` — match ✓

#### Detectability

| Verifier | Detection |
|----------|-----------|
| Pre-#33 IOP (composition check only) | **Undetectable** — all swap variants pass as valid |
| Post-#33 IOP (canonical check added) | **Fully detectable** — any swapped instance fails position check; 0 bits survive |

#### Why capacity scales at λ

Each depth level adds a factor of λ (dominant substitution eigenvalue) more sibling pairs, because the number of same-parent P'/F' pairs grows proportionally to the tile count, which grows at λ per level. The channel capacity doubles roughly every log₂(λ) ≈ 2.8 depth levels.

#### Implication

The sibling-swap ambiguity creates a covert channel with capacity growing exponentially in hierarchy depth. The #33 canonical check completely eliminates this channel: any stego bit is immediately detectable as a child-type mismatch at the corresponding hierarchy node.

---

## IOP and Proof Construction

### Tiling IOP Performance (#9)

Concrete measurements for the hat-tiling-based interactive oracle proof at depth 4 (3025 base tiles, 5 hierarchy levels):

| Metric | Value |
|--------|-------|
| Hierarchy build | 44 µs |
| Prove time | 1.4 ms |
| Verify time | 263 µs |
| Commitments | 5 (one per level) |
| Merkle openings | 280 (8 queries × 4 rounds × ~8.75 children) |
| Est. proof size | ~96 KB |
| Result | ACCEPTED |

The prove/verify ratio is ~5.3x, and both are sub-millisecond at this scale. The proof size is dominated by Merkle openings (280 × ~320 bytes each), not commitments.

---

### Spectre vs Hat IOP Soundness (#21)

The IOP crate was generalized from hat-specific (`MetatileType`) to system-generic (`usize` type indices), enabling `prove Spectre -S spectre` to run alongside hat. Results at 8 queries per round:

#### Proof size and openings by depth

| Depth | System | Base tiles | Openings | Proof size | Prove | Verify |
|-------|--------|------------|----------|------------|-------|--------|
| 1 | Hat | 10 | 88 | ~30.3 KB | 17µs | 101µs |
| 1 | Spectre | 8 | 72 | ~24.8 KB | 10µs | 53µs |
| 2 | Hat | 64 | 143 | ~49.2 KB | 43µs | 140µs |
| 2 | Spectre | 63 | 143 | ~49.2 KB | 45µs | 144µs |
| 3 | Hat | 442 | 209 | ~72.0 KB | 232µs | 252µs |
| 3 | Spectre | 496 | 214 | ~73.7 KB | 264µs | 278µs |
| 4 | Hat | 3,025 | 281 | ~96.8 KB | 1.07ms | 284µs |
| 4 | Spectre | 3,905 | 284 | ~97.8 KB | 1.13ms | 266µs |

All proofs verified. Proof sizes are within 1-2% of each other at every depth.

#### Average children per query

| Depth | Hat avg | Spectre avg |
|-------|---------|-------------|
| 1 | 10.0 | 8.0 |
| 2 | 7.94 | 7.94 |
| 3 | 7.71 | 7.92 |
| 4 | 7.78 | 7.88 |

At depth 1, hat always queries the H' supertile (10 children); spectre queries Spectre' (8 children). At deeper levels, hat's 4-type mix (H'=10, T'=1, P'=5, F'=6, weighted by Perron eigenvector) pulls the average below spectre's uniform 7-8.

#### Structural analysis: why the soundness question was malformed

The original hypothesis was that spectre's "no anchor" structure would translate to stronger IOP soundness than hat's T'-anchored structure. This was wrong about the relevant notion of soundness.

**This IOP proves algebraic consistency of folded values, not semantic tiling validity.** The prover commits to field values at each level, and the verifier checks that committed values fold correctly under the Fiat-Shamir challenges. Soundness — the bound on cheating probability — depends on:

1. The binding property of the Merkle commitments (Blake3 collision resistance)
2. The uniformity of the folding challenges (Fiat-Shamir randomness)

Neither of these depends on tiling structure. The confusability of supertile types (P'↔F' in hat, Mystic'↔Spectre' in spectre) is irrelevant: even if type labels are ambiguous, the prover cannot change committed field values without finding Blake3 preimages.

**The T' anchor has no soundness effect in this construction.** Hat's 1-child T' type means T'-queries require only 2 hash openings (1 supertile + 1 child), while spectre queries always require 8-9 openings. This makes hat queries cheaper, but does not change the algebraic soundness bound. A cheating prover cannot exploit the cheap T' position because changing a committed T'-child value would require a hash collision.

**Where tiling structure would matter.** If the IOP were extended to prove *semantic validity* — that the committed hierarchy is actually a valid tiling (correct tile shapes, consistent adjacencies, chirality constraints) — then spectre's no-reflection constraint and anchor-free uniformity would become relevant. Spectre's geometric rigidity (no reflected tiles) means there is one fewer degree of freedom for a cheating prover to exploit when constructing a semantically plausible fake hierarchy. Hat's chirality freedom provides the prover with local choices that do not violate the algebraic folding check but do violate geometric tiling validity.

This is an open direction: building an IOP that also commits to the *geometric* placement of tiles, not just their field values, and where spectre's rigidity provides measurable soundness improvement.

---

### IOP Proof Size Scaling Curve (#20)

Measured with 8 queries per round, BLS12-381 field (32-byte field elements, 32-byte Merkle hashes).

#### Hat system

| depth | base_tiles | proof_KB | commit_B | challenge_B | query_B | max_path | openings |
|-------|-----------|---------|---------|------------|--------|---------|---------|
| 1 | 10 | 14.9 | 64 | 128 | 15,040 | 4 | 88 |
| 2 | 64 | 27.8 | 96 | 256 | 28,040 | 6 | 143 |
| 3 | 442 | 49.4 | 128 | 384 | 50,040 | 9 | 209 |
| 4 | 3,025 | 79.1 | 160 | 512 | 80,248 | 12 | 281 |
| 5 | 20,737 | 99.9 | 192 | 640 | 101,408 | 15 | 320 |

#### Spectre system

| depth | base_tiles | proof_KB | commit_B | challenge_B | query_B | max_path | openings |
|-------|-----------|---------|---------|------------|--------|---------|---------|
| 1 | 8 | 10.0 | 64 | 64 | 10,048 | 3 | 72 |
| 2 | 63 | 26.4 | 96 | 128 | 26,760 | 6 | 143 |
| 3 | 496 | 49.5 | 128 | 192 | 50,288 | 9 | 214 |
| 4 | 3,905 | 79.0 | 160 | 256 | 80,480 | 12 | 284 |
| 5 | 30,744 | 116.4 | 192 | 320 | 118,672 | 15 | 358 |

#### Scaling analysis

The query_B component dominates (>99% of proof size). Commitments and challenges are negligible.

**Max Merkle path depth** grows by ~3 bits per depth level (consistent with branching factor ~5.5–7.5 → log₂(5.5)≈2.5 to log₂(7.5)≈2.9 bits per level).

**Proof size growth per depth level** is approximately linear: each added level contributes the same marginal cost because:
1. It adds one new query round (small — root level has 1 tile)
2. All existing rounds' Merkle paths grow by ~3 hashes (the new base level is larger)

**Hat vs spectre diverge at depth 5**: hat plateaus slightly below 100 KB while spectre grows to 116 KB. Spectre's higher branching factor (7.5 avg vs 5.5 avg) means deeper Merkle paths and more children per opening.

**Proof size formula**: `proof_bytes ≈ Q × ∑_{k=1}^{d} (1 + avg_children_k) × (field_el + merkle_path_k × hash_size)` where `merkle_path_k ≈ ceil(log₂(tiles_at_level_{k-1}))` and `tiles_at_level_k ≈ λ^(d-k)` (λ = dominant eigenvalue).

---

### IOP Tamper Detection Under Substitution Noise (#24)

The IOP detects arbitrary type substitutions at the base level (non-sibling type changes) whenever the tampered tile is queried. Detection scales with tamper rate and query coverage.

#### Detection rates (depth=3, 8 queries, 50 trials)

**Hat:**

| tamper rate | detected | not detected | detection rate |
|-------------|----------|-------------|----------------|
| 0% | 0/50 | 50/50 | 0.0% (baseline) |
| 1% | 19/50 | 31/50 | 38.0% |
| 2% | 38/50 | 12/50 | 76.0% |
| 5% | 46/50 | 4/50 | 92.0% |
| 10% | 50/50 | 0/50 | **100.0%** |
| 20% | 50/50 | 0/50 | 100.0% |
| 50% | 50/50 | 0/50 | 100.0% |

**Spectre:**

| tamper rate | detected | not detected | detection rate |
|-------------|----------|-------------|----------------|
| 0% | 0/50 | 50/50 | 0.0% (baseline) |
| 1% | 22/50 | 28/50 | 44.0% |
| 2% | 35/50 | 15/50 | 70.0% |
| 5% | 49/50 | 1/50 | 98.0% |
| 10% | 50/50 | 0/50 | **100.0%** |
| 20% | 50/50 | 0/50 | 100.0% |
| 50% | 50/50 | 0/50 | 100.0% |

#### Detection mechanism

The `verify_fold` function checks both (1) the multiset composition (child type counts must match the claimed parent type's expected composition) and (2) the folding value. A base-level type flip changes the child's type reported to the verifier, which changes the actual child-type counts and breaks the composition check for that parent.

**Why some trials escape detection**: with 8 queries over ~442–496 base tiles, roughly 8×avg_children ≈ 60 parent-child pairs are checked per round. At 1% tamper rate (~5 flipped tiles), the probability that at least one changed tile is checked = 1 − (1 − 5/496)^60 ≈ 46%. The observed rates (38–44%) match this analytical estimate.

**10% tamper is the saturation threshold**: at 10% tamper rate (~50 flipped tiles), detection probability per trial = 1 − (1 − 50/496)^60 > 99.99%, so all 50 trials are detected.

#### Contrast with sibling swaps (#31)

Base-level type flips (even P→F or Spectre→Mystic) ARE detected because they break composition at the parent level. The undetectable case from #31 is specifically SUPERTILE-LEVEL label swaps between sibling P'/F' pairs, where both siblings are already valid children of the same parent — the multiset is unchanged.

---

### Geometric Tile Placement: Position-as-Key Adds Only ~7% Proof Size Overhead (#28)

We analyzed the cost of extending the tiling IOP to commit to tile positions (x, y, angle) in addition to tile types.

#### Commitment design: position as key

The right design is to use the tile's spatial coordinate as the **Merkle leaf key**, with the oracle value stored at that key. This is distinct from a naive parallel Merkle tree approach:

| Design | Overhead at depth 5 | Mechanism |
|--------|-------------------|-----------|
| **Position as key** | **~7%** | Same single tree per level; +24 bytes per opened leaf |
| Parallel tree (naïve) | ~97% | Extra Merkle root + full extra path per opening |

With position-as-key:
- One Merkle tree per level — identical structure to the type-only IOP
- No-overlap guarantee comes free: two tiles can't share a key, so position collisions are impossible
- Each opening transmits position alongside value (+24 bytes per leaf) so the verifier can verify the key
- Inflation consistency check: `child_key == expected_pos(parent_key, child_slot_in_inflation)`
- Merkle path length is **unchanged** — position is the key, not additional payload

#### Proof size: type-only vs position-keyed geometric IOP (hat, 8 queries)

| Depth | Type-only | Geom IOP | Overhead | Overhead % |
|-------|-----------|----------|---------|------------|
| 1 | 4 KB | 5 KB | 1 KB | 24.7% |
| 2 | 15 KB | 17 KB | 2 KB | 14.9% |
| 3 | 31 KB | 35 KB | 3 KB | 10.7% |
| 4 | 54 KB | 58 KB | 4 KB | 8.3% |
| 5 | 82 KB | 88 KB | 5 KB | **6.8%** |

The overhead decreases with depth because the 24 bytes/opening is small relative to the growing Merkle path. At depth 5, ~6 KB of position data is carried in an 88 KB proof.

#### Why the naïve parallel-tree approach is wrong

A separate position Merkle tree alongside the value tree adds: (1) an extra root per level, and (2) an extra full-length Merkle path per opening. The result is ~97% overhead — the position data (24 bytes) is negligible, but the extra path is not. Position-as-key avoids both costs by restructuring the existing tree.

#### What position-keyed IOP checks

| Attack type | Type-only detectable? | Position-keyed detectable? |
|-------------|----------------------|---------------------------|
| Wrong child type count | Yes (composition check) | Yes |
| Base-level type flip | Yes (breaks composition) | Yes |
| Supertile label swap (P'↔F') | No (multiset unchanged) | No (geometry preserved) |
| Teleported tile (wrong position) | No | **Yes** (key mismatch) |
| Wrong spatial orientation | No | **Yes** (key mismatch) |
| Fabricated layout with valid types | No | **Yes** |
| Two tiles at same position (overlap) | No | **Yes** (key collision in Merkle tree) |

#### Inflation consistency check

For each queried parent-child pair:
1. `child_pos = parent_pos × φ² + slot_offset(child_slot)`
2. `child_angle = parent_angle + slot_rotation(child_slot)`

The verifier computes the expected child key from the parent key and slot index, then checks it matches the committed child key. No additional hash operations needed.

**Demo**: H-seed at depth 3 (442 base tiles) — all 442 pass the key-consistency check for a valid hierarchy. A teleported tile causes an immediate key mismatch.

#### Conclusion

Position-as-key geometric commitment costs ~7% proof size at depth 5. It adds spatial authenticity (no teleportation, no overlaps, correct inflation layout) with negligible verification overhead. The canonical form check ([#33](#iop-canonical-form-defense-zero-cost-enforcement-33)) remains the right fix for sibling swaps, which preserve geometry and would not be caught by position commitment.

---

### IOP Canonical Form Defense: Zero-Cost Enforcement (#33)

The IOP verifier can be upgraded to enforce canonical hierarchy labeling at zero extra proof size and O(children_per_query) extra verification cost.

#### Canonical form definition

**Inflation-order canonical**: each child's type at every parent-child edge must match the type the inflation rule specifies for that *position* in the parent's child list.

```
children[i].child_type == inflation_child_type(supertile_children(parent_type)[i])
```

The standard top-down inflation hierarchy satisfies this by construction. Any sibling swap violates it: the child at a P'-slot now has F'-type (or vice versa).

#### Inflation sequences (both systems, confirmed deterministic)

**Hat (all 4 types have deterministic sequences):**

| Parent | Children sequence |
|--------|------------------|
| H' (10 children) | H, H, H, T, P, F, P, F, P, F |
| T' (1 child) | H |
| P' (5 children) | F, H, P, H, F |
| F' (6 children) | F, H, P, H, F, F |

**Spectre (both types have deterministic sequences):**

| Parent | Children sequence |
|--------|------------------|
| Spectre' (8 children) | Spectre, Spectre, Spectre, Spectre, Spectre, Spectre, Spectre, Mystic |
| Mystic' (7 children) | Spectre, Spectre, Spectre, Spectre, Spectre, Spectre, Mystic |

#### IOP enforcement cost

| Metric | Hat | Spectre |
|--------|-----|---------|
| Extra Merkle proofs per query | **0** | **0** |
| Extra scalar comparisons per child | 1 | 1 |
| Avg children checked per query | 5.5 | 7.5 |
| Confusable-type tile fraction | 59.1% | 100.0% |

#### How it detects swaps

After a P'↔F' swap:
- Hat: the F'-labeled tile presents P'-slot children `[F, H, P, H, F]` (5 children) instead of the F'-slot sequence `[F, H, P, H, F, F]` (6 children) — position check FAILS at position 5
- Spectre: the Spectre'-labeled tile presents Mystic'-slot children (7 children) instead of the Spectre'-slot sequence (8 children) — position check FAILS at position 7

#### Relationship to existing composition check

The existing IOP composition (multiset) check verifies the right *counts* of each child type. The canonical check verifies the right *sequence*. Canonical is strictly stronger: a passed canonical check implies a passed composition check, but not vice versa.

#### Conclusion

The canonical form check eliminates the IOP blindness demonstrated in [#31](#algebraic-iop-is-blind-to-sibling-swaps-31) with no proof size increase and O(children_per_query) extra work per verification round. Both hat and spectre inflation rules are fully deterministic, making the canonical check well-defined for both systems.

---

### Sparse Merkle Tree Commitment: Compact Key Has ~5-7 Hash Overhead, Enables Non-Membership Proofs (#37)

A sparse Merkle tree (SMT) uses the leaf's key (here: tile coordinates) to determine its path through the tree. This enables *non-membership proofs*: proving that no tile exists at a given position. A standard dense Merkle tree commits to tiles by index and cannot make this statement.

Experiment: `cargo run --release -- sparse-iop --max-depth 5 --queries 8` (hat, `--system spectre` for spectre).

#### Path length comparison: dense vs SMT at the base level

**Hat system**, base tile counts and path lengths at each depth:

| Depth | Base tiles | log₂(N) | Dense path | SMT-compact | Overhead | SMT-Coxeter | SMT-SHA256 |
|-------|-----------|---------|------------|-------------|----------|-------------|------------|
| 1     | 10        | 3.32    | 4          | 10          | +6       | 132         | 256        |
| 2     | 64        | 6.00    | 6          | 12          | +6       | 132         | 256        |
| 3     | 442       | 8.79    | 9          | 16          | +7       | 132         | 256        |
| 4     | 3,025     | 11.56   | 12         | 18          | +6       | 132         | 256        |
| 5     | 20,737    | 14.34   | 15         | 20          | +5       | 132         | 256        |

All figures in hashes per opening. **SMT-compact** = compact coordinate key: 2 × ceil(1 + D × log₂(φ²)) + 4 bits (x + y + rotation:3b + reflected:1b). **SMT-Coxeter** = raw tx(64b) + ty(64b) + rotation(3b) + reflected(1b) = 132-bit fixed key. **SMT-SHA256** = hash of the CoxeterElement = 256-bit opaque key.

#### Proof size impact (8 queries, base-level tree replaced with SMT)

| Depth | Dense KB | SMT-compact KB | SMT-Coxeter KB | SMT-SHA256 KB |
|-------|----------|---------------|---------------|--------------|
| 1     | 7.6      | 16.6          | 199.6         | 385.6        |
| 2     | 21.1     | 30.1          | 210.1         | 396.1        |
| 3     | 45.1     | 55.6          | 229.6         | 415.6        |
| 4     | 78.2     | 87.2          | 258.2         | 444.2        |
| 5     | 120.2    | 127.7         | 295.7         | 481.7        |

#### Crossover analysis

Dense path grows at ≈ D × log₂(λ) ≈ 2.87D hashes (λ ≈ 7.30 growth rate per level).
SMT compact path grows at ≈ 2.78D + 6 hashes (coordinate range ≈ φ^(2D) per axis).

- **SMT compact vs dense**: overhead ≈ constant 5–7 hashes across depths 1–5. Dense grows at 2.87/depth, compact at 2.78/depth; the rates are nearly identical so the overhead is approximately constant.
- **SMT Coxeter (132 bits) vs dense**: crossover at depth > 46 (impractical). At D=5: +117 overhead.
- **SMT SHA-256 (256 bits) vs dense**: crossover at depth > 89 (very impractical). At D=5: +241 overhead.

**Spectre** shows identical compact-path results (also +5 at D=5, 30,744 base tiles) with slightly faster dense path growth (λ ≈ 7.90, crossover for Coxeter at depth > 44).

#### Non-membership proofs: the unique SMT capability

Dense Merkle trees cannot prove that a position is unoccupied. An SMT with tile coordinates as keys enables:

1. **`prove_empty(pos)`** → sibling path showing the leaf at `pos` is nil. Cost: O(key_bits) hashes — same as a membership proof.
2. **Gap-free coverage**: prover commits ALL tiles. Verifier samples random positions and demands membership or empty proofs. A prover that omits a tile cannot forge a valid empty proof for the omitted position.
3. **Tile uniqueness**: SMT structure enforces injectivity — two tiles cannot share a key.
4. **Boundary checking**: prove no tile key falls outside a claimed region.

These guarantees are impossible with a dense Merkle tree over a tile index list.

#### Conclusions

- Compact coordinate keys are the only viable SMT option for tiling IOPs (practical depths 1–10).
- The overhead is small (~5–7 hashes) and approximately constant across depths — both path lengths grow linearly at nearly the same rate.
- The Coxeter (132-bit) or SHA-256 (256-bit) fixed-width keys have crossover depths of 44+ and 86+ respectively, both impractical for this problem.
- The practical question (#37) is not proof size: it is whether non-membership proofs are needed. If gap-free coverage checking is a requirement, compact-key SMT is the right data structure with modest proof overhead.

---

### Semantic Geometric IOP: Spectre Adjacency Is Local, Hat Requires Cross-Supertile Openings (#39)

**Setup:** Code analysis of `crates/tiling/src/metatile.rs`, `systems/hat.rs`, `systems/spectre.rs`, and IOP prover/verifier.

#### Boundary children: the structural asymmetry

The core difference is encoded in `boundary_children()`:

| System | Boundary children | Count |
|--------|------------------|-------|
| Hat | Rule indices 5, 12, 13, 14, 17, 18, 19 | 7 |
| Spectre | (empty) | 0 |

The hat inflation has 29 rule indices (0–28). Of these, 22 are assigned to supertiles (H→10, T→1, P→5, F→6 children). The 7 boundary children are F-type tiles that appear at supertile interfaces — they are geometrically adjacent to tiles in two different parent supertiles.

Spectre's inflation assigns ALL child tiles cleanly within supertiles. There are no shared edges between parent supertile boundaries.

#### Current IOP verification (from prover/verifier code)

The current IOP verifies:
1. **Merkle inclusion**: supertile and each child are in the committed tree
2. **Composition**: child type counts match the supertile's template (multiset check)
3. **Fold consistency**: children fold to the claimed supertile value under random challenge

What is **not** currently verified:
- Geometric tile positions
- Canonical slot order (which child occupies which position)
- Edge adjacency between supertile boundaries

The canonical check (#33) adds slot-position type consistency at zero overhead. Position-as-key (#28) adds ~7% size overhead to commit each tile's geometric position.

#### Is edge-adjacency a local check?

**Spectre:** With canonical check + position-as-key, edge-adjacency is **fully local**.
- Opening `(parent_key, child_slot_i)` for all children of a parent reveals the full intra-supertile adjacency graph
- All 8 (or 7) children of Spectre' (or Mystic') are mutually adjacent within the supertile
- No tile appears in two parent supertiles simultaneously
- Therefore: verifying that a tile is correctly positioned relative to all its neighbors requires **only the opened parent cluster** — zero cross-supertile openings

**Hat:** Edge-adjacency is **non-local** for boundary children.
- Opening `(parent_key, child_slots)` for a hat supertile reveals only the 10 (H), 1 (T), 5 (P), or 6 (F) intra-supertile children
- The 7 boundary F-type children (rule positions 5, 12, 13, 14, 17, 18, 19) sit at supertile interfaces
- Verifying that a boundary F tile is geometrically consistent requires opening the **adjacent supertile** at the same level
- Each query that touches a boundary F child needs 1 additional cross-supertile opening

#### Fake hierarchy analysis

Can a cheating prover create a semantically invalid hierarchy that passes canonical check + position-as-key?

- **Spectre:** No. With 0 boundary children, canonical + position-as-key fully constrain the geometry. There are no degrees of freedom for a cheating prover to exploit: each child's type, position, and adjacency relationship to all siblings is uniquely determined. The hierarchy is either valid or it fails one of these checks.

- **Hat:** Yes. A cheating prover could place 7 boundary F children with consistent types and positions within their immediate parent, but with inconsistent cross-supertile adjacency. The boundary F children's positions relative to the neighboring supertile are not captured by the parent's cluster alone. The adjacency check (cross-supertile opening) closes this gap.

#### IOP proof size implications

| System | Adjacency check overhead | Cross-supertile openings |
|--------|--------------------------|------------------------|
| Spectre | 0 extra openings | 0 |
| Hat | Up to 7 extra supertile openings per query touching a boundary child | 7 out of 29 rule positions = 24% of queries may need 1 extra opening |

This is the **first concrete proof-structure advantage for spectre over hat** in the IOP setting: a semantic geometric IOP for spectre is achievable with canonical + position-as-key at zero extra query cost, while the same for hat requires cross-supertile openings for ~24% of queries at each level.

#### Spectre Z₂ orientation grading

The spectre substitution reverses all tile orientations at each level. Each child's angle is determined by the parent's angle and the child's slot. With position-as-key encoding `(x, y, angle)`, the Z₂ grading is already captured — it adds no additional checkable constraint beyond position-as-key.

#### Conclusions

- Spectre edge-adjacency is **purely local**: canonical check + position-as-key (already established in #28 and #33) are sufficient. Zero additional IOP overhead.
- Hat edge-adjacency is **non-local** for the 7 boundary F children: cross-supertile openings required, affecting ~24% of queries.
- A cheating prover has zero degrees of freedom in spectre (canonical + position-as-key fully constrains the geometry). Hat has a non-trivial attack surface at supertile boundaries.
- The semantic geometric IOP advantage for spectre is structural, not incidental: it follows directly from the 0 vs 7 boundary children count established in #30.

_See also: #28 (position-as-key ~7% overhead), #33 (canonical form zero-cost enforcement), #30 (boundary children as modification attack surface)._

---

### Spectral Gap Ratio and Convergence Rates (#51)

**Setup:** `cas/51_spectral_gap.gp`

#### All eigenvalues (exact)

| System | λ₁ (Perron) | λ₂ | λ₃ | λ₄ |
|--------|------------|----|----|-----|
| Hat | (7+3√5)/2 ≈ 6.854 | **1** (exact) | **−1** (exact) | (7−3√5)/2 ≈ 0.146 |
| Spectre | 4+√15 ≈ 7.873 | 4−√15 ≈ 0.127 | — | — |

#### Spectral gap ratios

**Hat:** The second-largest eigenvalue magnitude is **|λ₂| = |λ₃| = 1** — both ±1 lie on the unit circle. The formal ratio |λ₂|/λ₁ = 1/λ₁ = (7−3√5)/2 ≈ 0.146, but this masks a deeper issue: M^k never converges geometrically to a rank-1 Perron matrix because the unit-circle eigenvalues produce a PERSISTENT non-decaying component. The normalized tile frequency distribution (M^k·v / ‖M^k·v‖) does converge geometrically (at rate 1/λ₁ per step) since the dominant term grows as λ₁^k.

**Spectre:** Both eigenvalues are real with λ₁·λ₂ = det(M_spe) = 1, so λ₂ = 1/λ₁. The convergence rate is:

```
|λ₂|/λ₁ = 1/λ₁² = 1/(4+√15)² = 1/(31+8√15) ≈ 0.01613
Spectral gap g = 1 − 1/(31+8√15) = (30+8√15)/(31+8√15) ≈ 0.9839
```

This is exact and in Q(√15) (same field as λ₁ and the swap density f\*).

#### Convergence rates

**Spectre tile frequency convergence:**

| Levels k | Remaining error |(|λ₂|/λ₁)^k|
|---------|----------------|
| 1 | 1.61% |
| 2 | 0.026% |
| 3 | 0.00042% |

After **3 substitution levels**, spectre tile frequencies are within 0.01% of their Perron limit. This explains why the empirical swap density in #36 had fully converged at depth 3.

**S'/M' ratio convergence (from single Spectre seed):**

Starting from one Spectre tile, the S:M ratio of the inflation hierarchy converges to the right-eigenvector ratio r_S/r_M = 1/(√15−3) = (√15+3)/6 ≈ 1.145:

| Depth | S/M ratio | Error from limit |
|-------|-----------|-----------------|
| 1 | 1.1667 | 0.0212 |
| 2 | 1.1458 | 0.000285 |
| 3 | 1.14550 | 4.6×10⁻⁶ |
| 4 | 1.145497 | 7.4×10⁻⁸ |

Geometric convergence at rate (4−√15)² ≈ 0.016 per level, exactly as predicted.

#### Hat: unit eigenvalues and MI saturation

Hat has eigenvalues ±1 (from char poly factor (x−1)(x+1)). The corresponding integer eigenvectors (verified):
- λ=+1: [1, 1, 0, −1] — M·[1,1,0,-1] = [1,1,0,-1] ✓
- λ=−1: [−3, 3, 2, 1] — M·[-3,3,2,1] = -[−3,3,2,1] ✓

The projection of M·e_H (level-1 distribution from single H) onto the λ=1 eigenvector is **2/3 ≠ 0**, meaning the ±1 components persist at level 1. The MI saturation "after level 1" (finding #15) is therefore NOT explained by orthogonality eliminating unit-eigenvalue components. The correct explanation is that mutual information depends on CONDITIONAL probabilities (given a level-k supertile type), not the marginal tile frequencies — a different quantity from the eigenvector distribution.

#### Erasure plateau vs. spectral gap

The spectre erasure plateau decay (#23: depth-2=87%, depth-3=42%, depth-4=7.5%) is **not** the spectral gap convergence. The depth-to-depth ratios are ~0.48 and ~0.18, not the spectral gap 0.016. These are independent phenomena:

| Quantity | Rate | Governed by |
|----------|------|------------|
| Tile frequency stabilization | (4−√15)² ≈ 0.016/level | Spectral gap |
| Erasure plateau decay | ~0.2–0.5 per depth | Hierarchy structure |

#### Conclusions

- Hat has unit-circle eigenvalues (±1); normalized frequency distribution converges geometrically at rate 1/λ₁ ≈ 0.146/level (not zero, but bounded).
- Spectre has purely geometric convergence at rate **1/(31+8√15) ≈ 0.016/level**; exact in Q(√15).
- After 3 spectre substitution levels, tile frequencies are within 0.01% of limit.
- Swap density convergence reaches 4-decimal accuracy by depth 3 (consistent with #36 observation).
- Erasure plateau decay is independent of the spectral gap — a different phenomenon.

---

## Algebraic Number Theory (CAS Results)

All results in this section were computed with PARI/GP 2.17.3. Scripts are in `cas/`. These are exact algebraic computations, not experiments.

### Characteristic Polynomial, Minimal Polynomial, and Galois Group (#49)

**Setup:** `cas/49_char_poly_galois.gp`

#### Hat characteristic polynomial

```
charpoly(M_hat) = x^4 - 7x^3 + 7x - 1 = (x - 1)(x + 1)(x^2 - 7x + 1)
```

- Two rational eigenvalues: **+1 and −1** (consistent with det(M) = −1)
- One irreducible quadratic factor: x² − 7x + 1, discriminant 45 = 9·5 → field **Q(√5)**
- Hat Perron root: λ_hat = (7 + 3√5)/2 ≈ **6.8541**
- Non-Perron root of the quadratic: (7 − 3√5)/2 ≈ 0.1459

**Anti-palindromic structure:** x⁴ p(1/x) = −p(x) — confirmed by PARI. Every root λ pairs with 1/λ: the pair {+1, −1} and the pair {λ_hat, 1/λ_hat = (7−3√5)/2} both satisfy this. This explains the palindromic coefficient pattern (1, −7, 0, 7, −1) noted in WISDOM.md.

**Galois group of the splitting field Q(√5)/Q:** S2 = Z/2 (abelian, real quadratic extension).

#### Spectre characteristic polynomial

```
charpoly(M_spe) = x^2 - 8x + 1   [irreducible over Q]
```

- Discriminant 60 = 4·15 → field **Q(√15)**
- Spectre Perron root: λ_spe = 4 + √15 ≈ **7.8730**
- Galois group of Q(√15)/Q: S2 = Z/2

#### Relationship between the two eigenvalue fields

| Field | Defining polynomial | Discriminant | Perron root |
|-------|-------------------|-------------|------------|
| Q(√5) | x² − 7x + 1 | 5 | (7+3√5)/2 |
| Q(√15) | x² − 8x + 1 | 60 = 4·15 | 4+√15 |

Q(√5) and Q(√15) are **distinct** real quadratic fields. Their compositum Q(√3, √5) = Q(√5, √15) is generated by the minimal polynomial x⁴ − 16x² + 4 of √3+√5, has discriminant 3600 = 2⁴·3²·5², and Galois group **E(4) = Z/2 × Z/2** (Klein four-group). This is the natural coordinate ring of the tiling geometry, which involves both 5-fold (φ) and 3-fold (ω) symmetry.

#### Conclusions

- The hat substitution matrix has two rational eigenvalues (+1, −1) and a quadratic irrationality; it is far from "generic" (S₄ Galois group would be the generic case).
- Both eigenvalue fields are real quadratic with Galois group Z/2 — the simplest non-trivial algebraic structure.
- The two fields are related only through Q(√3, √5), not directly.
- The anti-palindromic structure of the hat charpoly is a direct algebraic consequence of det(M) = −1.

---

### Pisot/Salem Classification of the Dominant Eigenvalues (#50)

**Setup:** `cas/50_pisot_salem.gp`

**Both λ_hat and λ_spe are Pisot numbers.** A Pisot number is an algebraic integer > 1 all of whose algebraic conjugates have modulus strictly < 1.

| System | Perron root | Conjugate | |conjugate| | Classification |
|--------|------------|-----------|-----------|----------------|
| Hat | (7+3√5)/2 ≈ 6.854 | (7−3√5)/2 ≈ 0.146 | < 1 | **Pisot** |
| Spectre | 4+√15 ≈ 7.873 | 4−√15 ≈ 0.127 | < 1 | **Pisot** |

**Closed form for λ_hat:** Using φ = (1+√5)/2 (the golden ratio):

```
λ_hat = 2φ² + φ = φ(2φ + 1) = φ(√5 + 2)
```

Verified: φ(2φ+1) = 6.8541... ✓. This can also be written as **λ_hat = φ⁴** (established in #52 below).

**No φ-closed form for λ_spe:** Q(√15) is distinct from Q(√5), so 4+√15 has no closed form in terms of φ.

**Implication:** The Pisot property is standard for repetitive primitive substitution tilings. Neither system is Salem (which would require a conjugate on the unit circle). The Pisot property ensures that the frequencies converge exponentially fast, with convergence rate governed by |conjugate/Perron| = 1/λ² per level.

---

### Number Field Invariants of Q(λ_hat) and Q(λ_spe) (#52)

**Setup:** `cas/52_number_field_invariants.gp`

#### Q(√5) = Q(λ_hat)

| Invariant | Value |
|-----------|-------|
| Discriminant | 5 |
| Class number | **1** (PID) |
| Ring of integers | Z[φ], φ = (1+√5)/2 |
| Fundamental unit | φ = (1+√5)/2 |
| Regulator | log(φ) ≈ 0.4812 |

**λ_hat as an algebraic unit:**

```
λ_hat = (7+3√5)/2 = 3φ + 2 = φ⁴
```

λ_hat is a **unit** in Z[φ] (its norm N(λ_hat) = 1) and equals the 4th power of the fundamental unit φ. This is exact; PARI confirms φ⁴ = 6.8541... to full precision.

Prime splitting in Q(√5): p = 5 ramifies; primes p ≡ ±1 mod 5 split; primes p ≡ ±2 mod 5 are inert.

#### Q(√15) = Q(λ_spe)

| Invariant | Value |
|-----------|-------|
| Discriminant | 60 = 4·15 |
| Class number | **2** (NOT a PID) |
| Ring of integers | Z[√15] |
| Fundamental unit | 4+√15 = λ_spe |
| Regulator | log(4+√15) ≈ 2.0634 |

**λ_spe as an algebraic unit:**

λ_spe = 4+√15 is THE fundamental unit of Q(√15). Its norm N(4+√15) = 16−15 = 1. This means the spectre Perron eigenvalue is maximally simple from the unit-group perspective — it literally generates the unit group (together with −1).

The class number 2 means Z[√15] is not a UFD; there are ideals that are not principal. The class group is Z/2, generated by the prime ideal above 2 (since 2 ramifies: disc 60 = 4·15, 2|60).

#### Compositum Q(√3, √5)

| Invariant | Value |
|-----------|-------|
| Discriminant | 3600 = 2⁴·3²·5² |
| Class number | 1 (PID) |
| Regulator | ≈ 2.6153 |

The compositum has class number 1 despite containing Q(√15) (class number 2): the non-principal ideal of Q(√15) becomes principal in the larger field.

#### Conclusions

- λ_hat = φ⁴ is the 4th power of the golden ratio — a remarkable exact identity connecting the hat substitution to the Fibonacci sequence.
- λ_spe is itself the fundamental unit of Q(√15). The two Perron roots play structurally different roles: one is a power of a more fundamental number, the other is the most fundamental unit in its field.
- Q(√15) having class number 2 (non-PID) may affect the algebraic structure of the commitment scheme and IOP constructions based on spectre — unique factorization cannot be assumed in the ring of integers.

---

### Coordinate Ring of Tile Positions (#53)

**Setup:** `cas/53_coordinate_ring.gp`

#### Tile translation lattice

Every hat/spectre tile position `(tx, ty)` lives in the hexagonal lattice Z² with basis `e₁=(1,0)`, `e₂=(1/2, √3/2)` in Cartesian coordinates. This lattice is algebraically Z[ω], the **Eisenstein integers**, where ω = e^(iπ/3) = 1/2 + i√3/2 is a primitive 6th root of unity.

ω satisfies the **6th cyclotomic polynomial** Φ₆(x) = x²−x+1 (discriminant −3), so:

```
Z[ω] = Z[x]/(x²−x+1) = ring of integers of Q(√(−3))
```

This is one of the only two imaginary quadratic PIDs with a unit group of order 6 (the other is the Gaussian integers Z[i], which have 4 units).

#### Norm form

The norm of a lattice point a+bω is:

```
N(a+bω) = a² + ab + b²
```

This equals the squared hexagonal distance from the origin to (a,b). It is **multiplicative**: N(z·w) = N(z)·N(w), making Z[ω] → Z≥0 a ring homomorphism.

| (tx, ty) | N = a²+ab+b² | hex distance |
|----------|-------------|-------------|
| (0, 0) | 0 | 0 |
| (1, 0) | 1 | 1 |
| (0, 1) | 1 | 1 |
| (1, 1) | 3 | √3 |
| (2, 1) | 7 | √7 |
| (3, −1) | 7 | √7 |

Note: N=1 iff z is a unit. The 6 units of Z[ω] are ±1, ±ω, ±(1−ω), reflecting the hexagonal symmetry of the lattice.

#### Full tile group

The complete tile position group is:

```
Γ = Z[ω] ⋊ D₆ = Z² ⋊ D₆
```

where D₆ acts on Z[ω] by: rotation by k·(π/3) sends z ↦ ωᵏ·z, and reflection sends z ↦ z̄ (complex conjugate). The `CoxeterElement` struct in `crates/domain/src/coxeter.rs` implements this group in normal form `(tx: i64, ty: i64, rotation: u8, reflected: bool)`.

#### Exact positions and the inflation ring

The `psi` functor in `crates/tiling/src/geometry.rs` maps floating-point positions to integer hexagonal coordinates by rounding: `ty = round(y·2/√3)`, `tx = round(x − ty/2)`. Before rounding, exact child positions at level n live in:

```
Z[φ^{2n}, ω] ⊂ Q(√5, √(−3))
```

The compositum Q(√5, √(−3)) has degree 4 over Q, with:

| Field property | Value |
|----------------|-------|
| Degree | 4 |
| Discriminant | 225 |
| Class number | **1** (PID) |
| Signature | [0, 2] (totally complex) |
| Primitive element min. poly | x⁴ − 4x² + 64 |

After rounding (psi functor), positions return to Z[ω] with error ≤ 1/2 hexagonal unit.

#### Spectre subring

Spectre tiles have no reflected tiles (finding #30). Spectre positions live in:

```
Γ⁺ = Z[ω] ⋊ Z/6Z ⊂ Γ   (index-2 orientation-preserving subgroup)
```

This is a **group-theoretic** restriction, not an algebraic ring restriction. The coordinate ring is the same Z[ω] for both hat and spectre.

#### Splitting primes

Primes that split completely in Z[ω] (good primes for arithmetic in the lattice) are exactly those with p ≡ 1 mod 3: 7, 13, 19, 31, 37, 43, 61, 67, 73, 79, 97, ...

Primes p ≡ 2 mod 3 remain inert (prime in Z[ω]); p=3 ramifies (3 = −ω²(1−ω)² up to unit).

#### Conclusions

- Tile translation coordinates are **Eisenstein integers Z[ω]** — ring of integers of Q(√(−3)), class number 1, Euclidean algorithm exists.
- Norm form N(a+bω) = a²+ab+b² computes squared hex distance; it is multiplicative.
- Full tile group Γ = Z[ω] ⋊ D₆; spectre uses index-2 subgroup Γ⁺ (same ring, no reflections).
- Exact inflation positions at level n live in the degree-4 PID Q(√5, √(−3)) (disc = 225, class number 1); rounded back to Z[ω] by the psi functor.
- **SVP over Z[ω] is trivially easy**: the shortest vector has norm 1 (the 6 units). Standard lattice hardness (LWE/SIS) does **not** apply — Z[ω] is too structured for hardness.
- BLS12-381 and other primes ≡ 1 mod 3 are "good" for arithmetic in Z[ω]; primes 2, 3 ramify.

---

### Exact Tile Frequencies and Swap Density Closed Forms (#54)

**Setup:** `cas/54_swap_density.gp`, `cas/54b_spectre_swap_exact.gp`

#### Asymptotic tile frequencies (exact, in Q(√5))

The left PF eigenvector (normalized so H = 1/3) gives exact asymptotic frequencies:

| Type | Exact (unnormalized, sum=3) | Decimal |
|------|-----------------------------|---------|
| H | 1 | 0.3333 |
| T | (7−3√5)/2 | 0.0486 |
| P | −6+3√5 | 0.2361 |
| F | (9−3√5)/2 | 0.3820 |

The sum is exactly **3** — a pure integer, consistent with the WISDOM.md observation that the eigenvector scaled by 2 has integer component sum 6.

Verification: M^T v = λ_hat v with error < 10⁻⁷⁵ ✓

#### Hat tile counts (starting from a single H at level 0)

| Level n | Total tiles | [H, T, P, F] |
|---------|------------|--------------|
| 0 | 1 | [1, 0, 0, 0] |
| 1 | 8 | [3, 1, 2, 2] |
| 2 | 51 | [22, 3, 12, 14] |
| 3 | 351 | [147, 22, 84, 98] |
| 4 | 2402 | [1009, 147, 574, 672] |

Growth ratio ≈ 6.854 per level ✓

#### Spectre asymptotic tile frequencies (exact, in Q(√15))

| Type | Exact (unnormalized) | Decimal |
|------|---------------------|---------|
| Spectre | 6 | 0.8730 |
| Mystic | √15 − 3 | 0.1270 |

Sum = 3 + √15 ≈ 6.873. Asymptotic S'/M' ratio = 6/(√15−3) = **√15+3 ≈ 6.873**.

#### Exact swap density closed forms

The swap density formula counts (swap pairs from this parent type) / (total sibling pairs from this parent), weighted by the asymptotic parent-type frequency.

**Hat: exactly 1/5 for all depths and levels (∈ Q)**

Every non-trivial hat parent type contributes exactly 1/5:

| Parent | Children n | P'×F' pairs | C(n,2) | Density |
|--------|-----------|-------------|--------|---------|
| H' | 10 | 3×3=9 | 45 | **1/5** |
| P' | 5 | 1×2=2 | 10 | **1/5** |
| F' | 6 | 1×3=3 | 15 | **1/5** |

Since the density is identical for every contributing type, the overall density is exactly **1/5** regardless of depth or mix — algebraically constant.

**Spectre: (5+√15)/35 ≈ 25.35% (∈ Q(√15))**

Using the asymptotic S'/M' ratio r = √15+3:

```
f* = (7r + 6) / (28r + 21)           [7 swap pairs per S', 6 per M'; 28/21 total]
   = (7(√15+3) + 6) / (28(√15+3) + 21)
   = (7√15 + 27) / (28√15 + 105)
   = (5 + √15) / 35                   [after rationalizing: ÷ 735, simplify]
   ≈ 0.25351
```

Minimal polynomial of f*: **245x² − 70x + 2** (irreducible over Q; discriminant = 2940 = 4·3·5·49; conjugate (5−√15)/35 ≈ 0.032).

**Number-theoretic field distinction:**

| System | Swap density | Field | Notes |
|--------|-------------|-------|-------|
| Hat | 1/5 | Q | Rational; depth-independent |
| Spectre | (5+√15)/35 | Q(√15) | Irrational; Q(f*) = Q(λ_spe) |

The spectre swap density lives in the same field as the Perron eigenvalue — the algebraic structure of the tiling's dynamics is encoded directly in its security constant.

#### Tile count sequences mod p

Bad primes (where M has a repeated eigenvalue mod p = divisors of disc(charpoly)):
- Hat disc = 364500 = 2²·3⁶·5³ → bad primes: **2, 3, 5**
- Spectre disc = 60 = 2²·3·5 → bad primes: **2, 3, 5**

Observed periods of total tile count mod p (hat, starting from single H):

| Prime p | Period | Notes |
|---------|--------|-------|
| 2 | 3 | [0,1,1,0,1,1,...] — bad prime |
| 3 | 6 | [2,0,0,2,1,1,...] — bad prime |
| 5 | 10 | bad prime, longer period |
| 7 | 4 | good prime |
| 11 | 10 | good prime |

BLS12-381 prime does **not** divide either discriminant → good prime for both systems.

#### Conclusions

- Hat swap density = **1/5** exactly (rational, purely combinatorial, depth-independent).
- Spectre swap density = **(5+√15)/35** exactly (irrational, in Q(√15), minimal poly 245x²−70x+2).
- These live in different fields: hat in Q, spectre in Q(√15) = Q(λ_spe). This is a structural algebraic distinction, not merely a numerical one.
- Bad primes for both systems: 2, 3, 5. BLS12-381 is a good prime.

---

### Smith Normal Form of the Substitution Matrices (#55)

**Setup:** `cas/55_smith_normal_form.gp`

**Both substitution matrices have trivial Smith normal form:**

```
SNF(M_hat) = I₄   (identity 4×4)
SNF(M_spe) = I₂   (identity 2×2)
```

All elementary divisors are 1. This means:

| Property | Hat | Spectre |
|----------|-----|---------|
| Elementary divisors | (1,1,1,1) | (1,1) |
| Z-rank | 4 | 2 |
| Z-nullity | 0 | 0 |
| Cokernel Z^n/MZ^n | trivial (0) | trivial (0) |
| M ∈ GL(n,Z)? | Yes (det = −1) | Yes (det = 1) |

**Integer inverses:**

```
M_hat^{-1} = [ 0  1  0  0 ]     M_spe^{-1} = [ 1 -1 ]
             [ 1  3 -6  3 ]                   [-6  7 ]
             [ 0 -2  3 -2 ]
             [ 0  0 -1  1 ]
```

Verified: M · M^{-1} = I ✓ (exact integer arithmetic).

#### Implications

The trivial SNF means the substitution map Z^n → Z^n is an **isomorphism** (over Z, not just over Q). Deflation (applying M^{-1}) is an exact integer operation — no denominators, no rounding. This confirms and explains the integer structure observed in the tiling hierarchy, and establishes that the Anderson-Putnam cohomology for these tilings has no torsion (the chain map has trivial cokernel).

---

### Topological Entropy, Mahler Measure, and Substitution Zeta Function (#56)

**Setup:** `cas/56_zeta_mahler.gp`

#### Topological entropy

| System | Entropy h = log(λ) | Exact form |
|--------|--------------------|------------|
| Hat | 1.9248473... | log((7+3√5)/2) |
| Spectre | 2.0634371... | log(4+√15) |

Note: the spectre entropy **equals the regulator of Q(√15)** (= log of the fundamental unit = log(4+√15) ≈ 2.0634). This is not a coincidence: λ_spe IS the fundamental unit of Q(√15), so the topological entropy of the spectre tiling is exactly the arithmetic regulator of its eigenvalue field.

#### Mahler measure

The Mahler measure M(p) = ∏ max(1, |λᵢ|) equals the Perron root in both cases (Pisot property — only one root has modulus > 1):

| System | Mahler measure | Exact form |
|--------|---------------|-----------|
| Hat | (7+3√5)/2 ≈ 6.8541 | Pisot root of x²−7x+1 |
| Spectre | 4+√15 ≈ 7.8730 | Pisot root of x²−8x+1 |

The hat charpoly (x−1)(x+1)(x²−7x+1) contributes Mahler measure = 1·1·(7+3√5)/2. The two unit-circle roots (+1 and −1) contribute nothing. This matches the Lehmer-type structure: M(p_hat) is exactly the Perron root, no smaller.

#### Substitution zeta functions

```
ζ_hat(z) = 1 / ((1−z)(1+z)(1−7z+z²))
ζ_spe(z) = 1 / (1 − 8z + z²)
```

Both are rational functions of z (standard for primitive substitutions). Trace verification:

| n | tr(M_hat^n) | tr(M_spe^n) |
|---|------------|------------|
| 1 | 7 | 8 |
| 2 | 49 | 62 |
| 3 | 322 | 488 |
| 4 | 2209 | 3842 |
| 5 | 15127 | 30248 |
| 6 | 103684 | — |

The hat sequence 7, 49, 322, 2209, ... grows at rate λ_hat ≈ 6.854. The ratio 49/7 = 7, 322/49 ≈ 6.57, 2209/322 ≈ 6.86 converges to λ_hat.

#### Conclusions

- The spectre topological entropy equals the arithmetic regulator of Q(√15): h_spe = log(4+√15) = reg(Q(√15)).
- The Mahler measures are the Perron roots (not 1 — these are "interesting" polynomials in the sense of Lehmer's problem).
- The substitution zeta functions are rational with the exact pole structure determined by the characteristic polynomial factorization.

---

### GAB Equation, Sturmian Slope, and Hat-Polykite Density (#57)

**Setup:** `cas/57_gab_hat_density.gp`

These quantities appear in the ROCQ proofs (`HatSpectral.v`, `Substitution.v`) but were not previously computed by CAS.

#### GAB frequency equation

The GAB equation arises in spectral analysis of hat substitution. In integer form: **5q² − 5q + 1 = 0**.

Roots in Q(√5):

| Root | Exact form | Numerical |
|------|-----------|-----------|
| q₊ | (5+√5)/10 | ≈ 0.72361 |
| q₋ | (5−√5)/10 | ≈ 0.27639 |

Verification: 5q₊² − 5q₊ + 1 = 0 ✓ (to 38 decimal places). Discriminant = 5 (consistent with Q(√5) membership).

Algebraic properties:
- Both q± ∈ Q(√5) (= 1/2 ± √5/10)
- Neither is an algebraic integer (minimal poly has leading coeff 5)
- 10·q± = 5±√5 = 4±2φ **are** algebraic integers in Z[φ], with norm N(5+√5) = 20 = 2²·5

#### Sturmian slope identification

The hat tiling has continued fraction expansion [0; 3, 1, 1, 1, ...]. CAS computes this slope exactly:

```
slope = 1 / (3 + (φ−1)) = 1 / (2 + φ) = (5−√5)/10 = q₋
```

**q₋ = (5−√5)/10 IS the hat Sturmian slope** (verified numerically; match confirmed to 38 digits).

#### ROCQ comment clarification

`HatSpectral.v` calls q₊ the "H-metatile frequency." This is imprecise — q₊ and the PF eigenvector frequency f_H are different quantities in different models:

| Quantity | Value | Meaning |
|----------|-------|---------|
| PF frequency f_H | 1/3 ≈ 0.333 | Fraction of metatile *instances* that are H-type |
| q₊ = (5+√5)/10 | ≈ 0.724 | Sturmian symbol density (fraction of *area* or *space*) |

These are not equal. The PF eigenvector measures instance frequency; q₊ measures the spatial/symbolic density of H-symbols in the associated Sturmian word with slope q₋.

#### Hat-polykite density vector

From `Substitution.v`: h = [4, 1, 2, 2] is the number of hat polykite tiles in each metatile type (H: 4, T: 1, P: 2, F: 2).

**ROCQ claim M·h = [25, 4, 14, 16] verified:**

```
M_hat · [4, 1, 2, 2]ᵀ = [25, 4, 14, 16]ᵀ  ✓
```

(Exact integer arithmetic confirms the ROCQ proof.)

#### Right PF eigenvector (exact, in Q(√5))

For eigenvalue λ = (7+3√5)/2, setting r_H = 1 and solving M·r = λ·r:

| Component | Exact form | Numerical |
|-----------|-----------|-----------|
| r_H | 1 | 1.0 |
| r_T | (7−3√5)/2 | ≈ 0.14590 |
| r_P | (3√5−5)/3 | ≈ 0.56940 |
| r_F | 2/3 | ≈ 0.66667 |

Derivation: r_F = 2/3 follows from the substitution λ²−7λ+1 = 0, which gives λ²−4λ+1 = 3λ, collapsing a 4×4 system to an exact rational solution over Q(√5).

#### Asymptotic hat-polykite count per metatile

Average number of hat polykite tiles per metatile as level n → ∞:

```
h · r / (1 · r) = (11+√5)/2 / (7−√5)/2
               = (11+√5) / (7−√5)
               = (41+9√5) / 22
               ≈ 2.7784
```

This is > 1 (expected: each metatile consists of multiple polykites). The exact form **(41+9√5)/22 ∈ Q(√5)** is confirmed.

Rationalization: (11+√5)(7+√5) / ((7−√5)(7+√5)) = (82+18√5)/44 = (41+9√5)/22.

#### Conclusions

- q₋ = (5−√5)/10 is the hat tiling Sturmian slope (exactly the CF value [0;3,1,1,1,...]). Proved by CAS.
- q₊ = (5+√5)/10 is the complementary symbol density (= 1 − q₋), not the PF metatile frequency.
- The ROCQ `HatSpectral.v` label "H-metatile frequency" for q₊ is a misnomer: it should read "Sturmian complementary density."
- M·h = [25,4,14,16] verified exactly (no rounding).
- Right PF eigenvector has exact form (1, (7−3√5)/2, (3√5−5)/3, 2/3) in Q(√5).
- Asymptotic hat-polykite tiles per metatile = **(41+9√5)/22 ≈ 2.778** (exact, in Q(√5)).
