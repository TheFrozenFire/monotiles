# Research Summary: Section-by-Section Walkthrough

A conversational walkthrough of [RESEARCH.md](RESEARCH.md), explaining the key ideas,
connections, and significance of each section.

---

## Section 1: Introduction

Sets the stage. The hat (March 2023) and spectre (May 2023) solved a 60+ year open problem.
The document identifies five properties of these tilings that are potentially cryptographically
relevant: hierarchical substitution, irrational frequency ratios, group-theoretic encoding,
local indistinguishability with global diversity, and connections to computational hardness.
This is the lens through which everything else is read.

---

## Section 2: The Hat Monotile

This is the core object. The hat is 8 kites glued together from the `[3.4.6.4]` Laves
tiling -- a 13-sided polygon with edges of length 1, sqrt(3), and 2.

The critical insight is that the hat isn't isolated -- it belongs to a **continuous
one-parameter family** Tile(a,b). You can smoothly deform it by independently scaling two
families of edges. At the extremes (chevron, comet, equilateral) it tiles periodically;
everywhere else it's aperiodic. This continuum is what makes the first aperiodicity proof
work.

The **metatile system** (H, T, P, F) is how you analyze hat tilings at a coarser scale. Every
hat tiling decomposes into these four cluster shapes with signed edge-matching rules. The
metatiles then compose into supertiles, and here's the twist: unlike Penrose, the supertiles
are **not geometrically similar** to the originals -- only combinatorially equivalent. But
when you iterate to a fixed point, the limit shapes converge and become genuinely self-similar,
with edge lengths in **Z[phi]** (the ring of integers adjoined with the golden ratio). The
inflation factor is phi^2 ~ 2.618.

Every hat tiling necessarily mixes reflected and unreflected copies at roughly a 1:7 ratio.
This is why the spectre was needed.

---

## Section 3: The Spectre

The spectre eliminates the reflection requirement. It's built from Tile(1,1) -- the
equilateral member of the family -- by replacing straight edges with **s-curves** (paths with
180-degree rotational symmetry). The angle alternation at vertices (90-degree multiples
alternating with 120-degree multiples) means a spectre physically can't fit against its own
mirror image. Shape alone enforces chirality.

The substitution system is wild: it operates on a Spectre and a "Mystic" (a two-spectre
compound), and **every application reverses all tile orientations**. This has no precedent in
substitution tiling theory. The area scaling is `4 + sqrt(15)` -- irrational, so
non-periodicity follows immediately.

The aperiodicity proof is a five-step chain of combinatorial equivalences: Spectre tilings
<--> Tile(1,1) tilings <--> hat-turtle tilings <--> cluster tilings <--> 9 marked hexagons
<--> unique hierarchy. Each step preserves periodicity properties, so non-periodicity
propagates through the entire chain.

---

## Section 4: Substitution Tiling Theory

This is the theoretical foundation that all the specific tiles sit on top of. Frank's
primer [7] gives the formal framework.

The key objects: an **expansion map** phi (linear, all eigenvalues > 1 in modulus), a
**substitution rule** sigma that replaces each tile with a configuration occupying phi(tile),
and the **substitution matrix** M counting how many of each tile type appear in each
substitution.

**Perron-Frobenius theory** on M is the engine: the dominant eigenvalue gives the volume
expansion factor, the left eigenvector gives relative tile volumes (and hence frequencies).
Whether the expansion constant is a **Pisot number** (all Galois conjugates have modulus < 1)
determines whether the tiling is well-behaved (pure point spectrum, convergent shapes) or
pathological (fault lines, weak mixing). The golden ratio is Pisot; that's why hat tilings
are well-behaved.

The **Thurston-Kenyon theorem** constrains what expansion constants are even possible: they
must be algebraic integers strictly larger than all their Galois conjugates (except the
complex conjugate).

The tiling space (all admitted tilings under the local topology) forms a compact dynamical
system under R^d translation. **Recognizability** -- the ability to locally "undo" the
substitution -- is equivalent to the substitution map being invertible on this space.

---

## Section 5: Group-Theoretic Frameworks

This is where the geometry gets algebraized. Coulbois et al. [3] showed that the symmetry
group of the kitegrid is a **triangle Coxeter group** of type [6, 3, 2]:

```
Gamma = <alpha, beta, gamma | alpha^2, beta^2, gamma^2, (alpha*beta)^6, (beta*gamma)^3, (alpha*gamma)^2>
```

Three generators, all involutions (reflections). The orientation-preserving subgroup Gamma^+
is `Z^2 ⋊ Z/6Z` -- a lattice of translations extended by a 6-fold rotation. Both are
**virtually Z^2**, meaning they contain Z^2 as a finite-index subgroup.

The **Cucaracha** is the hat tile, discretized into group theory. You take the semikite as a
fundamental domain, then record which group elements are needed to cover the hat. The result
is a 16-element subset of Gamma (words of length <= 4 in the generators). This finite subset
tiles the group Gamma aperiodically -- it's a **group monotile**.

This sits at a sharp boundary: Z^2 itself admits no aperiodic monotile (Bhattacharya 2020,
Greenfeld-Tao 2021), but the virtually-Z^2 group Gamma does. The extra Z/6Z of rotational
symmetry is what makes the difference.

The **discretization functor** Psi is general-purpose: it works for any crystallographic group
in any dimension, for hyperbolic tilings, for locally compact groups with Haar measure. The
cotiler set can be viewed as a **subshift of finite type**, connecting everything to symbolic
dynamics.

---

## Section 6: Aperiodicity Proof Techniques

Four different proof strategies, each revealing different structure:

**Proof 1 (Geometric Incommensurability):** The most elegant. Assume periodicity, then deform
the tile to both degenerate endpoints (chevron and comet). Both degenerate tilings would be
periodic, connected by an affine map that scales area by 2/3. Frequency analysis forces this
map to be a similarity with factor sqrt(2/3). But squared distances in triangular lattices are
Loeschian numbers (m^2 + mn + n^2), which always have an even number of factors of 2 --
making sqrt(2/3) impossible. Contradiction.

**Proof 2 (Hierarchical):** More traditional. Computer-verify that all 188 surroundable
2-patches decompose into metatiles, then show forced composition into supertiles. The "PP
configuration" is the key impossibility that eliminates wrong cases.

**Proof 3 (Golden Ammann Bars):** Akiyama-Araki's independent approach. Mark each tile with
bars that must extend across boundaries into infinite lines forming a Kagome lattice. The
frequency equation `q^2 - q + 1/5 = 0` yields irrational roots `(5 +/- sqrt(5))/10`.
Periodic tilings would need rational frequencies. The connection to Sturmian words
(palindromic central words, slope `1/(1 + tau^2)`, continued fraction `[3, 1, 1, 1, ...]`)
is especially nice.

**The Irrationality Paradigm:** All proofs ultimately reduce to the same thing -- aperiodicity
is forced because some ratio must be irrational (phi^2, `4 + sqrt(15)`, `(5 +/- sqrt(5))/10`),
but periodicity would force it to be rational. The specific algebraic irrationality varies,
but the pattern is universal.

---

## Section 7: Historical Context

The 60-year arc from Wang to the hat. Wang (1961) showed the domino problem is decidable iff
no aperiodic tile set exists. Berger (1966) found one with 20,426 tiles, proving both
undecidability and Wang's conjecture wrong. Then a race to minimize: down through Penrose
(2 tiles with rotations), Taylor-Socolar (1 tile but not simply connected), and finally the
hat (1 simply connected tile).

The table at 7.3 captures the conceptual progression: from edge-color matching to shape-alone
aperiodicity, from undecidability to strict chirality. Each step weakened the assumptions
needed to force aperiodic order.

The key connection for us: **Wang tiles can simulate Turing machines**, so the domino problem
encodes the halting problem. This is the deepest source of computational hardness in the
tiling world.

---

## Section 8: Hierarchical Structure Forcing

Goodman-Strauss [6] industrialized aperiodic tile set construction. The three-step recipe:
(1) tiles force hierarchical decomposition, (2) hierarchy prevents periodicity,
(3) compactness guarantees tilings exist.

From just dominos, he built 211 tiles yielding **25,380** hierarchically distinct aperiodic
subsets. The construction uses a four-channel edge-marking system where the Klein four-group
`Z_2 + Z_2` acts via nim addition (XOR on binary strings). Each channel controls a different
aspect: orientation, sidedness, hierarchical level, orientation refinement.

The local-to-global forcing mechanism works through emergent layers: edge matching -> block
formation -> supertile assembly -> orientation control -> infinite hierarchy. A **local
derivation** Phi (finite lookup table) bridges matching-rule space to substitution-rule space
in constant time per tile.

The capstone: **every** geometric substitution tiling in R^d (d > 1) can be enforced with
finite matching rules. Substitution, matching rules, and aperiodicity are all equivalent.

---

## Section 9: Connections to Error Correction

This is where things get directly relevant to cryptography-adjacent applications. Li and
Boyle [8] showed that Penrose tilings are literally quantum error-correcting codes.

The construction: take each equivalence class of Penrose tilings (under Euclidean
transformations), form a quantum superposition over the entire orbit. These orbit states form
an orthogonal code basis.

Two tiling properties map exactly to QECC requirements:

- **Local indistinguishability** (any finite patch appears in every tiling at the same
  frequency) -> code states have identical reduced density matrices in any finite region
- **Local recoverability** (finite region uniquely determined by complement) -> erasure of
  any finite region is correctable

The continuum code corrects errors in ANY finite region. The discrete Fibonacci version
corrects contiguous errors of length f_n + 1 in a string of length ~f_{n+1}. Entanglement
entropy is `log(n) + O(1)` -- intermediate between topological codes (constant) and random
codes (linear), similar to critical systems.

The framework applies to **any** substitution tiling with these two properties. Hat and
spectre tilings should qualify (local indistinguishability from Perron-Frobenius, local
recoverability from the unique hierarchy), but this hasn't been rigorously established yet.

---

## Section 10: Toward Cryptographic Applications

Six directions, roughly ordered from most concrete to most speculative:

1. **Hard problems**: The undecidability of the domino problem suggests tiling decision
   problems might provide hard instances. The local-to-global gap (local patches reveal
   nothing about global identity) parallels lattice-based crypto.

2. **Algebraic structures**: The Coxeter group Gamma and the Cucaracha give a concrete
   algebraic setting where operations are efficient but recovering global structure from local
   data may be hard. The number fields Q(sqrt(5)) and Q(sqrt(15)) from substitution matrices
   could support number-theoretic constructions.

3. **One-way substitution**: Inflation is easy (local rule per tile). Deflation needs global
   context (identify supertile boundaries). This asymmetry looks like a one-way function. The
   spectre's handedness reversal adds a Z_2 grading.

4. **Error correction**: The QECC construction shows tilings naturally encode information
   with error-correcting properties, with code parameters unlike existing families.

5. **Irrational frequency trapdoors**: Knowing the exact algebraic irrationality lets you
   compute tile frequencies; extracting the irrationality from approximate frequency data is
   a number-theoretic problem.

6. **Subshift encoding**: Tilings as subshifts of finite type connect to coding theory.
   Sturmian sequences achieve minimal complexity p(n) = n + 1.

---

## Section 11: Open Questions

Five from the literature (strongly aperiodic geometric monotile? undecidability of
monotileability in Gamma? minimal marked hexagon sets? cut-and-project structure? fault line
characterization?) and five for cryptographic exploration (formalizing the local-to-global gap
as a hard search problem, Pisot lattice problems in Z[phi], deflation hardness, spectre
orientation-reversal hashing, Cucaracha-based group crypto).

---

## Section 12: References

All 8 papers with arXiv IDs and local paths to the PDFs in `papers/`.

---

## The Cryptographic Thread

The most promising structural feature is the combination of **local indistinguishability**
(any finite window looks the same across all tilings) with **rigid global determination**
(the full tiling is uniquely fixed). This is directly analogous to the "learning with errors"
paradigm -- local noise hides global structure.

The **group-theoretic encoding** via the Cucaracha in the Coxeter group Gamma gives you a
concrete algebraic setting to work in, and the **substitution matrix spectral theory** (Pisot
eigenvalues, algebraic number fields) gives you the number theory.

The **error-correction connection** suggests these structures have natural redundancy and fault
tolerance built in.
