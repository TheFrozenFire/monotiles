# Aperiodic Monotiles: Mathematical Foundations and Cryptographic Potential

## Table of Contents

1. [Introduction](#1-introduction)
2. [The Hat Monotile](#2-the-hat-monotile)
3. [The Spectre: A Strictly Chiral Monotile](#3-the-spectre-a-strictly-chiral-monotile)
4. [Substitution Tiling Theory](#4-substitution-tiling-theory)
5. [Group-Theoretic Frameworks](#5-group-theoretic-frameworks)
6. [Aperiodicity Proof Techniques](#6-aperiodicity-proof-techniques)
7. [Historical Context: Wang Tiles to Monotiles](#7-historical-context-wang-tiles-to-monotiles)
8. [Hierarchical Structure Forcing](#8-hierarchical-structure-forcing)
9. [Connections to Error Correction](#9-connections-to-error-correction)
10. [Toward Cryptographic Applications](#10-toward-cryptographic-applications)
11. [Open Questions](#11-open-questions)
12. [References](#12-references)

---

## 1. Introduction

In March 2023, David Smith, Joseph Myers, Craig Kaplan, and Chaim Goodman-Strauss resolved
a problem open for over 60 years: they found a single tile -- the "hat" -- that tiles the
Euclidean plane but only aperiodically [1]. Two months later, they followed up with the
"spectre," a strictly chiral monotile requiring no reflected copies [2]. These discoveries
sit at the intersection of discrete geometry, combinatorics, group theory, dynamical systems,
and number theory.

This document surveys the mathematical properties of aperiodic monotiles as established across
the foundational literature, with an eye toward structures that may be exploitable for
cryptographic primitive design. The key properties of interest are:

- **Hierarchical substitution structure**: local rules that force global aperiodic order
- **Irrational frequency ratios**: tile type densities involving algebraic irrationals
- **Group-theoretic encoding**: tilings as elements of Coxeter groups and related structures
- **Local indistinguishability with global diversity**: finite patches reveal nothing about
  global tiling identity
- **Computational hardness**: connections to undecidability and the domino problem

---

## 2. The Hat Monotile

### 2.1 Geometric Definition

The hat is a **polykite**: the union of 8 kites from the `[3.4.6.4]` Laves tiling (dual of
the `(3.4.6.4)` Archimedean tiling). It is a 13-sided non-convex polygon with edges of three
lengths: **1**, **sqrt(3)**, and **2** (where the length-2 edge is two collinear unit edges).
All interior angles are multiples of 30 degrees, with four reflex angles [1].

The hat belongs to a continuous one-parameter family **Tile(a, b)**, where `a` and `b`
independently scale two families of edges (those at even vs. odd multiples of 30 degrees
to the horizontal). Key members of this family:

| Tile(a, b)         | Name      | Aperiodic? |
|--------------------|-----------|------------|
| Tile(1, sqrt(3))   | **Hat**   | Yes        |
| Tile(sqrt(3), 1)   | **Turtle**| Yes        |
| Tile(1, 1)         | Equilateral | Periodic with reflections; weakly chiral aperiodic without |
| Tile(0, 1)         | Chevron   | Periodic   |
| Tile(1, 0)         | Comet     | Periodic   |

**Main theorem [1]:** Tile(r) is an aperiodic monotile for all positive `r != 1`. The three
degenerate boundary cases admit periodic tilings; all others are aperiodic.

The area of Tile(a, b) is `sqrt(3)(2a^2 + sqrt(3)ab + b^2)`.

### 2.2 The Metatile System

Hat tilings decompose into clusters encoded by four **metatiles** [1]:

- **H** (irregular hexagon): 4 hats (1 reflected + 3 unreflected shell)
- **T** (equilateral triangle): 1 unreflected hat
- **P** (parallelogram): 2 unreflected hats
- **F** (pentagonal triskelion leg): 2 unreflected hats

Edge-matching rules using signed labels (A+/A-, B+/B-, X+/X-, F+/F-, L/L) enforce legal
adjacency. Metatiles may only be rotated, never reflected.

### 2.3 Substitution Rules and the Golden Ratio

Level-1 supertiles (H', T', P', F') are assembled from patches of metatiles. A critical
subtlety: unlike classical substitution tilings, supertiles are **not geometrically similar**
to the original metatiles (except T). They are only **combinatorially equivalent** -- same
edge label structure, same matching rules [1].

When iterated to convergence, the limit shapes become genuinely self-similar. The converged
tile edge lengths lie in the ring **Z[phi]** where `phi = (1 + sqrt(5))/2` is the golden
ratio. The key parameters:

- **Inflation factor:** `phi^2 = phi + 1 ~ 2.618`
- **Area inflation:** `phi^4`
- **Substitution matrix leading eigenvalue:** `phi^2`

The golden ratio arises algebraically from the substitution matrix. Additionally, the
identity `1 + phi^{-1} + phi^{-2} = 2` connects the `[3.4.6.4]` lattice geometry to `phi`.

### 2.4 Reflections and Tile Ratios

Every hat tiling necessarily contains both reflected and unreflected copies. Each reflected
hat sits inside an H metatile, surrounded by a shell of 3 unreflected hats. The limiting
proportion of reflected to total tiles is determined by the Perron-Frobenius eigenvector of
the substitution matrix -- approximately **1:7** in the limit [1].

### 2.5 Hierarchy and Unique Decomposition

Every metatile belongs uniquely to a level-1 supertile, every level-1 supertile to a level-2
supertile, and so on for all levels. The radius of a ball contained in a level-n supertile
grows without bound. This unique infinite hierarchical structure is the foundation of the
aperiodicity proof: it is incompatible with translational symmetry [1].

---

## 3. The Spectre: A Strictly Chiral Monotile

### 3.1 Chirality and Motivation

The hat's requirement for reflected copies left open whether a single tile could tile
aperiodically using only orientation-preserving isometries (translations and rotations). The
spectre resolves this [2]:

- A **weakly chiral** monotile has all its homochiral tilings non-periodic (Tile(1,1))
- A **strictly chiral** monotile admits *only* homochiral non-periodic tilings (the Spectre)

### 3.2 Construction from Tile(1,1)

The spectre is constructed from the equilateral member Tile(1,1) by replacing each straight
edge with a curved **s-curve** -- a simple path symmetric under 180-degree rotation about
its center. The vertex angles of Tile(1,1) strictly alternate between multiples of 90 degrees
and multiples of 120 degrees. The s-curve symmetry prevents a spectre from fitting against
its reflection, geometrically enforcing chirality [2].

### 3.3 Substitution System with Handedness Reversal

The spectre substitution operates on two objects [2]:

- A single **Spectre** (one tile)
- A **Mystic**: a symmetric two-spectre compound with 180-degree rotational symmetry

The substitution rules:
1. Spectre --> 1 Mystic + 7 Spectres (all orientation-reversed)
2. Mystic --> 1 Mystic + 6 Spectres (all orientation-reversed)

**Each application reverses all tile orientations.** This is unprecedented in substitution
tiling theory. The area scaling factor is `4 + sqrt(15)`, which is irrational -- immediately
implying non-periodicity of any substitution-generated tiling.

### 3.4 Proof Architecture

The aperiodicity proof chains combinatorial equivalences [2]:

1. Spectre tilings <--> Tile(1,1) homochiral tilings (by construction)
2. Tile(1,1) tilings <--> homochiral hat-turtle tilings (Theorem 3.1, edge deformation)
3. Hat-turtle tilings --> T7H/T8H clusters (computer-assisted corona analysis)
4. T7H/T8H tilings --> 9 marked hexagons (Gamma through Psi)
5. Marked hexagons --> unique hierarchical supertile composition (Theorem 5.1)

The hierarchy forces non-periodicity: any translation symmetry would force a large supertile
to overlap its translate, contradicting uniqueness.

---

## 4. Substitution Tiling Theory

### 4.1 Formal Framework

A **tiling substitution rule** on a prototile set P with expansion map phi (a linear map with
all eigenvalues of modulus > 1) assigns to each tile t a configuration sigma(t) whose support
is phi(t). Applying sigma and rescaling is the **inflate-and-subdivide** operation [7].

A tiling T is **self-similar with expansion phi** if it is phi-subdividing, repetitive, and
has finite local complexity (FLC) [7]:

- **FLC**: finitely many two-tile patches up to rigid motion
- **Repetitivity**: for any patch P, there exists R > 0 such that every ball of radius R
  contains a copy of P

### 4.2 The Substitution Matrix

For prototiles {1, ..., m}, the substitution matrix M has entries `M_{ij}` = number of tiles
of type i in the substitution of tile type j. Key spectral results [7]:

- **Perron-Frobenius theorem**: If M is irreducible, the largest eigenvalue (Perron
  eigenvalue) is positive, real, and of multiplicity one.
- **Primitivity criterion**: M is primitive iff some power M^n has all positive entries.
  An FLC phi-subdividing tiling is repetitive iff M is primitive (Praggastis).
- **Volume relation**: For primitive M, the Perron eigenvalue equals `|det phi|`, and the
  left Perron eigenvector gives relative prototile volumes (Solomyak).

### 4.3 Expansion Constants and Algebraic Constraints

**Thurston-Kenyon theorem [7]:** A complex number lambda is the expansion constant for some
self-similar tiling if and only if lambda is an algebraic integer strictly larger in modulus
than all its Galois conjugates (except its complex conjugate).

The nature of the expansion constant profoundly affects tiling dynamics:

- **Pisot numbers** (all conjugates have modulus < 1): well-behaved substitutions, pure point
  dynamical spectrum, convergent replace-and-rescale. Examples: golden ratio phi = (1+sqrt(5))/2
  (Fibonacci, Penrose), tribonacci constant (Rauzy fractals).
- **Non-Pisot**: fault lines, loss of FLC, weak mixing. Example: (5+sqrt(5))/2 (binary
  tilings are weakly mixing despite having the same tile ratio as Penrose) [7].

### 4.4 Tiling Spaces as Dynamical Systems

The set of all tilings admitted by a substitution forms a compact topological space (the
**hull** or **tiling space**) under the local topology. The translation action of R^d makes
this a dynamical system [7]:

- **Spectral measures** decompose into pure point, singular continuous, and absolutely
  continuous components
- **Diffraction spectra** of quasicrystalline materials correspond to dynamical spectra
  (Dworkin, Hof)
- **Recognizability**: for non-periodic primitive substitutions, the substitution map is
  invertible on the tiling space (Mosse for 1D, Solomyak for higher dimensions)

### 4.5 Connections to Symbolic Dynamics

Substitution tilings are intimately connected to subshifts. An infinite sequence over an
alphabet A is **admitted** by a substitution if every finite block appears in some level-n
block. The space of admitted sequences under the shift action forms a subshift [7].

The **complexity function** p(n) counts distinct length-n words. Non-periodic sequences with
minimal complexity (p(n) = n + 1) are **Sturmian** -- they arise from codings of irrational
rotations on the circle.

---

## 5. Group-Theoretic Frameworks

### 5.1 The Coxeter Group of the Kitegrid

The `[3.4.6.4]` Laves tiling (the "kitegrid") has a rich symmetry structure formalized as a
Coxeter group [3].

Let alpha, beta, gamma be reflections along the three sides of a "semikite" (half of a kite,
bisected along its long diagonal). The full symmetry group is [3]:

```
Gamma = <alpha, beta, gamma | alpha^2, beta^2, gamma^2, (alpha*beta)^6, (beta*gamma)^3, (alpha*gamma)^2>
```

This is a **triangle Coxeter group** of type [6, 3, 2]. Its index-2 orientation-preserving
subgroup is:

```
Gamma^+ = <R_3, R_6 | R_3^3, R_6^6, (R_3 * R_6)^2>
```

where `R_6 = beta * alpha` (rotation by pi/3) and `R_3 = gamma * beta` (rotation by 2*pi/3).

**Key structural facts [3]:**

- The translations `t_1 = R_6^{-1} R_3 R_6^{-1}` and `t_2 = R_6^{-2} R_3` generate a
  lattice `L ~ Z^2`
- `Gamma^+ ~ Z^2 ⋊ Z/6Z` (semidirect product)
- `Gamma ~ Z^2 ⋊ (Z/6Z x Z/2Z)`
- Both Gamma and Gamma^+ are **virtually Z^2** with planar Cayley graphs
- The Cayley graph of Gamma^+ (generators {R_6, R_3}) is the 1-skeleton of the `4.3.4.6`
  Archimedean tiling
- The Cayley graph of Gamma (generators {alpha, beta, gamma}) is the 1-skeleton of the
  `4.6.12` Archimedean tiling

### 5.2 The Cucaracha: An Aperiodic Group Monotile

Applying the discretization functor Psi to the hat yields the **Cucaracha** -- a 16-element
subset of Gamma expressed as words of length <= 4 in {alpha, beta, gamma} [3]:

```
Cucaracha = {1, alpha, beta, gamma, alpha*beta, beta*alpha, beta*gamma, gamma*beta,
             alpha*beta*alpha, beta*alpha*beta, beta*alpha*gamma, gamma*beta*alpha,
             alpha*beta*alpha*gamma, beta*gamma*beta, gamma*beta*alpha*beta,
             gamma*beta*alpha*beta}
```

**Theorem (Coulbois et al.) [3]:** The Cucaracha is a **mildly aperiodic monotile** of the
group Gamma. The possible stabilizers of its cotilers are {id} or conjugates of
{id, R_3, R_3^2}, and both cases are achieved.

This result bridges the 2023 geometric discovery (Smith et al.) with the group-theoretic
framework (Greenfeld-Tao). Unlike Greenfeld-Tao's construction in Z^2 x H (a direct
product), the Cucaracha lives in a **semidirect product** `Z^2 ⋊ Z/6Z`, which prevents
lifting to Z^d via the Meyerovitch-Sanadhya-Solomon operation [3].

### 5.3 The Discretization Machinery

The paper [3] develops a general framework: for a countable group G acting on a space W with
a finite grid K (fundamental domain), the map Psi_K establishes a bijection between poly-K
tiles of W and finite tilesets of G, preserving cotiler sets exactly.

**Key consequence:** W admits (weakly/mildly/strongly) aperiodic poly-K sets if and only if G
admits aperiodic sets of finite tiles, with the same number of tiles [3].

This framework applies to:
- Any crystallographic group in any dimension (via Bieberbach's theorem)
- Hyperbolic tilings (`W = H^2`, `G = PGL_2(R)`)
- Locally compact groups with Haar measure

### 5.4 Symmetry Classification of Hat Tilings

The symmetry group of any hat tiling is either trivial {id} or conjugate to {id, R_3, R_3^2}
(order-3 rotational symmetry). No hat tiling has translational, reflective, order-6
rotational, or glide-reflective symmetry [3].

Both extremes are achieved: the "fylfot" (three F-metatiles) seed under iterated substitution
produces a tiling with 3-fold rotational symmetry, while a T-metatile seed produces a tiling
with trivial symmetry [3].

### 5.5 The Cotiler Group and Subshift Connection

For a tileset T with cotiler C, the **cotiler group** is [3]:

```
G_C := <g * h^{-1} | (g, T), (h, T) in C, T in T>
```

The cotiler set can be viewed as a **subshift of finite type**: encoding a cotiler as a
configuration in (2^T)^G, validity is a locally checkable property. This directly connects
the tiling framework to symbolic dynamics [3].

---

## 6. Aperiodicity Proof Techniques

### 6.1 Geometric Incommensurability (Smith et al., Proof 1)

The most novel proof technique exploits the Tile(a,b) continuum [1]:

1. Assume the hat = Tile(1, sqrt(3)) admits a strongly periodic tiling T
2. Contract 1-sides to 0: get periodic chevron tiling T_4 (area 3*sqrt(3) per tile)
3. Contract sqrt(3)-sides to 0: get periodic comet tiling T_8 (area 2*sqrt(3) per tile)
4. The affine map g between the two periodic lattices must scale areas by 2/3
5. Frequency analysis forces g to be a similarity (scale factor sqrt(2/3))
6. But squared distances in triangular lattices are Loeschian numbers `m^2 + mn + n^2`,
   which always have an even number of factors of 2 -- making sqrt(2/3) impossible

**Contradiction.** The map must be a similarity but cannot be.

### 6.2 Berger-Style Hierarchical Proof (Smith et al., Proof 2)

A more traditional approach via computer-assisted case analysis [1]:

1. **Clustering**: Any hat tiling decomposes into H, T, P, F metatiles (verified across
   all 188 surroundable 2-patches)
2. **Forced composition**: Starting from any metatile, forced deductions uniquely determine
   its containing supertile. The "PP configuration" (two P tiles in the same orientation) is
   the key impossible configuration that eliminates cases.
3. **Unique hierarchy**: Composition iterates for all n, yielding a unique infinite hierarchy
   incompatible with translation symmetry.

### 6.3 Golden Ammann Bars (Akiyama-Araki)

An independent proof technique for the turtle = Tile(sqrt(3), 1) [4]:

**Golden Ammann Bars (GABs)** are markings on each tile that must extend across tile
boundaries to form infinite lines (proved by exhaustive angle analysis). These lines form
a **Kagome lattice** (trihexagonal tiling, vertex configuration 3636).

The frequency q of GABs in any direction satisfies [4]:

```
q^2 - q + 1/5 = 0
```

yielding `q = (5 +/- sqrt(5))/10` -- both irrational. Since any periodic tiling would force
rational frequency, periodicity is impossible.

This proof reveals aperiodicity as an **arithmetic constraint**: the quadratic irrationality
involving sqrt(5) arises from the exact ratio of fore-to-rear GAB lengths (1:4), combined
with the bijection between flipped tiles and GAB crossings [4].

**Connection to Sturmian words:** The proof uses **central words** (palindromes from the
theory of Sturmian sequences) with slope `alpha = (5 - sqrt(5))/10 = 1/(1 + tau^2)`, where
`tau` is the golden ratio. The continued fraction `[3, 1, 1, 1, ...]` (eventually all 1s)
places this in the class of golden-ratio-related noble numbers [4].

### 6.4 The Irrationality Paradigm

Across all proofs, the same pattern emerges: **aperiodicity is forced by irrational ratios**.

- In the hat: the inflation factor phi^2 is irrational
- In the spectre: the area scaling `4 + sqrt(15)` is irrational
- In the Ammann bar proof: the frequency (5 +/- sqrt(5))/10 is irrational
- A periodic tiling would force these ratios to be rational (as ratios of tile counts in a
  fundamental domain), creating a contradiction

---

## 7. Historical Context: Wang Tiles to Monotiles

### 7.1 The Domino Problem and Undecidability

Hao Wang (1961) posed the **domino problem**: given a finite set of square tiles with colored
edges (matched by translation only), can they tile the plane? He showed this is decidable
if and only if no aperiodic tile set exists. His **Fundamental Conjecture** -- that no
aperiodic set exists -- was refuted by his student Robert Berger (1966), who constructed an
aperiodic set of 20,426 Wang tiles [5].

The undecidability connection is deep: Wang tiles can simulate Turing machines, so the domino
problem encodes the halting problem [5].

### 7.2 The Race to Minimize

| Year | Size | Author(s)          |
|------|------|--------------------|
| 1966 | 20,426 | Berger           |
| 1968 | 104  | Berger (improved)  |
| 1968 | 92   | Knuth              |
| ...  | 56, 52, 40, 35, 34, 32, 24, 16 | Various |
| 1996 | 13   | Kari-Culik         |
| 2021 | **11** | Jeandel-Rao (proven minimal) |

Relaxing from squares to arbitrary polygons and allowing rotations/reflections: Penrose
(1970s) achieved **2 tiles**. The Taylor-Socolar tile (2010) achieved **1 tile** but was not
simply connected. The hat (2023) is the first simply connected aperiodic monotile [5].

### 7.3 Key Conceptual Progression

The evolution reveals a deepening understanding of how local constraints force global order
[5]:

| Tile Set | Local Mechanism | Global Consequence |
|----------|----------------|-------------------|
| Wang tiles | Edge-color matching | Undecidability; some sets force aperiodicity |
| Penrose | Edge matching + line continuation | 10-fold symmetric aperiodic order |
| Taylor-Socolar | Edge lines + next-nearest-neighbor flags | Hierarchical model sets |
| Hat | Geometric shape alone | Nonstone substitution with golden-ratio inflation |
| Spectre | Shape + chirality (curved edges) | Strictly chiral aperiodic order |

---

## 8. Hierarchical Structure Forcing

### 8.1 The General Strategy

Goodman-Strauss [6] systematized the construction of aperiodic tile sets through three steps:

1. **Tiles force hierarchical decomposition**: Matching rules ensure every tiling decomposes
   into a unique nested hierarchy of supertiles
2. **Hierarchical tilings are non-periodic**: The unique growing hierarchy at each level
   prevents translational symmetry
3. **The tile set admits tilings**: By compactness (Extension Theorem / Koenig's Lemma),
   tiles that form arbitrarily large configurations can tile the entire plane

### 8.2 Industrial-Scale Construction

From domino tiles (2x1 rectangles), Goodman-Strauss constructed [6]:

- **T_1**: 27 tiles yielding 9 aperiodic subsets
- **T_2**: 211 tiles yielding **25,380** hierarchically distinct aperiodic subsets

The construction uses a four-channel edge-marking system encoding orientation, sidedness,
hierarchical control, and orientation refinement. The Klein four-group `Z_2 + Z_2` (symmetry
group of the domino) acts on markings via nim addition [6].

### 8.3 Local-to-Global Forcing Mechanism

The enforcement operates through layers of emergent structure [6]:

1. **Edge matching** (local): adjacent tiles have complementary markings
2. **Block formation** (local consequence): markings force tiles into 3x7 domino blocks
3. **Supertile assembly** (emergent): blocks assemble into marked supertiles
4. **Orientation control**: channel markings select specific substitution systems
5. **Infinite hierarchy** (global): the process iterates to all levels

The **local derivation** Phi bridges the gap: a finite lookup table maps matching-rule patches
to substitution-rule patches, making the correspondence computable in constant time per
tile [6].

### 8.4 Matching Rules as a Universal Mechanism

**Goodman-Strauss theorem [7]:** Every geometric substitution tiling of R^d (d > 1) can be
enforced with finite matching rules, subject to a mild "sibling edge-to-edge" condition. This
closes the loop: substitution <--> matching rules <--> aperiodicity.

---

## 9. Connections to Error Correction

### 9.1 Penrose Tilings as Quantum Error-Correcting Codes

Li and Boyle [8] proved that two classical properties of Penrose tilings -- **local
indistinguishability** and **local recoverability** -- are exactly the properties needed for
a quantum error-correcting code (QECC) when tilings are promoted to quantum states via
superposition.

**Code construction [8]:** For each equivalence class [T] of Penrose tilings (under Euclidean
transformations), define:

```
|Psi_[T]> = integral dg |gT>
```

These orbit states form an orthogonal basis for a code space C that corrects arbitrary errors
in any finite region K.

### 9.2 The Two Pillars

| Tiling Property | QECC Property |
|----------------|---------------|
| **Local indistinguishability**: any finite patch appears in every tiling with the same frequency | **Code state indistinguishability**: reduced density matrix rho_K is the same for all code states |
| **Local recoverability**: any finite region can be uniquely recovered from its complement | **Error correctability**: erasure of any finite region K can be corrected |

The verification reduces to checking the Knill-Laflamme conditions [8]:
- Off-diagonal: distinct tiling classes that agree on K^c must agree globally (recoverability)
- Diagonal: rho_K = integral dg |gT>_K <gT|_K is T-independent (indistinguishability)

### 9.3 Quantitative Properties

**Continuum code:** Corrects arbitrary errors in ANY finite region, regardless of size [8].

**Discrete Fibonacci code:** For a cyclic string of length `k_0*f_n + k_1*f_{n+1}` (where
f_n are Fibonacci numbers), the code corrects errors in any contiguous region of length up to
`f_n + 1`. The substitution matrix `M = [[1,1],[1,0]]` with Perron eigenvalue phi determines
exact patch frequencies via its dominant eigenvector [8].

**Ammann-Beenker torus code:** A 4-dimensional code space on the torus (analogous to the
toric code). After n inflations, corrects erasures of any disk of radius `Theta((1+sqrt(2))^n)`,
with linear size also `Theta((1+sqrt(2))^n)` [8].

**Entanglement entropy:** `S(n) = log(n) + Theta(1)` -- intermediate between area law
(S ~ const, topological codes) and volume law (S ~ n), similar to critical systems [8].

### 9.4 Structural Parallels with the Toric Code

| Toric Code | Penrose Tiling QECC |
|------------|-------------------|
| Superpositions of loop configurations | Superpositions of tiling configurations |
| Information in loop topology | Information in global tiling geometry |
| 4D code space (2 torus cycles) | 4D code space (4 initial AB tilings) |
| Long-range entangled | Long-range entangled |
| Cannot prepare with local circuits | Cannot prepare with local circuits |

### 9.5 Applicability to Hat/Spectre Tilings

The framework in [8] applies to **any** substitution tiling satisfying local
indistinguishability and local recoverability. For hat/spectre tilings:

- **Local indistinguishability** holds by the same Perron-Frobenius arguments (substitution
  rules determine unique patch frequencies)
- **Local recoverability** should follow from the unique hierarchical supertile structure
  (analogous to Ammann line extension for Penrose)

Establishing these properties rigorously for the hat/spectre would immediately yield new
QECCs based on monotile tilings.

---

## 10. Toward Cryptographic Applications

The mathematical structures surveyed here suggest several potential avenues for cryptographic
primitive design:

### 10.1 Hard Problems from Aperiodic Tilings

**Tiling decision problems.** The undecidability of the domino problem [5] suggests that
tiling-related decision problems may provide hard instances for cryptographic reductions.
Whether monotileability of specific groups is undecidable remains open [3, Question 34].

**Local-to-global gap.** Finite patches reveal nothing about global tiling identity (local
indistinguishability), yet global structure is rigidly determined. This gap between local
information and global structure is analogous to the structure exploited by lattice-based
cryptography.

### 10.2 Algebraic Structures

**The Coxeter group Gamma** [3] provides a concrete algebraic setting. The Cucaracha
(16-element subset of Gamma) encodes aperiodic tiling structure in group-theoretic terms.
Operations in Gamma = `<alpha, beta, gamma | alpha^2, beta^2, gamma^2, (alpha*beta)^6,
(beta*gamma)^3, (alpha*gamma)^2>` are efficiently computable, but recovering global tiling
information from local data may be hard.

**Substitution matrices** with Pisot eigenvalues provide algebraic number fields (Q(sqrt(5))
for hat tilings, Q(sqrt(15)) for spectre tilings) that could serve as the basis for
number-theoretic constructions.

### 10.3 Hierarchical Substitution as One-Way Structure

Substitution (inflation) is easy: apply the local rule to each tile. Deflation (recovering
the previous level) requires global context -- one must identify supertile boundaries from
local information. This asymmetry between inflation and deflation could potentially be
exploited as a one-way function.

The spectre's **handedness reversal** under substitution adds another layer: the substitution
map doesn't preserve orientation, creating a Z_2-graded structure on the tiling space [2].

### 10.4 Error-Correcting Properties

The QECC construction [8] demonstrates that aperiodic tilings naturally encode information
with error-correcting properties. The logarithmic entanglement entropy `S(n) = log(n) +
Theta(1)` suggests a code family with interesting parameters that differ from both
topological codes and random codes.

### 10.5 Irrational Frequency Ratios

The irrational ratios forced by aperiodicity (phi for the hat, `4 + sqrt(15)` for the
spectre, `(5 +/- sqrt(5))/10` for Ammann bar frequencies) could provide trapdoor-like
structure: knowing the exact algebraic irrationality allows computing tile frequencies, but
extracting the irrationality from approximate frequency data is a number-theoretic problem.

### 10.6 Subshift of Finite Type Encoding

Representing tilings as elements of a subshift of finite type [3, 7] provides a symbolic
dynamics framework amenable to coding theory. The complexity function p(n) of the tiling's
symbolic dynamics (with Sturmian sequences achieving minimal complexity p(n) = n + 1 [4, 7])
characterizes the information-theoretic content of the tiling.

---

## 11. Open Questions

### From the Literature

1. **Strongly aperiodic geometric monotile:** Does there exist a monotile whose cotilers all
   have trivial stabilizers? [3, Question 33]

2. **Undecidability of monotileability:** Is it undecidable whether a finite monotile tiles
   the Coxeter group Gamma? [3, Question 34]

3. **Minimal aperiodic marked hexagons:** Can the 9 marked hexagons of the spectre
   construction be reduced? Preliminary work suggests 5 may suffice [2].

4. **Cut-and-project structure:** Does a closed path in 4 or 6 dimensions project to the
   Tile(a,b) family? (Suggested by Smith et al. [1]; partially resolved by Baake-Gahler-Sadun
   who identified hat tilings as model sets)

5. **Full characterization of hat tiling space:** Do tilings with infinite "fault lines" on
   supertile boundaries at all levels exist? [1]

### For Cryptographic Exploration

6. Can the local-to-global gap (local indistinguishability + global uniqueness) be formalized
   as a hard search problem suitable for cryptographic reductions?

7. Can substitution matrices with Pisot eigenvalues define lattice problems in Z[phi] or
   Z[sqrt(15)] with useful hardness properties?

8. Does the deflation problem (recovering level-(n-1) structure from level-n) have
   provable computational hardness?

9. Can the spectre's orientation-reversal substitution define a cryptographic hash function
   with the Z_2-graded structure providing collision resistance?

10. Can the Cucaracha's structure in the Coxeter group Gamma support a group-based
    cryptographic scheme (analogous to braid group or Artin group cryptography)?

---

## 12. References

1. Smith, D., Myers, J.S., Kaplan, C.S., Goodman-Strauss, C. "An Aperiodic Monotile."
   *Combinatorial Theory* 4(1), #6, 2024. arXiv:2303.10798.
   `papers/smith-et-al-2023-an-aperiodic-monotile.pdf`

2. Smith, D., Myers, J.S., Kaplan, C.S., Goodman-Strauss, C. "A Chiral Aperiodic Monotile."
   *Combinatorial Theory* 4(2), #13, 2024. arXiv:2305.17743.
   `papers/smith-et-al-2023-a-chiral-aperiodic-monotile.pdf`

3. Coulbois, T., Gajardo, A., Guillon, P., Lutfalla, V.H. "Aperiodic Monotiles: From
   Geometry to Groups." arXiv:2409.15880, 2024.
   `papers/coulbois-et-al-2024-aperiodic-monotiles-geometry-to-groups.pdf`

4. Akiyama, S., Araki, Y. "An Alternative Proof for an Aperiodic Monotile."
   arXiv:2307.12322, 2025.
   `papers/alternative-proof-aperiodic-monotile-2023.pdf`

5. Bruneau, O., Whittaker, M.F. "From Wang Tiles to the Hat and Spectre Aperiodic
   Monotiles." arXiv:2310.06759, 2024.
   `papers/bruneau-whittaker-2023-wang-tiles-to-hat-spectre.pdf`

6. Goodman-Strauss, C. "Lots of Aperiodic Sets of Tiles." *Journal of Combinatorial Theory,
   Series A*, 2016. arXiv:1608.07165.
   `papers/goodman-strauss-2016-lots-of-aperiodic-sets.pdf`

7. Frank, N.P. "A Primer of Substitution Tilings of the Euclidean Plane." *Expositiones
   Mathematicae* 26(4), 295-326, 2008. arXiv:0705.1142.
   `papers/frank-2008-primer-substitution-tilings.pdf`

8. Li, Z., Boyle, L. "The Penrose Tiling is a Quantum Error-Correcting Code."
   arXiv:2311.13040, 2024.
   `papers/penrose-tiling-quantum-error-correcting-code-2023.pdf`
