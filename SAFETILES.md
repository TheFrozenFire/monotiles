# SafeTiles: Tiling System Parameter Guide

How to pick a tiling system and understand what each parameter controls for recoverability and vulnerability analysis.

## Available Systems

| System | Tile Types | Inflation Children | Boundary Children | Inflation Factor | det(M) |
|--------|-----------|-------------------|-------------------|-----------------|--------|
| **Hat** | 4 (H/T/P/F) | 29 | 7 | phi^4 ~ 6.854 | -1 |
| **Spectre** | 2 (Spectre/Mystic) | 15 | 0 | 4+sqrt(15) ~ 7.873 | 1 |
| **Hat-turtle** | 4 (H/T/P/F) | 29 | 7 | phi^4 ~ 6.854 | -1 |

## System Parameters

### Number of Tile Types (`num_types`)

The count of distinct tile types in the substitution system.

- **Hat**: 4 types (H, T, P, F). More types create richer local context for deflation, but also create more potential swap vulnerabilities between supertile types with similar compositions.
- **Spectre**: 2 types (Spectre, Mystic). Fewer types means less local information per tile, but the larger supertile sizes compensate.
- **Hat-turtle**: 4 types, identical to hat.

**What it controls**: The dimensionality of the composition matrix and the information content of each tile observation. More types = more bits of information per tile = easier local determination, but also a larger space of potential swap confusions.

### Composition Matrix (`composition`)

The substitution rule: `composition[i][j]` = count of type-j tiles in supertile type i.

**Hat**:
```
H' = 3H + 1T + 3P + 3F  (10 children)
T' = 1H                   (1 child)
P' = 2H + 0T + 1P + 2F   (5 children)
F' = 2H + 0T + 1P + 3F   (6 children)
```

**Spectre**:
```
Spectre' = 7 Spectre + 1 Mystic  (8 children)
Mystic'  = 6 Spectre + 1 Mystic  (7 children)
```

**What it controls**: Everything downstream. The composition matrix determines:
- Whether type-bag decomposition is unique (via matrix invertibility)
- Which supertile pairs can be confused by single-tile swaps
- Position criticality scores
- Minimum determining set sizes
- Tile frequencies at scale (via Perron-Frobenius eigenvector)

### Matrix Determinant (`det(M)`)

The determinant of the composition matrix over the integers.

- **Hat**: det(M) = -1. The matrix is in GL(4,Z) -- it has an exact integer inverse (M^{-1} = M^3 - 7M^2 + 7I). This means type-bag decomposition is always unique: given any valid bag of tile types, there is exactly one way to partition them into supertiles.
- **Spectre**: det(M) = 1. Also in GL(2,Z) with an integer inverse. Decomposition is unique.

**What it controls**: Whether type counts alone uniquely determine the supertile partition. |det(M)| = 1 guarantees uniqueness. A larger determinant would mean multiple valid decompositions exist for the same type counts, making deflation fundamentally ambiguous even with global information.

### Inflation Factor (Perron Eigenvalue)

The dominant eigenvalue of the composition matrix. Controls the growth rate of tile count per substitution level.

- **Hat**: phi^4 = (7 + 3*sqrt(5))/2 ~ 6.854. At depth d, the base level has ~6.854^d tiles.
- **Spectre**: 4 + sqrt(15) ~ 7.873. Slightly faster growth, so spectre hierarchies are larger at the same depth.

**What it controls**: How quickly the tiling grows with depth. Higher inflation factor means more base tiles per level of hierarchy, which affects:
- The statistical power of erasure experiments at a given depth
- The computational cost of analysis
- How many tiles are available for local context at each level

### Supertile Sizes

The number of children assigned to each supertile type.

**Hat**: H'=10, T'=1, P'=5, F'=6 (22 assigned + 7 boundary = 29 total)

**Spectre**: Spectre'=8, Mystic'=7 (15 assigned, 0 boundary)

**What it controls**: Larger supertiles provide more internal structure for determination, but also more positions where erasure could occur. The variance in supertile sizes is important: T' with only 1 child is trivially identifiable by size alone, while H' with 10 children has redundancy that enables partial erasure tolerance.

### Boundary Children

Tiles in the inflation rule that are not assigned to any supertile. They sit at supertile boundaries and are shared between adjacent supertiles at the next level.

- **Hat**: 7 boundary children (indices 5, 12, 13, 14, 17, 18, 19). These are the "glue" between supertiles.
- **Spectre**: 0 boundary children. All inflation children belong to a supertile.

**What it controls**: Boundary children affect how information propagates between supertiles during deflation. With boundary children, adjacent supertiles share tiles, which provides cross-supertile context. Without boundary children (spectre), each supertile is self-contained, and inter-supertile information must come from geometric adjacency rather than shared tiles.

### Orientation Reversal (`reverses_orientation`)

Whether inflation reverses tile orientation at each level.

- **Hat**: false. Tiles maintain orientation through substitution.
- **Spectre**: true. Each level of substitution mirrors the tiles.

**What it controls**: In systems with orientation reversal, alternating levels have opposite chirality. This means geometric operations (like deflation from a physical patch) must track whether the current level is "normal" or "reversed". For the combinatorial analysis (one-way, vulnerability), this flag has no effect -- the composition matrix is the same regardless of orientation.

### Edge Ratio (`edge_ratio`, hat-turtle only)

A continuous parameter interpolating between the hat shape (a/b = 1/sqrt(3) ~ 0.577) and the turtle shape (a/b = sqrt(3) ~ 1.732).

**What it controls**: Only the geometric shape. The combinatorial structure -- compositions, child assignments, adjacency, inflation rules -- is identical across the entire hat-turtle continuum. All SafeTiles analysis results are invariant under edge ratio changes. This is confirmed by tests showing hat and hat-turtle produce identical one-way and vulnerability analysis results.

**Implication**: The edge ratio is irrelevant for SafeTiles evaluation. The hat and hat-turtle systems are combinatorially equivalent.

## Vulnerability Parameters

### Swap Vulnerability

A pair of supertile types whose compositions differ by exactly one tile in exactly one type component. An adversary who can insert or remove a single tile could change one supertile type into the other.

**Hat**: One swap pair exists: P'↔F'. Their compositions differ by exactly 1 F-tile:
```
P' = 2H + 1P + 2F  (5 children)
F' = 2H + 1P + 3F  (6 children)
```
Adding one F-tile to a P' supertile makes it look like an F' (by type counts).

**Spectre**: One swap pair exists: Spectre'↔Mystic'. Their compositions differ by exactly 1 Spectre-tile:
```
Spectre' = 7S + 1M  (8 children)
Mystic'  = 6S + 1M  (7 children)
```

**What it controls**: Swap pairs identify the minimum-effort attack surface. If no swap pairs exist, an adversary would need to change at least two tiles to convert one supertile type into another, making attacks harder to execute and easier to detect.

**Observation**: Both current systems have exactly one swap pair. This appears to be a consequence of having compositions that form a "staircase" differing by one tile at a time. A system where all compositions differ by 2+ tiles in every component would have no swap vulnerability.

### Position Criticality

For each child position within a supertile, the criticality score (0 or 1) indicates whether erasing that position creates ambiguity about the supertile's type.

- **Score 0 (redundant)**: Removing this child, the remaining children still uniquely identify the supertile type (no other supertile type could match by adding one tile).
- **Score 1 (critical)**: Removing this child, some other supertile type could be reached by adding a single tile of the appropriate type.

**Hat**: In the H' supertile (10 children), the F-type children at certain positions are critical because removing one F could make the remaining composition look like P' + 1 tile. T' (1 child) has a redundant position because no other supertile has size 1.

**What it controls**: Critical positions are the tiles an adversary would target for maximum ambiguity. The fraction of critical positions across all supertile types measures the system's surface area for single-tile erasure attacks.

### Minimum Determining Set

The smallest subset of child positions whose types uniquely identify the supertile among all types. If you can observe at least this many well-chosen positions, you know which supertile type you're in.

**What it controls**: The minimum amount of information needed to resolve supertile identity under partial erasure. Smaller determining sets mean the system is more robust -- fewer observations suffice to remove ambiguity.

**Hat T'**: Determining set size 0 -- even with no children observed, the fact that a supertile has exactly 1 child uniquely identifies it as T'. (The size itself is determining.)

Note: The determining set analysis considers type counts at selected positions, not position indices. Two positions of the same type are interchangeable for this analysis.

### Determination Radius

The minimum BFS radius r such that a tile's type signature (the per-shell type counts of its r-hop neighborhood) uniquely identifies its parent supertile type.

Two adjacency models are analyzed:

1. **Full sibling adjacency**: All tiles sharing the same parent are mutually adjacent. This is the maximum-information model.
2. **Intra-supertile inflation adjacency**: Only tiles that are geometrically adjacent within their parent supertile are connected. This is the realistic geometric model.

**Hat (full sibling)**: All tiles determined at radius <= 1. T-type tiles are determined at radius 0 (their type alone is sufficient, since T' is the only supertile containing a T-tile at that frequency).

**Hat (inflation adjacency)**: All tiles determined at radius <= 4. The H' supertile is disconnected in the inflation adjacency graph (it has two components), requiring larger radius to propagate information across components.

**Spectre (full sibling)**: All tiles determined at radius <= 1.

**What it controls**: Determination radius measures the locality of deflation. Radius 1 means each tile only needs to see its immediate neighbors. Larger radius means more global context is required. A system where some tiles are never determined (radius = infinity) would have genuinely one-way substitution.

**Key finding**: Neither hat nor spectre exhibits computational one-wayness. Both are locally solvable at small radius with full sibling adjacency. The asymmetry between inflation and deflation is implementation convenience, not computational hardness.

## Analysis Parameters (CLI flags)

### `--depth` / `-d`

Number of substitution levels to build. The base level (level 0) has the most tiles.

| Depth | Hat base tiles | Spectre base tiles |
|-------|---------------|-------------------|
| 1 | 10 | 8 |
| 2 | 69 | 57 |
| 3 | 441 | 441 |
| 4 | 3,025 | 3,473 |
| 5 | 20,737 | 27,329 |
| 6 | 142,129 | 215,017 |

**What it controls**: Statistical significance of erasure experiments and the scale at which boundary effects become negligible. Depth 3 is sufficient for qualitative analysis. Depth 5-6 gives stable quantitative results. Depth 7+ (~1M tiles) is expensive but confirms asymptotic behavior.

### `--max-radius` / `-r` (oneway)

Maximum BFS neighborhood radius to test for determination. The analysis checks radii 0, 1, ..., max_radius and stops early if all tiles are determined.

**What it controls**: How far the analysis looks for local solvability. For hat with full sibling adjacency, radius 1 suffices. For inflation adjacency, radius 4-5 is needed. Setting this too low gives false "undetermined" results.

### `--erasure-trials` / `-e` (vulnerability)

Number of random erasure trials per fraction step. The erasure sweep tests fractions 0%, 10%, ..., 100%.

**What it controls**: Statistical confidence in erasure tolerance curves. 10 trials gives rough trends. 100 trials gives stable means. 1000+ is overkill for the current analysis.

### `--system` / `-S`

Selects the tiling system: `hat`, `spectre`, or `hat-turtle`.

### Seed type

The tile type to use as the top-level seed for hierarchy generation. System-dependent:
- **Hat**: H, T, P, or F (default: H)
- **Spectre**: Spectre or Mystic (default: Spectre)
- **Hat-turtle**: H, T, P, or F (default: H)

**What it controls**: The seed affects tile counts at small depths (the hierarchy is a finite subtree rooted at the seed). At large depths, the Perron-Frobenius eigenvector dominates and all seeds converge to the same frequency ratios. For most analysis, the seed choice doesn't matter.

## Comparative Summary

| Property | Hat | Spectre |
|----------|-----|---------|
| Tile types | 4 | 2 |
| Supertile sizes | 10/1/5/6 | 8/7 |
| Size variance | High (1 to 10) | Low (7 to 8) |
| Boundary children | 7 | 0 |
| Swap pairs | 1 (P'↔F') | 1 (Spectre'↔Mystic') |
| det(M) | -1 (GL(4,Z)) | 1 (GL(2,Z)) |
| Decomposition | Always unique | Always unique |
| Full-sibling det. radius | <= 1 | <= 1 |
| Inflation-adj det. radius | <= 4 | <= 1 |
| Orientation reversal | No | Yes |
| Inflation factor | ~6.854 | ~7.873 |

**Hat advantages**: More tile types provide richer local context. The high variance in supertile sizes (T' has 1 child, H' has 10) means some supertiles are trivially identifiable by size alone. 7 boundary children provide cross-supertile information flow.

**Spectre advantages**: Simpler 2-type system with more uniform supertile sizes (7 and 8). No boundary children means cleaner supertile boundaries. Slightly faster growth rate. The 2x2 composition matrix is easier to analyze algebraically.

**Hat-turtle**: Combinatorially identical to hat. The edge ratio parameter only affects geometry, not SafeTiles properties.

## What Would Make a "Better" System

Based on the parameters analyzed, an ideal tiling system for SafeTiles would have:

1. **No swap pairs**: Compositions differing by 2+ tiles in every pair, eliminating single-tile confusion attacks.
2. **Small determination radius**: All tiles determined at radius 0 or 1 with realistic adjacency.
3. **Low criticality ratio**: Few critical positions relative to total positions.
4. **Small determining sets**: Each supertile identifiable from a small fraction of its children.
5. **|det(M)| = 1**: Guaranteeing unique decomposition.
6. **Uniform supertile sizes**: Reducing variance so no supertile is disproportionately easy or hard to identify.
7. **High inflation factor**: More tiles per level means better statistical properties.

Both hat and spectre score well on most of these criteria. The main vulnerability in both is the single swap pair, which is a structural consequence of having compositions that form a near-staircase pattern.
