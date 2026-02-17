# monotiles

What happens when you take the first aperiodic monotile ever discovered and try to build cryptographic primitives from it?

In 2023, Smith, Myers, Kaplan, and Goodman-Strauss found the "hat" — a single shape that tiles the infinite plane but only aperiodically. No translational symmetry, ever. The tiling is forced into a hierarchical substitution structure with irrational frequency ratios, local indistinguishability, and a curious asymmetry: building the hierarchy up is easy (local rules), but recovering it from a patch requires global context.

This project is an exploration of that structure. We're asking: do the mathematical properties of aperiodic monotile tilings — recognizability, local recoverability, hierarchical deflation, algebraic irrationals, the gap between local information and global structure — give rise to anything useful in cryptography or coding theory?

We don't know yet. Some of the directions look promising. Some are probably dead ends. This repo is the laboratory.

## What's Built

The foundation is a Rust workspace with machine-checked Rocq (Coq) proofs alongside it. Everything compiles, everything is tested, and the mathematical claims that matter are formally verified.

### The Tiling Engine

The full hat metatile system — four tile types (H, T, P, F) with edge-matching rules, 29-child inflation, supertile composition, geometric patch generation, and both inflation and deflation. You can generate a level-n patch from any seed metatile and watch the tile counts grow by the Perron eigenvalue (~6.854x per level).

The recognition system identifies supertile structure from local data: given a patch of metatiles, it determines which children belong to which supertile. This is the computational core of "recognizability" — the property that makes the tiling locally testable.

Local recoverability is implemented and tested: erase a finite region from a valid tiling, and the system reconstructs the missing tiles from the surrounding context alone. This is the error-correction property that connects to quantum codes.

### The Algebra

The triangle Coxeter group Gamma (type [6,3,2]) with normal-form arithmetic, the Cucaracha (a 16-element aperiodic group monotile), exact field extensions Q(sqrt(5)) and Q(sqrt(15)) for algebraic number arithmetic, and the 4x4 substitution matrix with its full spectral theory — Perron-Frobenius eigenvectors, Cayley-Hamilton inverse (det(M) = -1, so M is in GL(4,Z)), and tile frequency computation.

Sturmian word generation for the hat tiling's symbolic dynamics, with the slope (5 - sqrt(5))/10 and its continued fraction [0; 3, 1, 1, 1, ...] producing a generalized Fibonacci sequence.

### The Rocq Proofs

Seven proof files (~2,400 lines) formally verify the claims that matter most:

- **Recognizability**: the substitution map is invertible on the tiling space — supertile decomposition is unique
- **Local recoverability**: erased tiles are uniquely determined by their complement
- **Spectral properties**: eigenvalues, eigenvectors, and the Cayley-Hamilton identity for the substitution matrix
- **Cucaracha aperiodicity**: the 16-element tile has trivial stabilizer under the point group action

These aren't just "the code works" — they're machine-checked proofs that the mathematical structure is what we think it is.

## The Toy: A Tiling-Based IOP

The `iop` crate implements a proof-of-concept interactive oracle proof that uses the hat tiling's substitution hierarchy as a folding domain — the role that roots of unity play in FRI/STARKs.

The analogy:

| FRI | Tiling IOP |
|-----|-----------|
| Domain: roots of unity | Domain: metatiles in a hat tiling patch |
| Folding: polynomial degree-halving | Folding: deflation via type-stratified random combination |
| Consistency: f(x) and f(-x) yield same folded value | Consistency: child values combine to supertile value |
| Rounds: log_2(n) | Rounds: log_{phi^4}(n) |

The prover commits to field values on base tiles, folds upward through the hierarchy using Fiat-Shamir challenges (one random coefficient per metatile type per round), and the verifier spot-checks folding consistency via Merkle openings. Blake3 for hashing, BLS12-381 Fr for field arithmetic.

It works — honest proofs verify, tampered proofs are rejected — but it achieves only ~6 bits of query soundness with current parameters. The domain is small (~3000 tiles at depth 4) and there's no proximity gap analogous to FRI's correlated agreement theorem. The field-level soundness from Schwartz-Zippel is strong (~253 bits), but per-query detection probability against a cheater who confines inconsistency to one ancestor chain is ~1/441.

The interesting open question is whether the substitution structure has a natural proximity gap — whether inconsistency amplifies through folding rounds the way it does in Reed-Solomon codes — or whether the path forward is composing the tiling domain with polynomial commitments to import algebraic proximity gap.

## What We're Exploring

### Quantum Error-Correcting Codes

Li and Boyle (2024) proved that Penrose tilings are quantum error-correcting codes. The key properties are local indistinguishability (any finite patch appears in every valid tiling with the same frequency) and local recoverability (any finite erasure is correctable from the complement). We've formally proved local recoverability for the hat tiling. The remaining work is constructing the stabilizer code and characterizing its parameters.

### The Local-to-Global Gap

Aperiodic tilings have a striking structural property: any finite patch of radius r appears everywhere with the same frequency (you can't tell where you are from local information), yet the global tiling is rigidly determined. This gap between local information and global structure is reminiscent of what lattice-based cryptography exploits. Can it be formalized as a computationally hard problem?

### One-Way Substitution

Inflation is local and O(n). Deflation requires global context — identifying supertile boundaries from tile data. Is this asymmetry computational (a genuine one-way function) or just informational (hard for small patches, easy with enough context)?

### Code-Based Signatures

The substitution matrix M is in GL(4,Z) with a clean integer inverse (M^{-1} = M^3 - 7M^2 + 7I). The composition map — which of the 22 assigned children belong to which supertile — acts as a structural trapdoor. Can this support a signature scheme in the style of WAVE or CROSS?

### Group Cryptography

The Cucaracha lives in the Coxeter group Gamma, which is virtually abelian (probably too tame for cryptographic hardness on its own). But the tiling constraint adds combinatorial structure that might compensate. The cotiler recovery problem and exact cover decomposition are worth investigating.

See [RESEARCH.md](RESEARCH.md) for the full survey and [open issues](https://github.com/TheFrozenFire/monotiles/issues) for specific research threads.

## Getting Started

### Build and Test

```bash
cargo test --workspace
```

172 tests across all crates. Takes a few seconds.

### Run the IOP Demo

```bash
cargo run -- prove H --depth 4 --queries 8
```

Generates a tiling hierarchy from an H seed (3025 base tiles, 5 levels), proves, and verifies. You'll see timing and proof size.

### Other Commands

```bash
cargo run -- inflate H --levels 6    # Watch tile counts grow by ~6.854x per level
cargo run -- matrix                   # Substitution matrix, eigenvalues, Cayley-Hamilton
cargo run -- deflate H --levels 3     # Generate patch, deflate, inflate round-trip
cargo run -- recover --levels 3       # Erase a region and recover it
cargo run -- sturmian --terms 100     # Sturmian word with complexity p(n) = n+1
cargo run -- verify-coxeter           # Check all 6 Coxeter group relations
cargo run -- cucaracha                # Display the 16-element aperiodic monotile
cargo run -- fields                   # Verify Q(sqrt(5)) and Q(sqrt(15)) arithmetic
```

### Check the Rocq Proofs

Requires Rocq 8.19+ (formerly Coq).

```bash
cd rocq
coqc -Q . Monotiles CoxeterGroup.v
coqc -Q . Monotiles Substitution.v
coqc -Q . Monotiles Recognizability.v
coqc -Q . Monotiles LocalRecoverability.v
coqc -Q . Monotiles HatSpectral.v
coqc -Q . Monotiles Sturmian.v
coqc -Q . Monotiles Cucaracha.v
```

## Where to Look

**If you're interested in the tiling math**: start with `crates/tiling/src/metatile.rs` (the substitution rules) and `crates/tiling/src/recognition.rs` (how local data determines global structure). The Rocq proof `rocq/Recognizability.v` is the formal backbone.

**If you're interested in the IOP**: `crates/iop/src/prover.rs` and `crates/iop/src/verifier.rs` are the protocol. `crates/iop/src/fold.rs` is where the tiling structure meets the folding operation. The integration tests in `crates/iop/tests/iop_integration.rs` show honest acceptance, tamper detection, and hierarchy verification against the substitution matrix.

**If you're interested in the spectral theory**: `crates/analysis/src/spectral.rs` has the eigenvalue/eigenvector computation, GAB frequency equation, and matrix inverse. `WISDOM.md` explains what the formalization taught us that the code alone couldn't show.

**If you're interested in the group theory**: `crates/domain/src/coxeter.rs` for the Coxeter group arithmetic, `crates/domain/src/cucaracha.rs` for the aperiodic group monotile.

## References

1. Smith, Myers, Kaplan, Goodman-Strauss. "An Aperiodic Monotile." 2023.
2. Smith, Myers, Kaplan, Goodman-Strauss. "A Chiral Aperiodic Monotile." 2023.
3. Coulbois, Gajardo, Guillon, Lutfalla. "Aperiodic Monotiles: From Geometry to Groups." 2024.
4. Akiyama, Araki. "An Alternative Proof for an Aperiodic Monotile." 2023.
5. Bruneau, Whittaker. "From Wang Tiles to the Hat and Spectre Aperiodic Monotiles." 2023.
6. Goodman-Strauss. "Lots of Aperiodic Sets of Tiles." 2016.
7. Frank. "A Primer of Substitution Tilings of the Euclidean Plane." 2008.
8. Li, Boyle. "The Penrose Tiling is a Quantum Error-Correcting Code." 2024.
