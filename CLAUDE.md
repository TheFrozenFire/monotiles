# monotiles

## Project Documentation

| File | Purpose |
|------|---------|
| `README.md` | Project overview — what this is, what's built, how to run it |
| `RESEARCH.md` | Literature survey — mathematical foundations from published papers |
| `RESEARCH_SUMMARY.md` | Conversational walkthrough of RESEARCH.md for quick orientation |
| `SAFETILES.md` | Parameter guide for choosing tiling systems in experiments |
| `FINDINGS.md` | Experimental results — things we measured, not things we read |
| `WISDOM.md` | Process insights — subtle lessons from implementation and formalization that papers and code don't surface |

When writing to these docs:
- **RESEARCH.md**: only cite published results with references. No original experiments.
- **FINDINGS.md**: concrete data tables and measurements. Include issue numbers. State what was measured and what was concluded.
- **WISDOM.md**: "things the paper doesn't tell you." Subtle implementation/process insights. No raw data — explain *why* something is surprising or non-obvious.

## Codebase

Rust workspace with 5 crates:

| Crate | Role |
|-------|------|
| `domain` | Core algebra: Coxeter group, Cucaracha, fields, matrix, group crypto |
| `tiling` | Metatile systems: substitution, deflation, geometry, recovery, one-way, gap, vulnerability |
| `analysis` | Spectral analysis, Sturmian words |
| `iop` | Tiling-based interactive oracle proof (hierarchy, prover, verifier) |
| `cli` | All subcommands — the only binary crate |

Three tiling systems are supported: `hat` (4 types: H/T/P/F), `spectre` (2 types: Spectre/Mystic), `hat-turtle` (4 types).

## CLI Subcommands

Every experiment is a CLI subcommand. Run with `RUST_LOG=info` for output (all output goes through `tracing`).

```
cargo run --release -- verify-coxeter          # Coxeter group relation checks
cargo run --release -- cucaracha               # Display Cucaracha elements
cargo run --release -- inflate H --levels 5    # Substitution growth
cargo run --release -- inflate Spectre -S spectre --levels 5
cargo run --release -- sturmian --terms 100    # Sturmian word
cargo run --release -- matrix                  # Substitution matrix spectral analysis
cargo run --release -- fields                  # Field extension verification
cargo run --release -- deflate H --levels 3    # Deflation demo
cargo run --release -- recover --levels 3 -r 1.5  # Hole recovery
cargo run --release -- prove H --depth 4 --queries 8  # IOP prove/verify
cargo run --release -- oneway H --depth 3 -r 5        # One-way analysis
cargo run --release -- oneway Spectre -S spectre --depth 3 -r 5
cargo run --release -- gap --depth 3 -r 5              # Local-to-global gap
cargo run --release -- vulnerability --depth 3 --erasure-trials 100
cargo run --release -- group-crypto --experiment all --max-size 5 --trials 10
cargo run --release -- group-crypto --experiment coset --max-size 6 --trials 3
```

## Exploration Process

This is a research project. The workflow is:

1. **Issue first.** Every exploration starts as a GitHub issue with a hypothesis, approach, and key questions. Issues are the source of truth for what we're investigating and why.

2. **Implement as a CLI subcommand.** New experiments get a module in the appropriate crate and a subcommand in `cli`. All output through `tracing` (not `println`). Use `info!` for primary results, `debug!` for progress, `trace!` for high-frequency instrumentation.

3. **Run, observe, instrument.** Run experiments at small sizes first. If something is slow, don't just wait — add tracing instrumentation, run again with a short timeout, and diagnose the bottleneck. Check output proactively.

4. **Document findings.** Experimental results go in FINDINGS.md with data tables and issue references. Process insights go in WISDOM.md. Close the GitHub issue with a summary comment linking to the docs.

5. **Negative results are results.** If an approach doesn't work, document why. Close the issue. This is how we've ruled out one-way deflation (#5), LWE-style gap hardness (#6), group cryptography (#8), and substitution trapdoor signatures (#11).

6. **Findings suggest new issues.** After documenting results, look at what the data implies. Create follow-up issues for the next questions. Annotate existing open issues with relevant new information.

## Issue Conventions

- Closed issues have a summary comment with the conclusion and a link to FINDINGS.md or WISDOM.md
- Open issues represent live hypotheses or planned experiments
- When findings invalidate an open issue's premise, close it with an explanation

To get the full issue landscape:

```
gh issue list --repo TheFrozenFire/monotiles --state all --json number,title,state,comments --jq '.[] | "#\(.number) [\(.state)] \(.title) (\(.comments | length) comments)"' | sort -t'#' -k2 -n
```

## Key Patterns

### xorshift64 PRNG
Deterministic RNG used in group crypto experiments. Pattern from `vulnerability.rs`: shifts 13, 7, 17. Seed with a hex constant like `0xDEAD_BEEF_u64`.

### CoxeterElement doesn't implement Ord
Use `coxeter_sort_key(e) -> (i64, i64, u8, bool)` for deterministic ordering.

### Node budgets for backtracking
When a backtracking search might explode, add a node budget (e.g., 10M) and return a `budget_exceeded` flag alongside results. Don't let experiments hang.

### Tiling system abstraction
The `TilingSystem` trait in `tiling::systems` abstracts over hat/spectre/hat-turtle. Use `resolve_system(name)` in CLI, pass `&dyn TilingSystem` to analysis functions.

### Test structure
Tests live in `#[cfg(test)] mod tests` within each module. Integration-first: test the public API, not internals. Currently 64 tests across the workspace.
