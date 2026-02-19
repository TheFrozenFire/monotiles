/* Issue #53: Coordinate ring of tile positions
 *
 * From crates/domain/src/coxeter.rs and crates/tiling/src/geometry.rs:
 *   - Tile positions are elements of CoxeterElement: (tx, ty, rotation, reflected)
 *   - (tx, ty) ∈ Z² with hexagonal lattice basis: e1=(1,0), e2=(1/2,√3/2) in Cartesian
 *   - rotation ∈ Z/6Z (multiples of π/3)
 *   - reflected ∈ {false, true}
 *   - The full group is Γ = Z² ⋊ D₆ (Coxeter group in normal form)
 *
 * This script identifies the coordinate ring, norm form, lattice properties,
 * and the algebraic action of the inflation map.
 */

x = 'x;
s3  = sqrt(3);
s5  = sqrt(5);
s15 = sqrt(15);

/* ── The hexagonal lattice as Eisenstein integers ────────────────────── */

print("=== Hexagonal lattice = Eisenstein integers Z[ω] ===");
/* The basis {e1=(1,0), e2=(1/2,√3/2)} generates a lattice in R² ≅ C.
 * A position (tx, ty) in hexagonal coordinates corresponds to the complex number:
 *   z = tx · 1 + ty · (1/2 + i√3/2) = tx + ty·ω
 * where ω = 1/2 + i√3/2 = e^(iπ/3), the primitive 6th root of unity.
 *
 * ω satisfies ω² - ω + 1 = 0 (minimal polynomial, since Φ₆(x) = x²-x+1). */
print("ω = e^(iπ/3) = 1/2 + i√3/2  satisfies  ω² - ω + 1 = 0");
print("Minimal polynomial of ω over Q: x² - x + 1  (6th cyclotomic polynomial Φ₆)");
print("Z[ω] = Z[x]/(x²-x+1) = ring of integers of Q(√(-3))");
print("     = Eisenstein integers  (one of the only two imaginary quadratic PIDs with units)");

/* Verify the minimal polynomial */
omega_min = x^2 - x + 1;
disc_omega = poldisc(omega_min);
print("\nDiscriminant of x²-x+1: ", disc_omega, " = -3  ✓  (field Q(√(-3)))");

/* Norm form: N(a + bω) = (a + bω)(a + bω̄) where ω̄ = 1/2 - i√3/2 = 1 - ω */
print("\nNorm form: N(a + b·ω) = a² - ab + b²");
print("  (from (a+bω)(a+b(1-ω)) = a² + ab - abω + abω - b²ω - ab + b²·(ω-ω²) + ...)");
print("  Direct computation: (a+bω)(ā+b̄ω̄)");
print("  Let z = a + b/2 + ib√3/2 (Cartesian)");
print("  |z|² = (a+b/2)² + 3b²/4 = a² + ab + b²/4 + 3b²/4 = a² + ab + b²... WAIT");
print("  Correct: |a + b·ω|² = (a+b/2)² + (b√3/2)² = a²+ab+b²/4+3b²/4 = a²+ab+b²");
print("  But the norm form of Eisenstein integers is N(a+bζ₃) = a²-ab+b² for ζ₃=e^(2πi/3)");
print("  Here ω = e^(iπ/3) and ζ₃ = e^(2πi/3) = ω²-1 (different!). Let me reconcile.");
print("");
/* The Eisenstein integers Z[ζ₃] where ζ₃ = e^(2πi/3) = -1/2+i√3/2 have norm a²-ab+b².
 * Our ω = e^(iπ/3) = 1/2+i√3/2 = -ζ₃ + 1 (since ζ₃ = -1/2+i√3/2 = ω - 1).
 * So Z[ω] = Z[ζ₃+1] = Z[ζ₃] (same ring, just a change of basis: b→b, a→a+b).
 * The norm in the ω-basis: N_ω(a+bω) = (a+b)² - (a+b)b + b² = a²+2ab+b²-ab-b²+b² = a²+ab+b²
 * In the ζ₃-basis: N_ζ₃(c+dζ₃) = c²-cd+d²
 * Change: a+bω = a+b(1+ζ₃) = (a+b)+bζ₃, so c=a+b, d=b.
 * Verify: (a+b)²-(a+b)b+b² = a²+2ab+b²-ab-b²+b² = a²+ab+b². ✓ */
print("Norm in ω-basis: N(a+bω) = a²+ab+b²  (hexagonal, always ≥ 0)");
print("Norm in ζ₃-basis: N(c+dζ₃) = c²-cd+d²  (same ring, different basis)");
print("Change of basis: a+bω = (a+b)+(b)ζ₃");
print("Both give the hexagonal norm form — equal to the squared hex distance.");

/* Verify numerically */
a = 3; b = -2;
norm_omega = a^2 + a*b + b^2;
c = a+b; d = b;
norm_zeta = c^2 - c*d + d^2;
print("\nVerify: N_ω(3-2ω) = ", norm_omega, ", N_ζ₃(", c, "+", d, "ζ₃) = ", norm_zeta, " (should match)");

/* ── Full group structure Γ = Z[ω] ⋊ D₆ ─────────────────────────────── */

print("\n=== Full Coxeter group Γ = Z[ω] ⋊ D₆ ===");
print("Tile position = (tx, ty, rotation, reflected) ∈ Z² × Z/6Z × Z/2Z");
print("= element of Γ = Z[ω] ⋊ D₆ where D₆ acts on Z[ω] by:");
print("  rotation by k·(π/3): z ↦ ω^k · z");
print("  reflection: z ↦ z̄  (complex conjugate)");
print("");
print("Group structure: |Z[ω]/nZ[ω]|, for n=7 (smallest prime that splits fully in Z[ω]):");
/* N(7) = 7² = 49 in Z[ω] since 7 ≡ 1 mod 3, so 7 splits in Z[ω] as (2+√(-3))(2-√(-3)) */
print("7 splits in Z[ω] as: check 7 = (p)(p̄)... 7 ≡ 1 mod 3, so YES it splits.");
print("Good primes for tiling IOP over Z[ω]: primes p ≡ 1 mod 3 (split completely).");
print("Good primes include: 7, 13, 19, 31, 37, 43, ...");

/* Which primes p are 'good' (split in Z[ω])? p ≡ 1 mod 3 */
good_primes = select(p -> p%3==1, primes(50));
print("\nPrimes p ≡ 1 mod 3 (split in Z[ω]): ", good_primes);

/* ── Lattice determinant ──────────────────────────────────────────────── */

print("\n=== Lattice geometry ===");
/* Gram matrix of {e1, e2} in Cartesian:
 * e1 = (1, 0), e2 = (1/2, √3/2)
 * G = [[e1·e1, e1·e2], [e2·e1, e2·e2]] = [[1, 1/2], [1/2, 1]] */
G = [1, 1/2; 1/2, 1];
det_G = matdet(G);
print("Gram matrix of hexagonal basis {e1=(1,0), e2=(1/2,√3/2)}:");
print("  G = [[1, 1/2], [1/2, 1]]");
print("  det(G) = ", det_G, " = 3/4");
print("  Unit cell area = √det(G) = √3/2 ≈ ", s3/2);
print("  This is the standard hexagonal lattice fundamental domain area.");

print("\nShortest vector: e1 = (1,0) or e2 = (1/2,√3/2), both with |·| = 1");
print("Second shortest: ω² = e^(2iπ/3) = ω-1 = (-1/2, √3/2), also |·|=1");
print("Six units of Z[ω]: ±1, ±ω, ±(1-ω)  [hexagonal symmetry]");

/* ── Inflation action ────────────────────────────────────────────────── */

print("\n=== Inflation action: Q(√5) ⊗ Z[ω] ===");
phi_sq = (3 + s5) / 2;   /* φ² = inflation factor */
print("Inflation scales positions by φ² = (3+√5)/2 ≈ ", phi_sq);
print("φ² ∈ Q(√5) ⊂ R  (real, not in Z[ω])");
print("After inflation: parent position z ∈ Z[ω] → child position ≈ φ²·z + offset");
print("  where offset ∈ Z[ω] (integer hexagonal, from substitution rules)");
print("  So exact child positions ∈ φ²·Z[ω] + Z[ω] = Z[φ²]·Z[ω] = Z[φ², ω]");
print("");
print("The exact coordinate ring at level n:");
print("  Positions ∈ Z[φ^{2n}, ω] = Z-span of {φ^{2k}·ω^j : 0≤k≤n, j∈Z/6Z}");
print("  This is a subring of Q(√5, √(-3))");
print("");
print("After discretization (psi functor rounds to Z[ω]):");
print("  The discrete positions (tx, ty) ∈ Z² = Z[ω] at ALL levels");
print("  Rounding error ≤ 1/2 hexagonal unit");

/* ── Q(√5, √(-3)): the full position field ───────────────────────────── */

print("\n=== The field Q(√5, √(-3)) ===");
/* This is the compositum of Q(√5) (from inflation) and Q(√(-3)) (from hex lattice) */
comp_poly = polcompositum(x^2-5, x^2+3)[1];
print("Compositum Q(√5, √(-3)): minimal polynomial of a primitive element:");
print("  ", comp_poly);
print("Degree: ", poldegree(comp_poly));

bnf_comp = bnfinit(comp_poly);
print("Discriminant: ", bnf_comp.disc);
print("Class number: ", bnf_comp.clgp.no);
print("Signature:    [", bnf_comp.r1, ", ", bnf_comp.r2, "]  (r1=real, r2=complex pairs)");
print("  → totally complex (r1=0): makes sense, Q(√(-3)) is imaginary");

/* ── Spectre subring ──────────────────────────────────────────────────── */

print("\n=== Spectre's restricted coordinate ring ===");
print("From #30 (geometric modification distance): spectre has NO reflected tiles.");
print("Spectre positions ∈ Z[ω] × Z/6Z × {false}  (index-2 subgroup of Γ)");
print("This is the orientation-preserving subgroup Γ⁺ = Z[ω] ⋊ Z/6Z");
print("It is NOT a different ring — same Z[ω] lattice, just no reflections.");
print("Lattice geometry is identical for hat and spectre; reflection constraint");
print("is a group-theoretic restriction, not an algebraic one.");

/* ── Norm form as distance metric ────────────────────────────────────── */

print("\n=== Norm form as tiling distance ===");
print("N(a+bω) = a²+ab+b² = squared hex-grid distance from origin to (a,b)");
print("Properties:");
print("  N(z) = 0 iff z = 0");
print("  N(z·w) = N(z)·N(w)  [multiplicative — N is a ring homomorphism Z[ω]→Z≥0]");
print("  N(z) = 1 iff z is a unit (6 units: ±1, ±ω, ±(1-ω))");
print("  Prime elements: primes p≡2 mod 3 (inert), and factors of p≡1 mod 3 (split)");

/* Compute N for a few tile positions */
print("\nSample norms (hexagonal distances²):");
pairs = [[0,0], [1,0], [0,1], [1,1], [2,1], [3,-1]];
for(i=1, #pairs, {
    a = pairs[i][1]; b = pairs[i][2];
    n = a^2 + a*b + b^2;
    dist = sqrt(n+0.);
    print("  (tx=", a, ",ty=", b, "): N = ", n, ", distance = ", dist);
});

/* ── Summary ──────────────────────────────────────────────────────────── */

print("\n=== Summary ===");
print("Coordinate ring of tile positions: Z[ω] where ω = e^(iπ/3) = 1/2+i√3/2");
print("  = Eisenstein integers = ring of integers of Q(√(-3))");
print("  = the unique imaginary quadratic PID with units of order 6");
print("");
print("Full tile group: Γ = Z[ω] ⋊ D₆  (Coxeter group, as in coxeter.rs)");
print("  = Z² ⋊ D₆ with hexagonal translation lattice");
print("  Normal form: (tx, ty, rotation mod 6, reflection bool)");
print("");
print("Norm form: N(a+bω) = a²+ab+b²  (multiplicative, Z[ω] → Z≥0)");
print("  Computes squared hexagonal distance from origin.");
print("");
print("Inflation ring: exact positions at level n live in Z[φ^{2n}, ω] ⊂ Q(√5, √(-3))");
print("  Q(√5, √(-3)) has degree 4, disc = ", bnf_comp.disc, ", class number = ", bnf_comp.clgp.no);
print("  After discretization (psi functor): positions return to Z[ω].");
print("");
print("Spectre: same coordinate ring Z[ω]; no-reflection constraint is");
print("  a group condition (index-2 subgroup of Γ), not an algebraic ring restriction.");
print("");
print("SVP/CVP over Z[ω]: Z[ω] is a PID (class number 1) and has a Euclidean algorithm.");
print("  SVP is trivially easy (shortest vector has norm 1 in Z[ω]).");
print("  Standard lattice hardness does NOT apply — Z[ω] is too structured.");
