/* Issue #57 (follow-up to #50, #52, #54): GAB frequency equation and hat-tile density
 *
 * Two quantities appear in the ROCQ proofs but were not computed by CAS:
 *
 * 1. GAB equation: q^2 - q + 1/5 = 0  (equivalently 5q^2 - 5q + 1 = 0)
 *    Roots: q_± = (5 ± √5) / 10
 *    Appear in HatSpectral.v as `ten_q_plus = mkQuad 5 1` (meaning (5+√5) in Z[√5] representation,
 *    so q_+ = ten_q_plus / 10 = (5+√5)/10).
 *    These are related to the Sturmian slope for hat tilings.
 *
 * 2. Hat-tile density vector: h = [4, 1, 2, 2] (hats per metatile type H, T, P, F)
 *    ROCQ proves M * h = [25, 4, 14, 16] (hats in each supertile type).
 *    The asymptotic hat-tile density is (v · h) / (v · 1) where v is the PF eigenvector.
 */

x = 'x;
s5 = sqrt(5);

/* ── GAB frequency equation ─────────────────────────────────────────── */

print("=== GAB frequency equation: 5q^2 - 5q + 1 = 0 ===");
gab_poly = 5*x^2 - 5*x + 1;
print("Polynomial: ", gab_poly);
print("Discriminant: ", poldisc(gab_poly));  /* 5 */

gab_roots = polroots(gab_poly);
print("Roots (numerical):  q_+ = ", real(gab_roots[2]), ", q_- = ", real(gab_roots[1]));

/* Exact forms */
q_plus  = (5 + s5) / 10;
q_minus = (5 - s5) / 10;
print("Exact: q_+ = (5+√5)/10 ≈ ", q_plus);
print("Exact: q_- = (5-√5)/10 ≈ ", q_minus);

/* Verify they satisfy 5q^2 - 5q + 1 = 0 */
check_plus  = 5*q_plus^2  - 5*q_plus  + 1;
check_minus = 5*q_minus^2 - 5*q_minus + 1;
print("\nVerify 5q_+^2 - 5q_+ + 1 = 0: ", check_plus, " (should be 0)");
print("Verify 5q_-^2 - 5q_- + 1 = 0: ", check_minus, " (should be 0)");

/* ── GAB roots as elements of Q(√5) ──────────────────────────────────── */

print("\n=== GAB roots in Q(√5) ===");
/* q_+ = (5+√5)/10 = 1/2 + √5/10 */
/* q_- = (5-√5)/10 = 1/2 - √5/10 */
print("q_+ = 1/2 + (1/10)·√5  [in Q(√5)]");
print("q_- = 1/2 - (1/10)·√5  [in Q(√5)]");
print("Sum:  q_+ + q_- = 1  (= coefficient ratio 5/5 by Vieta)");
print("Prod: q_+ · q_- = ", q_plus * q_minus, " = 1/5  (= constant term 1/5 by Vieta)");

/* Minimal polynomial of q_+ over Q: same as gab_poly (since its Galois conjugate is q_-) */
/* But q_+ is NOT an algebraic integer — denominator 10 */
/* Its minimal poly over Q is 5x^2-5x+1, not monic. */
/* As algebraic integer, 10·q_+ = 5+√5 is in Z[√5] since disc(Q(√5))=5≡1 mod 4,
 * ring of integers is Z[φ] where φ=(1+√5)/2.
 * 10·q_+ = 5+√5 = 2·φ^2 + ... let's compute */

phi = (1 + s5) / 2;
ten_q_plus = 5 + s5;   /* = 10 * q_+ */
ten_q_minus = 5 - s5;  /* = 10 * q_- */
print("\n10·q_+ = 5+√5 ≈ ", ten_q_plus);
print("10·q_- = 5-√5 ≈ ", ten_q_minus);

/* Express 5+√5 in terms of φ = (1+√5)/2:
 * 5+√5 = 5 + (2φ-1) = 4 + 2φ  (since √5 = 2φ-1)
 * Check: 4 + 2*(1+√5)/2 = 4 + 1 + √5 = 5 + √5 ✓ */
print("5+√5 = 4 + 2φ  (in Z[φ])");
print("Verify 4+2φ = ", 4 + 2*phi, " vs 5+√5 = ", ten_q_plus);

/* ── Sturmian slope connection ────────────────────────────────────────── */

print("\n=== Sturmian slope for hat tiling ===");
/* From Sturmian.v: hat tiling has continued fraction [0;3,1,1,1,...] = [0;3,(1)^∞]
 * This CF evaluates to: let α = [0;1,1,1,...] = φ-1 = (√5-1)/2
 * Then [0;3,1,1,1,...] = 1/(3 + α) = 1/(3 + (√5-1)/2) = 2/(6+√5-1) = 2/(5+√5)
 *                      = 2/(5+√5) * (5-√5)/(5-√5) = 2(5-√5)/(25-5)
 *                      = 2(5-√5)/20 = (5-√5)/10 = q_- */
alpha_sturmian = (s5 - 1) / 2;   /* = φ-1 = [0;1,1,1,...] */
slope = 1 / (3 + alpha_sturmian);
print("Sturmian slope from CF [0;3,1,1,1,...] = 1/(3+φ-1) = 1/(2+φ)");
print("  = ", slope);
print("q_- = (5-√5)/10 = ", q_minus);
print("Match? ", abs(slope - q_minus) < 1e-14, " (should be 1)");
print("=> q_- = (5-√5)/10 IS the hat Sturmian slope");
print("=> q_+ = (5+√5)/10 = 1 - q_- is the complementary density");

/* ── Relationship to PF eigenvector frequency of H-type ─────────────── */

print("\n=== GAB 'frequency' vs PF eigenvector frequency ===");
/* The ROCQ comment in HatSpectral.v calls q_+ the 'H-metatile frequency',
 * but it is NOT the PF eigenvector component — it's the Sturmian symbol density.
 * Let's clarify the distinction. */

/* PF left eigenvector of M_hat (from 54_swap_density.gp): */
M_hat = [3,1,3,3; 1,0,0,0; 2,0,1,2; 2,0,1,3];
lambda_hat = (7 + 3*s5) / 2;
v_H = 1;
v_T = (7 - 3*s5) / 2;
v_P = (-12 + 6*s5) / 2;
v_F = (9 - 3*s5) / 2;
total_v = v_H + v_T + v_P + v_F;  /* = 3 */
f_H_PF = v_H / total_v;
f_T_PF = v_T / total_v;
f_P_PF = v_P / total_v;
f_F_PF = v_F / total_v;

print("PF eigenvector normalized frequencies (metatile type fractions):");
print("  f_H = ", f_H_PF + 0., "  (NOT q_+ = ", q_plus, ")");
print("  f_T = ", f_T_PF + 0.);
print("  f_P = ", f_P_PF + 0.);
print("  f_F = ", f_F_PF + 0.);

print("\nGAB q_+ = (5+√5)/10 ≈ ", q_plus, " is the Sturmian symbol density,");
print("  = density of '0' symbols in the Sturmian word with slope q_- = (5-√5)/10");
print("  This is NOT the fraction of H-type metatiles in the substitution system.");
print("  The two quantities live in different models:");
print("    PF freq f_H = 1/3 ≈ 0.333 (fraction of metatile INSTANCES)");
print("    q_+  = (5+√5)/10 ≈ 0.724 (Sturmian symbol density — fraction of SPACE)");

/* ── Minimal polynomial of q_+ and field membership ─────────────────── */

print("\n=== Algebraic properties of q_± ===");
/* q_+ has minimal polynomial 5x^2 - 5x + 1 over Q.
 * This is NOT in Z[x] (leading coeff 5) so q_+ is not an algebraic integer.
 * However q_+^2 - q_+ + 1/5 = 0 so 5 is the content.
 * The field Q(q_+) = Q(√5) since q_+ = 1/2 + √5/10. */
print("q_+ ∈ Q(√5): YES (= 1/2 + √5/10)");
print("q_+ is an algebraic integer: NO (minimal poly has leading coeff 5)");
print("But 10·q_+ = 5+√5 = 4+2φ IS an algebraic integer in Z[φ]");
print("And q_+ = (4+2φ)/10 = (2+φ)/5 in lowest terms");
print("Check (2+φ)/5 = ", (2+phi)/5, " vs q_+ = ", q_plus);

/* Norm of 10·q_+ = 5+√5 in Q(√5): */
norm_ten_qplus = ten_q_plus * ten_q_minus;
print("\nN_{Q(√5)/Q}(5+√5) = (5+√5)(5-√5) = 25-5 = ", norm_ten_qplus, " = 20");
print("  = 2^2 · 5  (factors in Z)");

/* ── Hat-tile density vector ─────────────────────────────────────────── */

print("\n=== Hat-tile density vector ===");
/* h = [4, 1, 2, 2]: number of hats contained in each metatile type H, T, P, F */
h = [4, 1, 2, 2]~;
print("Hat counts per metatile type h = [H:4, T:1, P:2, F:2]");

/* Verify M * h = [25, 4, 14, 16] as proved in ROCQ Substitution.v */
Mh = M_hat * h;
print("\nM_hat * h = ", Mh~);
print("Expected  = [25, 4, 14, 16]");
print("Match: ", Mh == [25, 4, 14, 16]~);

/* ── Asymptotic hat-polykite count per metatile ──────────────────────── */

print("\n=== Asymptotic hat-polykite tiles per metatile (exact in Q(√5)) ===");
/* Each metatile type is built from multiple hat polykite tiles:
 *   H: 4 polykites, T: 1 polykite, P: 2 polykites, F: 2 polykites
 * (These are the base-level physical tile counts, NOT a fraction ≤ 1.)
 *
 * At level n starting from a single H:
 *   polykite_count(n) = h · (M^n e_1)
 *   metatile_count(n) = 1 · (M^n e_1)
 * As n → ∞, M^n e_1 ~ c · λ^n · r (right PF eigenvector).
 * So: polykite_count / metatile_count → (h · r) / (1 · r)  [average polykites/metatile]
 * This ratio is > 1 since each metatile contains multiple polykites. */

/* Compute right eigenvector by finding the null space of (M - λI) */
lambda_val = lambda_hat;
/* For a 2-component check first with a known approach:
 * (M - λI) r = 0.  Since char poly factors as (x-1)(x+1)(x^2-7x+1),
 * the Perron root λ = (7+3√5)/2 is a root of x^2-7x+1.
 * The right eigenvector can be computed numerically. */
M_minus_lambda = M_hat - lambda_val * matid(4);
/* The kernel of this matrix — take any non-trivial column */
/* Numerically: */
right_ev = mateigen(M_hat)[,4];   /* last column = largest eigenvalue */
print("Right PF eigenvector (numerical): ", right_ev~);

/* Normalize so components sum to 1 */
r_sum = sum(i=1, 4, real(right_ev[i]));
r_norm = real(right_ev) / r_sum;
print("Normalized right eigenvector: ", r_norm~);

/* Hat-tile density = h · r_norm */
hat_density_num = sum(i=1, 4, h[i] * r_norm[i]);
total_density = sum(i=1, 4, r_norm[i]);  /* = 1 by normalization */
print("\nAsymptotic avg polykites/metatile (numerical) = h · r = ", hat_density_num);
print("  = expected hat polykite tiles per metatile instance as level n → ∞");

/* ── Exact form using right eigenvector in Q(√5) ─────────────────────── */

print("\n=== Exact right PF eigenvector in Q(√5) ===");
/* The right eigenvector of M for eigenvalue λ = (7+3√5)/2 can be computed exactly.
 * (M - λI) r = 0.  We solve the 4×4 system over Q(√5).
 * Row reduce [M - λI | 0]. */

/* We know from the left eigenvector analysis that v^T M = λ v^T.
 * For the right eigenvector, we parameterize by the H-component.
 * M r = λ r:
 *   Row 1: 3r_H + r_T + 3r_P + 3r_F = λ r_H
 *   Row 2: r_H                        = λ r_T  → r_T = r_H / λ
 *   Row 3: 2r_H + r_P + 2r_F         = λ r_P  → (λ-1)r_P = 2r_H + 2r_F
 *   Row 4: 2r_H + r_P + 3r_F         = λ r_F  → (λ-3)r_F = 2r_H + r_P
 */
/* Set r_H = 1. */
r_H = 1;
r_T = 1 / lambda_val;
/* From row 4: (λ-3)r_F = 2 + r_P  and row 3: (λ-1)r_P = 2 + 2r_F */
/* Substitute: r_P = (2 + 2r_F)/(λ-1), then
 * (λ-3)r_F = 2 + (2+2r_F)/(λ-1)
 * (λ-3)(λ-1)r_F = 2(λ-1) + 2 + 2r_F
 * ((λ-3)(λ-1) - 2)r_F = 2(λ-1) + 2 = 2λ
 * (λ^2 - 4λ + 3 - 2)r_F = 2λ
 * (λ^2 - 4λ + 1)r_F = 2λ
 * Since λ satisfies λ^2 - 7λ + 1 = 0, we have λ^2 = 7λ-1.
 * λ^2 - 4λ + 1 = 7λ-1-4λ+1 = 3λ.
 * So 3λ r_F = 2λ → r_F = 2/3. */
r_F = 2/3;
r_P = (2 + 2*r_F) / (lambda_val - 1);

print("Right eigenvector (exact, r_H=1):");
print("  r_H = 1");
print("  r_T = 1/λ = 2/(7+3√5) = (7-3√5)/2 ÷ ... let's compute:");
print("    1/λ = 1/((7+3√5)/2) = 2/(7+3√5) = 2(7-3√5)/((7+3√5)(7-3√5))");
print("        = 2(7-3√5)/(49-45) = (7-3√5)/2 ≈ ", r_T);
print("  r_F = 2/3 (exact)");
print("  r_P = (2 + 2·r_F)/(λ-1) = (2 + 4/3)/(λ-1) = (10/3)/(λ-1)");
lam_minus_1 = lambda_val - 1;
r_P_val = (10/3) / lam_minus_1;
print("    (λ-1) = (7+3√5)/2 - 1 = (5+3√5)/2 ≈ ", lam_minus_1);
print("    r_P = (10/3)/((5+3√5)/2) = 20/(3(5+3√5)) = 20(5-3√5)/(3(25-45))");
print("         = 20(5-3√5)/(3·(-20)) = -(5-3√5)/3 = (3√5-5)/3 = √5-5/3");
r_P_exact = (3*s5 - 5) / 3;
print("  r_P = (3√5-5)/3 ≈ ", r_P_exact, " vs numerical ", r_P_val);

/* Check all components match numerical */
print("\nNumerical comparison:");
print("  r_H = 1,     numerical = ", real(right_ev[1]) / real(right_ev[1]));
print("  r_T ≈ ", r_T, " numerical = ", real(right_ev[2]) / real(right_ev[1]));
print("  r_P ≈ ", r_P_exact, " numerical = ", real(right_ev[3]) / real(right_ev[1]));
print("  r_F = 2/3 ≈ ", 2/3., " numerical = ", real(right_ev[4]) / real(right_ev[1]));

/* ── Exact hat-tile density from right eigenvector ───────────────────── */

print("\n=== Hat-tile density in Q(√5) (exact) ===");
/* h · r = 4·r_H + 1·r_T + 2·r_P + 2·r_F
 *       = 4·1 + 1·(7-3√5)/2 + 2·(3√5-5)/3 + 2·(2/3)
 *       = 4 + (7-3√5)/2 + (6√5-10)/3 + 4/3
 * Common denom 6:
 *       = 24/6 + 3(7-3√5)/6 + 2(6√5-10)/6 + 8/6
 *       = (24 + 21 - 9√5 + 12√5 - 20 + 8) / 6
 *       = (33 + 3√5) / 6
 *       = (11 + √5) / 2 */
h_dot_r_exact = (11 + s5) / 2;
print("h · r (unnormalized) = (11+√5)/2 ≈ ", h_dot_r_exact);

/* 1 · r = r_H + r_T + r_P + r_F
 *       = 1 + (7-3√5)/2 + (3√5-5)/3 + 2/3
 * Common denom 6:
 *       = 6/6 + 3(7-3√5)/6 + 2(3√5-5)/6 + 4/6
 *       = (6 + 21 - 9√5 + 6√5 - 10 + 4) / 6
 *       = (21 - 3√5) / 6
 *       = (7 - √5) / 2 */
one_dot_r_exact = (7 - s5) / 2;
print("1 · r (sum of components) = (7-√5)/2 ≈ ", one_dot_r_exact);

hat_density_exact = h_dot_r_exact / one_dot_r_exact;
print("Hat-tile density = (11+√5)/(7-√5)");
/* Rationalize: (11+√5)(7+√5) / ((7-√5)(7+√5)) = (77+11√5+7√5+5)/(49-5)
 *            = (82+18√5)/44 = (41+9√5)/22 */
hat_density_rationalized = (41 + 9*s5) / 22;
print("                = (11+√5)(7+√5) / ((7-√5)(7+√5))");
print("                = (82+18√5)/44");
print("                = (41+9√5)/22");
print("Numerical: (41+9√5)/22 ≈ ", hat_density_rationalized, "  [> 1: avg polykites per metatile]");
print("Check matches h·r/(1·r): ", abs(hat_density_exact - hat_density_rationalized) < 1e-10);

/* ── Summary ──────────────────────────────────────────────────────────── */

print("\n=== Summary ===");
print("GAB equation: 5q^2 - 5q + 1 = 0");
print("  q_+ = (5+√5)/10 ≈ ", q_plus, "  [complementary density]");
print("  q_- = (5-√5)/10 ≈ ", q_minus, "  [Sturmian slope for hat tiling]");
print("  q_- is the slope of CF [0;3,1,1,1,...] (verified numerically)");
print("  Both are elements of Q(√5) but NOT algebraic integers");
print("  10·q_± = 5±√5 = 4±(2φ-1)+1 are algebraic integers in Z[φ]");
print("");
print("CLARIFICATION: q_+ ≠ PF frequency of H-type metatiles");
print("  PF freq f_H = 1/3 ≈ 0.333  (fraction of metatile instances)");
print("  q_+ ≈ 0.724              (Sturmian symbol density / fraction of area)");
print("  These measure different things in different models.");
print("");
print("Hat-tile density vector h = [4, 1, 2, 2]:");
print("  M·h = [25, 4, 14, 16]  (verified, matches Substitution.v)");
print("  Right PF eigenvector r = (1, (7-3√5)/2, (3√5-5)/3, 2/3)  [exact, r_H=1]");
print("  Asymptotic avg polykites/metatile = (41+9√5)/22 ≈ ", hat_density_rationalized);
print("  = average hat polykite tiles per metatile instance as level n → ∞  [> 1 by construction]");
