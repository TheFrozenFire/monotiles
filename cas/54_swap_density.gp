/* Issue #54: Exact closed form of spectre swap density and tile count sequences mod p
 *
 * Background (from FINDINGS.md #36):
 * - Hat swap density: confusable tile pairs / total pairs converges to ~20%
 * - Spectre swap density: converges to ~25.4%
 * - Both converge geometrically at rate 1/λ² per level (sub-Perron eigenvalue)
 *
 * This script derives:
 * 1. Exact rational or algebraic expressions for the asymptotic swap density
 * 2. Tile count sequences mod p (periodicity, structural zeros)
 * 3. The growth ratio that determines convergence rate
 */

x = 'x;
M_hat = [3,1,3,3; 1,0,0,0; 2,0,1,2; 2,0,1,3];
M_spe = [7,1; 6,1];

/* ── Left Perron eigenvector = asymptotic tile frequencies ─────────────── */
/* The frequency vector satisfies v^T M = λ v^T, i.e., M^T v = λ v */
/* We compute the left eigenvector corresponding to the Perron eigenvalue */

print("=== Asymptotic tile frequencies (left PF eigenvector) ===");

/* Hat: find eigenvector of M^T for eigenvalue λ ≈ 6.854 */
lambda_hat = (7 + 3*sqrt(5)) / 2;
/* From WISDOM.md: 2v = [(2,0), (7,-3), (-12,6), (9,-3)] in Z[√5] representation */
/* where (a,b) = a + b√5 */
/* So v_H = 1, v_T = (7-3√5)/2, v_P = (-12+6√5)/2 = -6+3√5, v_F = (9-3√5)/2 */
s5 = sqrt(5);
v_H_hat = 1;
v_T_hat = (7 - 3*s5) / 2;
v_P_hat = (-12 + 6*s5) / 2;  /* = -6 + 3√5 */
v_F_hat = (9 - 3*s5) / 2;

print("Hat frequency vector (unnormalized, exact in Q(√5)):");
print("  v_H = 1");
print("  v_T = (7-3√5)/2 ≈ ", v_T_hat);
print("  v_P = (-12+6√5)/2 = -6+3√5 ≈ ", v_P_hat);
print("  v_F = (9-3√5)/2 ≈ ", v_F_hat);
total_hat = v_H_hat + v_T_hat + v_P_hat + v_F_hat;
print("  Sum = ", total_hat, " (should be 3 from WISDOM.md: 'component sum = 6, × 1/2 = 3')");

/* Verify it's an eigenvector: M^T v = λ v */
M_hat_T = mattranspose(M_hat);
v_hat = [v_H_hat, v_T_hat, v_P_hat, v_F_hat]~;
Mv = M_hat_T * v_hat;
print("\nVerify M^T v = λ v:");
print("  M^T v = ", Mv~);
print("  λ v   = ", (lambda_hat * v_hat)~);
print("  Error: ", norml2(Mv - lambda_hat * v_hat));

/* ── Hat swap density: P' ↔ F' ─────────────────────────────────────── */
/* P' and F' are the confusable pair. Swap density = freq(P') / (freq(P') + freq(F'))
 * or some other natural ratio. Let's compute the ratio of confusable-pair count
 * to total tile count. */

print("\n=== Hat swap density (exact) ===");
/* At each level, confusable tiles are P-type and F-type tiles in parent context.
 * The P'↔F' swap is possible when P and F are siblings.
 * The density of swappable pairs = fraction of tiles in confusable positions.
 * From FINDINGS.md #36: empirically ~20% for hat. */

/* The swap density equals freq(P) * freq(F) / (freq(total))^2 normalized somehow.
 * More precisely: it's the fraction of supertile pairs at level k that are (P,F)-siblings.
 * Let f_P = v_P / sum(v) and f_F = v_F / sum(v). */
f_P = v_P_hat / total_hat;
f_F = v_F_hat / total_hat;
f_H = v_H_hat / total_hat;
f_T = v_T_hat / total_hat;
print("Asymptotic frequencies (normalized):");
print("  f_H = ", f_H, " ≈ ", f_H+0.);
print("  f_T = ", f_T, " ≈ ", f_T+0.);
print("  f_P = ", f_P, " ≈ ", f_P+0.);
print("  f_F = ", f_F, " ≈ ", f_F+0.);
print("  Sum = ", f_H + f_T + f_P + f_F);

/* The swap density in #36 was defined as (number of swappable tile pairs) /
 * (total tile pairs at that level). This involves the number of P-F sibling pairs.
 * Since P' children of H' include [H,T,P,F in specific counts], and F' similarly,
 * the ratio of (P+F tiles that are siblings) to (total tiles) converges to
 * a function of f_P and f_F.
 * Without the exact definition from #36, let's compute f_P + f_F and f_P * f_F: */
print("\nf_P + f_F = ", f_P + f_F, " ≈ ", (f_P + f_F)+0.);
print("f_P * f_F = ", f_P * f_F, " ≈ ", (f_P * f_F)+0.);
/* The empirical 20% ≈ 2*f_P*f_F or (f_P+f_F)/(something) */
print("2·f_P·f_F = ", 2*f_P*f_F, " ≈ ", (2*f_P*f_F)+0.);

/* ── Spectre tile frequencies ────────────────────────────────────────── */

print("\n=== Spectre asymptotic tile frequencies ===");
lambda_spe = 4 + sqrt(15);
spe_min = x^2 - 8*x + 1;
/* Left eigenvector of M_spe for λ_spe:
 * M_spe^T * v = λ_spe * v
 * M_spe^T = [7, 6; 1, 1]
 * [7-λ, 6; 1, 1-λ] * v = 0
 * (7-λ)v_S + 6·v_M = 0 → v_M/v_S = (λ-7)/6
 * With λ = 4+√15: v_M/v_S = (√15-3)/6 */
s15 = sqrt(15);
v_S_spe = 6;                /* normalize so v_S = 6 */
v_M_spe = s15 - 3;
total_spe = v_S_spe + v_M_spe;
print("Spectre frequency vector (unnormalized):");
print("  v_S = 6");
print("  v_M = √15-3 ≈ ", v_M_spe);
print("  Sum = ", total_spe, " ≈ ", total_spe+0.);

f_S = v_S_spe / total_spe;
f_M = v_M_spe / total_spe;
print("Normalized: f_S = ", f_S, " ≈ ", f_S+0., ", f_M = ", f_M, " ≈ ", f_M+0.);

/* Verify eigenvector */
M_spe_T = mattranspose(M_spe);
v_spe = [v_S_spe, v_M_spe]~;
Mv_spe = M_spe_T * v_spe;
print("Verify M^T v = λ v:");
print("  M^T v = ", Mv_spe~);
print("  λ v   = ", (lambda_spe * v_spe)~);
print("  Error: ", norml2(Mv_spe - lambda_spe * v_spe));

/* ── Spectre swap density: Mystic' ↔ Spectre' ───────────────────────── */

print("\n=== Spectre swap density (exact) ===");
/* Mystic'↔Spectre' swap density: empirically ~25.4% from FINDINGS.md #36 */
/* Similar analysis: depends on f_Spectre and f_Mystic */
print("f_S + f_M = ", f_S + f_M, " = 1 (only 2 types)");
print("f_S * f_M = ", f_S * f_M, " ≈ ", (f_S * f_M)+0.);
print("2·f_S·f_M = ", 2*f_S*f_M, " ≈ ", (2*f_S*f_M)+0.);

/* Exact simplified form of 2·f_S·f_M: */
/* f_S = 6/(3+√15), f_M = (√15-3)/(3+√15) */
/* f_S * f_M = 6(√15-3)/(3+√15)^2 */
/* (3+√15)^2 = 9 + 6√15 + 15 = 24 + 6√15 */
denom_sq = (3 + s15)^2;
print("Exact: 2·f_S·f_M = 12(√15-3) / (24+6√15)");
print("     = 12(√15-3) / (6(4+√15))");
print("     = 2(√15-3) / (4+√15)");
print("     = 2(√15-3)(4-√15) / ((4+√15)(4-√15))");
print("     = 2(4√15-15-12+3√15) / (16-15)");
print("     = 2(7√15-27) / 1");
print("     = 14√15-54");
print("Numerical: ", 14*s15 - 54);
print("Compare empirical swap density ~0.254");
/* Hmm, 14√15-54 ≈ 14*3.873-54 ≈ 54.22-54 = 0.22. Close but not exactly 0.254. */
/* The definition of swap density in #36 may differ. Let's try f_M alone: */
print("\nAlternative: f_M = (√15-3)/(3+√15) ≈ ", f_M+0.);
/* ≈ (3.873-3)/(3+3.873) ≈ 0.873/6.873 ≈ 0.127 -- too small */
print("Alternative: 1-f_S = f_M ≈ ", f_M+0.);
/* The swap density from #36 was probably swap_count/total_tiles at each depth. */
/* Without the exact formula, we note the closed form candidates. */

/* ── Tile count sequences mod p ────────────────────────────────────────── */

print("\n=== Tile count sequences mod p ===");
/* Total tile count at level n for hat: sum(M^n * e_1) where e_1 = initial H */
/* = sum of entries in the n-th column of M^n (starting from H) */
/* Satisfies linear recurrence given by the characteristic polynomial */

print("Hat tile counts (starting from single H at level 0):");
v_init_hat = [1,0,0,0]~;   /* start with one H */
Mn = matid(4);
for(n=0, 8, {
    counts = Mn * v_init_hat;
    total = sum(i=1,4, counts[i]);
    print("  n=", n, ": total=", total, "  [H,T,P,F]=", counts~);
    Mn = Mn * M_hat;
});

print("\nHat tile counts mod 2:");
Mn = matid(4);
for(n=0, 12, {
    counts = Mn * v_init_hat;
    total = sum(i=1,4, counts[i]) % 2;
    Mn = Mn * M_hat;
    print("  n=", n, ": total mod 2 = ", total);
});

print("\nHat tile counts mod 3:");
Mn = matid(4);
for(n=0, 12, {
    counts = Mn * v_init_hat;
    total = sum(i=1,4, counts[i]) % 3;
    Mn = Mn * M_hat;
    print("  n=", n, ": total mod 3 = ", total);
});

print("\nSpectre tile counts (starting from single Spectre at level 0):");
v_init_spe = [1,0]~;
Mn = matid(2);
for(n=0, 8, {
    counts = Mn * v_init_spe;
    total = sum(i=1,2, counts[i]);
    print("  n=", n, ": total=", total, "  [S,M]=", counts~);
    Mn = Mn * M_spe;
});

/* ── Summary ──────────────────────────────────────────────────────────── */

print("\n=== Summary ===");
print("Hat asymptotic frequencies in Q(√5):");
print("  (H:T:P:F) = (1 : (7-3√5)/2 : (-6+3√5) : (9-3√5)/2)  [exact]");
print("  Sum = 3  (pure integer, confirming WISDOM.md claim)");
print("");
print("Spectre asymptotic frequencies in Q(√15):");
print("  (S:M) = (6 : √15-3)  [exact, sum = 3+√15]");
print("  Normalized: f_S = ", f_S+0., ", f_M = ", f_M+0.);
print("");
print("Swap density closed forms (candidates):");
print("  Hat 2·f_P·f_F ≈ ", (2*f_P*f_F)+0., "  (empirical ~0.20)");
print("  Spectre 2·f_S·f_M ≈ ", (2*f_S*f_M)+0., "  (empirical ~0.254)");
