/* Issue #50: Pisot/Salem classification of dominant substitution eigenvalues
 *
 * A Pisot number is an algebraic integer > 1 all of whose algebraic conjugates
 * have modulus strictly < 1.
 * A Salem number is an algebraic integer > 1 whose minimal polynomial is
 * reciprocal (x^n p(1/x) = p(x)) and all conjugates have modulus ≤ 1, with
 * at least one on the unit circle.
 *
 * These classes are mutually exclusive and exhaustive for algebraic integers
 * > 1 with real quadratic minimal polynomials.
 */

M_hat = [3,1,3,3; 1,0,0,0; 2,0,1,2; 2,0,1,3];
M_spe = [7,1; 6,1];
x = 'x;

p_hat = charpoly(M_hat, x);
p_spe = charpoly(M_spe, x);

hat_irred = x^2 - 7*x + 1;   /* irreducible factor containing Perron root */
spe_min   = p_spe;             /* already irreducible */

/* ── Roots of minimal polynomials ──────────────────────────────────── */

print("=== Roots of minimal polynomials ===");
r_hat = polroots(hat_irred);
r_spe = polroots(spe_min);
print("Hat minimal poly roots: ", r_hat);
print("Spe minimal poly roots: ", r_spe);

/* ── Pisot test ─────────────────────────────────────────────────────── */
/* λ is Pisot if it has degree d, all other d-1 conjugates have |·| < 1 */

pisot_hat = 1;
lambda_hat = vecmax(real(r_hat));
for(i=1, #r_hat, {
    c = real(r_hat[i]);
    if(abs(c) < 1, print("Hat conjugate ", c, " has |·| < 1 ✓"),
                   if(abs(c) > 1 && c != lambda_hat,
                      print("Hat conjugate ", c, " has |·| > 1 — NOT Pisot");
                      pisot_hat = 0));
});
if(pisot_hat, print("λ_hat = ", lambda_hat, " is PISOT"));

pisot_spe = 1;
lambda_spe = vecmax(real(r_spe));
for(i=1, #r_spe, {
    c = real(r_spe[i]);
    if(abs(c) < 1, print("Spe conjugate ", c, " has |·| < 1 ✓"),
                   if(abs(c) > 1 && c != lambda_spe,
                      print("Spe conjugate ", c, " has |·| > 1 — NOT Pisot");
                      pisot_spe = 0));
});
if(pisot_spe, print("λ_spe = ", lambda_spe, " is PISOT"));

/* ── Anti-palindromic structure of hat charpoly ─────────────────────── */
/* Check if x^4 p(1/x) = -p(x) */

print("\n=== Palindromic / anti-palindromic check ===");
p4 = x^4 * subst(p_hat, x, 1/x);
p4_simplified = simplify(p4);
print("x^4 * p_hat(1/x) = ", p4_simplified);
print("-p_hat(x)         = ", -p_hat);
print("Equal? ", p4_simplified == -p_hat);
/* If true: anti-palindromic — every root λ pairs with 1/λ */
/* This means the product of all roots is ±1, matching det = -1 */

/* ── Product of roots (Vieta) ───────────────────────────────────────── */
print("\n=== Root products (Vieta's formulas) ===");
print("Hat:     product of all roots = ", vecprod(real(polroots(p_hat))));
print("Hat:     det(M) = ", matdet(M_hat));
print("Spectre: product of all roots = ", vecprod(real(polroots(p_spe))));
print("Spectre: det(M) = ", matdet(M_spe));

/* ── Explicit closed forms ──────────────────────────────────────────── */

print("\n=== Closed forms via Q(√5) and Q(√15) ===");
phi = (1 + sqrt(5)) / 2;
print("φ = (1+√5)/2 = ", phi);
print("λ_hat = (7+3√5)/2 = ", (7 + 3*sqrt(5))/2);
print("  = 3φ² (since φ² = φ+1, 3φ² = 3φ+3 = (3(1+√5)/2)+3 = (9+3√5)/2... recheck)");
print("  Actually: 3φ² = 3(φ+1) = 3φ+3 = 3(1+√5)/2 + 3 = (3+3√5+6)/2 = (9+3√5)/2 ≠ (7+3√5)/2");
print("  Let's try: φ² = (3+√5)/2, so 2φ²+φ = (3+√5) + (1+√5)/2 = (6+2√5+1+√5)/2 = (7+3√5)/2 ✓");
print("  λ_hat = 2φ² + φ = φ(2φ+1) = φ(√5+2)");
print("  Verify: φ(2φ+1) = ", phi * (2*phi + 1));
print("  Verify (7+3√5)/2 = ", (7+3*sqrt(5))/2);
print("");
print("λ_spe = 4+√15 = ", 4 + sqrt(15));
print("  No simple closed form in terms of φ; Q(√15) ≠ Q(√5)");

/* ── Summary ────────────────────────────────────────────────────────── */

print("\n=== Summary ===");
print("λ_hat ≈ ", lambda_hat, " is a Pisot number in Q(√5)");
print("  Minimal polynomial: x^2 - 7x + 1");
print("  Conjugate: (7-3√5)/2 ≈ ", (7-3*sqrt(5))/2, " (modulus < 1)");
print("  Closed form: λ_hat = 2φ² + φ  where φ = (1+√5)/2");
print("");
print("λ_spe ≈ ", lambda_spe, " is a Pisot number in Q(√15)");
print("  Minimal polynomial: x^2 - 8x + 1");
print("  Conjugate: 4-√15 ≈ ", 4-sqrt(15), " (modulus < 1)");
print("  No φ-closed form; Q(√15) is distinct from Q(√5)");
print("");
print("Both are Pisot — standard for repetitive primitive substitution tilings.");
print("Neither is Salem (which would require conjugates on the unit circle).");
