/* Issue #52: Number field invariants of Q(λ_hat) = Q(√5) and Q(λ_spe) = Q(√15)
 *
 * Computes: discriminant, class number, class group, fundamental unit,
 * regulator, unit rank, and prime splitting behavior.
 *
 * Results establish the arithmetic structure of the fields in which the
 * dominant eigenvalues live.
 */

x = 'x;
hat_min = x^2 - 7*x + 1;   /* min poly of λ_hat; generates Q(√5) */
spe_min = x^2 - 8*x + 1;   /* min poly of λ_spe; generates Q(√15) */

/* ── Basic number field data ─────────────────────────────────────────── */

print("=== Q(√5) = Q(λ_hat) ===");
bnf5 = bnfinit(hat_min);
print("Polynomial:         ", bnf5.pol);
print("Discriminant:       ", bnf5.disc);
print("Signature:          [", bnf5.r1, ", ", bnf5.r2, "]  (r1 real, r2 complex pairs)");
print("Class number:       ", bnf5.clgp.no);
print("Class group:        ", bnf5.clgp.cyc);
print("Regulator:          ", bnf5.reg);
print("Fundamental units:  ", bnf5.fu);

print("\n=== Q(√15) = Q(λ_spe) ===");
bnf15 = bnfinit(spe_min);
print("Polynomial:         ", bnf15.pol);
print("Discriminant:       ", bnf15.disc);
print("Signature:          [", bnf15.r1, ", ", bnf15.r2, "]");
print("Class number:       ", bnf15.clgp.no);
print("Class group:        ", bnf15.clgp.cyc);
print("Regulator:          ", bnf15.reg);
print("Fundamental units:  ", bnf15.fu);

/* ── Prime splitting ─────────────────────────────────────────────────── */

print("\n=== Prime splitting in Q(√5) ===");
print("Discriminant = 5; primes split/ramify/remain inert based on Kronecker symbol (disc|p)");
primes_to_check = [2, 3, 5, 7, 11, 13, 17, 19, 23, 29];
for(i=1, #primes_to_check, {
    p = primes_to_check[i];
    k = kronecker(bnf5.disc, p);
    stype = if(k == 0, "ramifies", if(k == 1, "splits", "inert"));
    print("  p=", p, ": (5|p) = Kronecker(", bnf5.disc, ",", p, ") = ", k, " → ", stype);
});

print("\n=== Prime splitting in Q(√15) ===");
print("Discriminant = 60; splits/ramifies/inert based on (60|p)");
for(i=1, #primes_to_check, {
    p = primes_to_check[i];
    k = kronecker(bnf15.disc, p);
    stype = if(k == 0, "ramifies", if(k == 1, "splits", "inert"));
    print("  p=", p, ": Kronecker(", bnf15.disc, ",", p, ") = ", k, " → ", stype);
});

/* ── Eigenvalue as algebraic integer ────────────────────────────────── */

print("\n=== The Perron eigenvalues as algebraic integers ===");
/* Q(√5): ring of integers Z[(1+√5)/2] since disc=5≡1 mod 4  */
print("Q(√5): disc=5≡1 mod 4 → ring of integers O = Z[φ] where φ=(1+√5)/2");
print("  λ_hat = (7+3√5)/2 = 3 + 3(√5-1)/2 + 1 = ...");
/* Express λ_hat in terms of φ: λ_hat = 2φ²+φ = 2(φ+1)+φ = 3φ+2 */
/* Check: 3φ+2 = 3(1+√5)/2 + 2 = (3+3√5+4)/2 = (7+3√5)/2 ✓ */
print("  λ_hat = 3φ + 2  (explicitly in Z[φ]) ✓");
print("  Norm N(λ_hat) = N(3φ+2) = product of conjugates = ((7+3√5)/2)·((7-3√5)/2) = (49-45)/4 = 1");
print("  → λ_hat is a unit in O(Q(√5))!");
print("  Fundamental unit of Q(√5): φ = (1+√5)/2");
print("  λ_hat = 3φ+2 = φ^4 (since φ^2=φ+1, φ^3=2φ+1, φ^4=3φ+2) ✓");
print("  Verify φ^4: ", ((1+sqrt(5))/2)^4, " vs λ_hat: ", (7+3*sqrt(5))/2);

print("");
/* Q(√15): ring of integers Z[√15] since 15≡3 mod 4 */
print("Q(√15): disc=60, 15≡3 mod 4 → ring of integers O = Z[√15]");
print("  λ_spe = 4+√15 ∈ Z[√15]");
print("  Norm N(λ_spe) = (4+√15)(4-√15) = 16-15 = 1");
print("  → λ_spe is a unit in O(Q(√15))!");
print("  Fundamental unit of Q(√15): checking if 4+√15 is fundamental...");
print("  Regulator = log(fund. unit). bnfinit regulator: ", bnf15.reg);
print("  log(4+√15) = ", log(4+sqrt(15)));
print("  Match? (should be equal if 4+√15 is fundamental unit)");

/* ── Compositum Q(√3, √5) invariants ──────────────────────────────────── */

print("\n=== Compositum Q(√3, √5) ===");
comp_poly = x^4 - 16*x^2 + 4;   /* min poly of √3+√5 */
bnf_comp = bnfinit(comp_poly);
print("Polynomial: ", comp_poly);
print("Discriminant: ", bnf_comp.disc);
print("Class number: ", bnf_comp.clgp.no);
print("Class group:  ", bnf_comp.clgp.cyc);
print("Regulator:    ", bnf_comp.reg);
/* Note: disc(Q(√3,√5)) should be disc(Q(√3))^2 * disc(Q(√5))^2 / something */
print("Expected disc factored: ", factor(bnf_comp.disc));

/* ── Summary ──────────────────────────────────────────────────────────── */

print("\n=== Summary ===");
print("Q(√5) = Q(λ_hat):");
print("  disc=5, class number=", bnf5.clgp.no, ", unit rank=1");
print("  Ring of integers: Z[φ] where φ=(1+√5)/2");
print("  λ_hat = φ^4 (a unit, the 4th power of the fundamental unit)");
print("  Primes: 5 ramifies; p≡±1 mod 5 split; p≡±2 mod 5 inert");
print("");
print("Q(√15) = Q(λ_spe):");
print("  disc=60, class number=", bnf15.clgp.no, ", unit rank=1");
print("  Ring of integers: Z[√15]");
print("  λ_spe = 4+√15 (the fundamental unit)");
print("  Class number=", bnf15.clgp.no, ": the ring Z[√15] is", if(bnf15.clgp.no==1, " a PID", " NOT a PID"));
