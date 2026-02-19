/* Issue #55: Smith normal form of the hat and spectre substitution matrices
 *
 * The Smith normal form SNF(M) = diag(d1, d2, ..., dn) where d1|d2|...|dn
 * is the unique diagonal form over Z reachable by row and column operations
 * over Z (i.e., by left/right multiplication by matrices in GL(n,Z)).
 *
 * The SNF encodes:
 * - The torsion structure of the cokernel Z^n / M Z^n
 * - The elementary divisors of the substitution map
 * - Cohomological invariants (Anderson-Putnam complex for the tiling)
 *
 * For the tiling IOP: the SNF determines which constraint combinations are
 * "purely algebraic" (forced by integer linear relations) vs. geometric.
 */

M_hat = [3,1,3,3; 1,0,0,0; 2,0,1,2; 2,0,1,3];
M_spe = [7,1; 6,1];

print("=== Smith Normal Form ===");
print("\nHat substitution matrix:");
print(M_hat);
snf_hat = matsnf(M_hat, 1);  /* flag=1 returns [SNF, U, V] with U*M*V = SNF */
print("SNF(M_hat) = ", snf_hat[1]);
print("Left transform U (det=±1):  ", snf_hat[2]);
print("Right transform V (det=±1): ", snf_hat[3]);
print("Verify U*M*V = SNF: ", snf_hat[2] * M_hat * snf_hat[3]);

print("\nSpectre substitution matrix:");
print(M_spe);
snf_spe = matsnf(M_spe, 1);
print("SNF(M_spe) = ", snf_spe[1]);
print("Left transform U:  ", snf_spe[2]);
print("Right transform V: ", snf_spe[3]);
print("Verify U*M*V = SNF: ", snf_spe[2] * M_spe * snf_spe[3]);

/* ── Elementary divisors ─────────────────────────────────────────────── */

print("\n=== Elementary divisors ===");
print("Hat:     ", matdiagonal(snf_hat[1]));
print("Spectre: ", matdiagonal(snf_spe[1]));

/* ── Cokernel structure ───────────────────────────────────────────────── */

print("\n=== Cokernel Z^n / M·Z^n ===");
/* Cokernel has torsion part given by the non-unit elementary divisors */
/* and free part given by the kernel rank (= number of zero diagonal entries) */
print("Hat cokernel:");
hat_diag = matdiagonal(snf_hat[1]);
for(i=1, #hat_diag, {
    d = hat_diag[i];
    if(d == 0, print("  Z (free summand)"),
    if(d == 1, print("  0 (trivial)"),
               print("  Z/", d, "Z")));
});

print("Spectre cokernel:");
spe_diag = matdiagonal(snf_spe[1]);
for(i=1, #spe_diag, {
    d = spe_diag[i];
    if(d == 0, print("  Z (free summand)"),
    if(d == 1, print("  0 (trivial)"),
               print("  Z/", d, "Z")));
});

/* ── Rank and nullity ────────────────────────────────────────────────── */

print("\n=== Rank and nullity over Z ===");
/* select returns a Vec; count non-zero and zero entries manually */
hat_d = Vec(matdiagonal(snf_hat[1]));
spe_d = Vec(matdiagonal(snf_spe[1]));
hat_rank = sum(i=1, #hat_d, hat_d[i] != 0);
hat_null = sum(i=1, #hat_d, hat_d[i] == 0);
spe_rank = sum(i=1, #spe_d, spe_d[i] != 0);
spe_null = sum(i=1, #spe_d, spe_d[i] == 0);
print("Hat rank (non-zero invariant factors): ", hat_rank);
print("Hat nullity (zero diagonal entries):   ", hat_null);
print("Spectre rank:    ", spe_rank);
print("Spectre nullity: ", spe_null);

/* ── Integer inverse ──────────────────────────────────────────────────── */

print("\n=== Integer inverse (Cayley-Hamilton / det = ±1) ===");
/* If det = ±1, M is invertible over Z. Verified from det(M_hat) = -1. */
print("Hat det:     ", matdet(M_hat), " → M_hat ∈ GL(4,Z), has integer inverse");
print("Spectre det: ", matdet(M_spe), " → M_spe ∈ GL(2,Z), has integer inverse");

/* Compute M_hat^{-1} via adjugate / det */
M_hat_inv = matinverseimage(M_hat, matid(4));
print("M_hat^{-1} = ", M_hat_inv);
print("Verify M * M^{-1} = I: ", M_hat * M_hat_inv);

M_spe_inv = matinverseimage(M_spe, matid(2));
print("M_spe^{-1} = ", M_spe_inv);
print("Verify M * M^{-1} = I: ", M_spe * M_spe_inv);

/* ── Summary ──────────────────────────────────────────────────────────── */

print("\n=== Summary ===");
print("Hat SNF diagonal:     ", matdiagonal(snf_hat[1]));
print("Spectre SNF diagonal: ", matdiagonal(snf_spe[1]));
print("");
print("Both matrices are in GL(n,Z) (det = ±1).");
print("All elementary divisors are 1 → cokernel is trivial in both cases.");
print("M is already SNF-trivial: Z^n / M·Z^n = 0 (finite, no free summand).");
print("This means the substitution map is a Z-module isomorphism on Z^n.");
