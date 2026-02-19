From Stdlib Require Import ZArith.
From Stdlib Require Import List.
From Stdlib Require Import Lia.
Import ListNotations.

Require Import RocqProofs.Primitives.
Require Import RocqProofs.MatrixTheory.
Require Import RocqProofs.QuadraticFields.

Open Scope Z_scope.

Set Default Proof Using "Type".

(** * Hat Substitution Matrix: Spectral Properties

    Formal verification of the 4x4 hat substitution matrix and its spectral
    properties, corresponding to crates/analysis/src/spectral.rs.

    The matrix M[i][j] = number of type-j metatiles in the level-1 supertile
    of type i. Row/column order: H, T, P, F.

    Key results:
    - det(M) = -1
    - tr(M) = 7
    - Characteristic polynomial: lambda^4 - 7*lambda^3 + 7*lambda - 1 = 0
    - Eigenvalues: phi^4 = (7 + 3*sqrt(5))/2, 1, -1, (7 - 3*sqrt(5))/2
    - Integer eigenvectors for lambda = 1 and lambda = -1
    - Eigenvector verification over Z[sqrt(5)] for the Perron eigenvalue
    - GAB frequency equation: q^2 - q + 1/5 = 0

    Reference: Smith, Myers, Kaplan, Goodman-Strauss (2023),
    "An aperiodic monotile". *)

(** ** The Hat Substitution Matrix *)

(** M[i][j] = number of type-j metatiles in the level-1 supertile of type i.
    Row/column order: H, T, P, F.

    H' = 3H + 1T + 3P + 3F  (10 children)
    T' = 1H                   (1 child)
    P' = 2H + 0T + 1P + 2F   (5 children)
    F' = 2H + 0T + 1P + 3F   (6 children) *)
Definition hat_matrix : matrix :=
  mat4x4  3 1 3 3
           1 0 0 0
           2 0 1 2
           2 0 1 3.

(** ** Basic Matrix Properties *)

(** Row sums: total children per metatile type. *)
Theorem hat_row_sum_H :
  mat_get hat_matrix 0 0 + mat_get hat_matrix 0 1 +
  mat_get hat_matrix 0 2 + mat_get hat_matrix 0 3 = 10.
Proof. vm_compute. reflexivity. Qed.

Theorem hat_row_sum_T :
  mat_get hat_matrix 1 0 + mat_get hat_matrix 1 1 +
  mat_get hat_matrix 1 2 + mat_get hat_matrix 1 3 = 1.
Proof. vm_compute. reflexivity. Qed.

Theorem hat_row_sum_P :
  mat_get hat_matrix 2 0 + mat_get hat_matrix 2 1 +
  mat_get hat_matrix 2 2 + mat_get hat_matrix 2 3 = 5.
Proof. vm_compute. reflexivity. Qed.

Theorem hat_row_sum_F :
  mat_get hat_matrix 3 0 + mat_get hat_matrix 3 1 +
  mat_get hat_matrix 3 2 + mat_get hat_matrix 3 3 = 6.
Proof. vm_compute. reflexivity. Qed.

(** Trace = 7. *)
Theorem hat_trace : mat_trace hat_matrix = 7.
Proof. vm_compute. reflexivity. Qed.

(** ** Determinant

    Computed by cofactor expansion. det(M) = -1. *)

(** Direct verification of det(hat_matrix) = -1 via cofactor expansion. *)
Theorem hat_det : forall (det_val : Z),
  det_val = (  mat_get hat_matrix 0 0 *
                 (  mat_get hat_matrix 1 1 * (mat_get hat_matrix 2 2 * mat_get hat_matrix 3 3 - mat_get hat_matrix 2 3 * mat_get hat_matrix 3 2)
                  - mat_get hat_matrix 1 2 * (mat_get hat_matrix 2 1 * mat_get hat_matrix 3 3 - mat_get hat_matrix 2 3 * mat_get hat_matrix 3 1)
                  + mat_get hat_matrix 1 3 * (mat_get hat_matrix 2 1 * mat_get hat_matrix 3 2 - mat_get hat_matrix 2 2 * mat_get hat_matrix 3 1))
             - mat_get hat_matrix 0 1 *
                 (  mat_get hat_matrix 1 0 * (mat_get hat_matrix 2 2 * mat_get hat_matrix 3 3 - mat_get hat_matrix 2 3 * mat_get hat_matrix 3 2)
                  - mat_get hat_matrix 1 2 * (mat_get hat_matrix 2 0 * mat_get hat_matrix 3 3 - mat_get hat_matrix 2 3 * mat_get hat_matrix 3 0)
                  + mat_get hat_matrix 1 3 * (mat_get hat_matrix 2 0 * mat_get hat_matrix 3 2 - mat_get hat_matrix 2 2 * mat_get hat_matrix 3 0))
             + mat_get hat_matrix 0 2 *
                 (  mat_get hat_matrix 1 0 * (mat_get hat_matrix 2 1 * mat_get hat_matrix 3 3 - mat_get hat_matrix 2 3 * mat_get hat_matrix 3 1)
                  - mat_get hat_matrix 1 1 * (mat_get hat_matrix 2 0 * mat_get hat_matrix 3 3 - mat_get hat_matrix 2 3 * mat_get hat_matrix 3 0)
                  + mat_get hat_matrix 1 3 * (mat_get hat_matrix 2 0 * mat_get hat_matrix 3 1 - mat_get hat_matrix 2 1 * mat_get hat_matrix 3 0))
             - mat_get hat_matrix 0 3 *
                 (  mat_get hat_matrix 1 0 * (mat_get hat_matrix 2 1 * mat_get hat_matrix 3 2 - mat_get hat_matrix 2 2 * mat_get hat_matrix 3 1)
                  - mat_get hat_matrix 1 1 * (mat_get hat_matrix 2 0 * mat_get hat_matrix 3 2 - mat_get hat_matrix 2 2 * mat_get hat_matrix 3 0)
                  + mat_get hat_matrix 1 2 * (mat_get hat_matrix 2 0 * mat_get hat_matrix 3 1 - mat_get hat_matrix 2 1 * mat_get hat_matrix 3 0)))
  -> det_val = -1.
Proof. vm_compute. lia. Qed.

(** Simpler statement: the cofactor expansion equals -1. *)
Theorem hat_determinant_is_minus_one :
  3 * (0 * (1*3 - 2*1) - 0 * (0*3 - 2*0) + 0 * (0*1 - 1*0))
  - 1 * (1 * (1*3 - 2*1) - 0 * (2*3 - 2*2) + 0 * (2*1 - 1*2))
  + 3 * (1 * (0*3 - 2*0) - 0 * (2*3 - 2*2) + 0 * (2*0 - 0*2))
  - 3 * (1 * (0*1 - 1*0) - 0 * (2*1 - 1*2) + 0 * (2*0 - 0*2))
  = -1.
Proof. reflexivity. Qed.

(** ** Characteristic Polynomial

    The characteristic polynomial of the hat matrix is:
      lambda^4 - 7*lambda^3 + 7*lambda - 1 = 0

    It factors as: (lambda - 1)(lambda + 1)(lambda^2 - 7*lambda + 1) = 0

    We verify this by showing the polynomial vanishes at the four eigenvalues. *)

(** The polynomial lambda^4 - 7*lambda^3 + 7*lambda - 1. *)
Definition hat_char_poly (lambda : Z) : Z :=
  lambda * lambda * lambda * lambda - 7 * lambda * lambda * lambda + 7 * lambda - 1.

(** Factored form: (lambda - 1)(lambda + 1)(lambda^2 - 7*lambda + 1). *)
Theorem hat_char_poly_factors : forall lambda,
  hat_char_poly lambda = (lambda - 1) * (lambda + 1) * (lambda * lambda - 7 * lambda + 1).
Proof. intros. unfold hat_char_poly. nia. Qed.

(** Eigenvalue lambda = 1 is a root. *)
Theorem hat_eigenvalue_1 : hat_char_poly 1 = 0.
Proof. vm_compute. reflexivity. Qed.

(** Eigenvalue lambda = -1 is a root. *)
Theorem hat_eigenvalue_neg1 : hat_char_poly (-1) = 0.
Proof. vm_compute. reflexivity. Qed.

(** ** Integer Eigenvectors

    For eigenvalues 1 and -1, the eigenvectors are over Z. *)

(** Eigenvector for lambda = 1: [1, 1, 0, -1].
    Verification: M * [1,1,0,-1] = 1 * [1,1,0,-1]. *)
Theorem hat_eigenvector_1 :
  is_eigenvector_4x4 hat_matrix 1 1 0 (-1) 1.
Proof. vm_compute. repeat split; reflexivity. Qed.

(** Eigenvector for lambda = -1: [-3, 3, 2, 1].
    Verification: M * [-3,3,2,1] = -1 * [-3,3,2,1]. *)
Theorem hat_eigenvector_neg1 :
  is_eigenvector_4x4 hat_matrix (-3) 3 2 1 (-1).
Proof. vm_compute. repeat split; reflexivity. Qed.

(** ** Perron-Frobenius Eigenvalue over Z[sqrt(5)]

    The Perron eigenvalue is phi^4 = (7 + 3*sqrt(5))/2.
    Since we work over Z, we use the "2x" representation:
    2 * phi^4 = 7 + 3*sqrt(5) = (7, 3) in Z[sqrt(5)].

    The quadratic factor lambda^2 - 7*lambda + 1 = 0 has roots:
    lambda = (7 +/- sqrt(45)) / 2 = (7 +/- 3*sqrt(5)) / 2 *)

(** 2 * Perron eigenvalue = 7 + 3*sqrt(5). *)
Definition two_perron : quad 5 := mkQuad 7 3.

(** 2 * anti-Perron eigenvalue = 7 - 3*sqrt(5). *)
Definition two_anti_perron : quad 5 := mkQuad 7 (-3).

(** Product of the two quadratic roots: (7+3s)(7-3s)/4 = (49-45)/4 = 1.
    In the 2x representation: (2*lambda1)(2*lambda2) = 4*lambda1*lambda2 = 4*1 = 4. *)
Theorem perron_anti_perron_product :
  quad_mul 5 two_perron two_anti_perron = mkQuad 4 0.
Proof. vm_compute. reflexivity. Qed.

(** Sum of the two quadratic roots: lambda1 + lambda2 = 7.
    In the 2x representation: 2*lambda1 + 2*lambda2 = 14. *)
Theorem perron_anti_perron_sum :
  quad_add 5 two_perron two_anti_perron = mkQuad 14 0.
Proof. vm_compute. reflexivity. Qed.

(** Verify: (2*lambda)^2 - 7*(2*lambda)*2 + 1*4 = 0 for the Perron eigenvalue.
    That is: (7+3s)^2 - 14*(7+3s) + 4 = 0.
    (7+3s)^2 = 49 + 42s + 45 = 94 + 42s
    14*(7+3s) = 98 + 42s
    94 + 42s - 98 - 42s + 4 = 0. ✓ *)
Theorem perron_satisfies_quadratic :
  let p := two_perron in
  let p2 := quad_mul 5 p p in
  let seven_2p := quad_mul 5 (mkQuad 14 0) p in
  quad_add 5 (quad_sub 5 p2 seven_2p) (mkQuad 4 0) = mkQuad 0 0.
Proof. vm_compute. reflexivity. Qed.

(** Same for the anti-Perron eigenvalue. *)
Theorem anti_perron_satisfies_quadratic :
  let p := two_anti_perron in
  let p2 := quad_mul 5 p p in
  let seven_2p := quad_mul 5 (mkQuad 14 0) p in
  quad_add 5 (quad_sub 5 p2 seven_2p) (mkQuad 4 0) = mkQuad 0 0.
Proof. vm_compute. reflexivity. Qed.

(** Norm of the Perron eigenvalue: N(7 + 3*sqrt(5)) = 49 - 45 = 4.
    So N(phi^4) = N((7+3s)/2) = 4/4 = 1, confirming phi^4 is a unit. *)
Theorem perron_norm : quad_norm 5 two_perron = 4.
Proof. vm_compute. reflexivity. Qed.

(** ** Connection to Golden Ratio

    phi^4 = phi^2 * phi^2 = ((3+s)/2)^2 = (14 + 6s)/4 = (7 + 3s)/2.
    In 2x representation: 2*phi^4 = (2*phi^2)^2 / 2.
    But (2*phi^2) = (3+s), so (3+s)^2 = 9 + 6s + 5 = 14 + 6s = 2*(7+3s). *)
Theorem phi4_from_phi2 :
  let two_phi2 := mkQuad 3 1 in  (* 2*phi^2 = 3 + sqrt(5) *)
  quad_mul 5 two_phi2 two_phi2 = quad_add 5 two_perron two_perron.
Proof. vm_compute. reflexivity. Qed.

(** ** Eigenvector Verification over Z[sqrt(5)]

    The left Perron-Frobenius eigenvector (unnormalized, over Z) is:
      v = [3, 5 - 3*phi, 6*phi - 9, 6 - 3*phi]
    which sums to 3.

    In the 2x representation (multiply phi terms by 2):
      3*v = [3, (10 - 3*(1+s))/1, (3*(1+s) - 9)/1, (6 - 3*(1+s)/1)]
    Actually, we work more carefully:

    The unnormalized eigenvector satisfies v^T * M = phi^4 * v^T.
    Over Z[sqrt(5)], we verify M^T * v = phi^4 * v componentwise.

    To avoid fractions, we multiply everything by 6 and work in Z[sqrt(5)]:
      6*v = [6, 10 - 6*phi, 12*phi - 18, 12 - 6*phi]
    where phi = (1+s)/2.
    6*phi = 3*(1+s) = 3+3s.
    So 6*v = [6, 10-(3+3s), (6+6s)-18, 12-(3+3s)]
           = [(6,0), (7,-3), (-12,6), (9,-3)].

    And 6*phi^4 = 3*(7+3s) = (21, 9).

    Verify: M^T * 6v = (21,9) * 6v componentwise.
    Row 0: 3*(6,0) + 1*(7,-3) + 2*(-12,6) + 2*(9,-3) = (18,0)+(7,-3)+(-24,12)+(18,-6) = (19,3)
    phi^4 * 6*v_0 = ((7+3s)/2)*6 = (21+9s) ... need to be more careful.

    Let me instead verify using the matrix-vector product directly in Z[sqrt(5)]. *)

(** 4-vector over Z[sqrt(5)]. *)
Definition q5_vec4 := (quad 5 * quad 5 * quad 5 * quad 5)%type.

(** Left eigenvector product: v^T * M where M is over Z and v is over Z[sqrt(5)].
    Column j of result = sum_i (v_i * M[i][j]).
    This is the transpose multiplication M^T * v, which verifies left eigenvectors. *)
Definition hat_mat_T_vec_mul (v : q5_vec4) : q5_vec4 :=
  let '(v0, v1, v2, v3) := v in
  let lift := quad_of_Z 5 in
  let mul := quad_mul 5 in
  let add := quad_add 5 in
  (* Column 0: 3*v0 + 1*v1 + 2*v2 + 2*v3 *)
  ( add (add (mul (lift 3) v0) (mul (lift 1) v1))
        (add (mul (lift 2) v2) (mul (lift 2) v3)),
  (* Column 1: 1*v0 + 0*v1 + 0*v2 + 0*v3 *)
    mul (lift 1) v0,
  (* Column 2: 3*v0 + 0*v1 + 1*v2 + 1*v3 *)
    add (mul (lift 3) v0)
        (add (mul (lift 1) v2) (mul (lift 1) v3)),
  (* Column 3: 3*v0 + 0*v1 + 2*v2 + 3*v3 *)
    add (mul (lift 3) v0)
        (add (mul (lift 2) v2) (mul (lift 3) v3)) ).

(** Scalar multiplication of a 4-vector by a Z[sqrt(5)] element. *)
Definition q5_vec4_scale (s : quad 5) (v : q5_vec4) : q5_vec4 :=
  let '(v0, v1, v2, v3) := v in
  let mul := quad_mul 5 in
  (mul s v0, mul s v1, mul s v2, mul s v3).

(** The eigenvector for verification. Using the "times 6" form to stay in Z[sqrt(5)]:
    6*v = [(6,0), (7,-3), (-12,6), (9,-3)] where entries are (a, b) = a + b*sqrt(5).

    Actually, let's use the simplest form. The unnormalized eigenvector is
    [1, 5-3*phi, 6*phi-9, 6-3*phi] where phi = (1+sqrt(5))/2.

    In Z[sqrt(5)] with "times 2" representation (to clear the phi denominator):
    2*v = [(2,0), (10-3-3s, ...) ]
    Hmm, this gets messy. Let me just verify with concrete "times 2" elements.

    2*[1, 5-3*phi, 6*phi-9, 6-3*phi]
    = [2, 10-3*(1+s), 6*(1+s)-18, 12-3*(1+s)]
    = [(2,0), (7,-3), (-12,6), (9,-3)] *)

Definition hat_eigvec_2x : q5_vec4 :=
  (mkQuad 2 0, mkQuad 7 (-3), mkQuad (-12) 6, mkQuad 9 (-3)).

(** M * (2v) should equal phi^4 * (2v).
    Since 2*phi^4 = (7, 3), we have phi^4 * (2v) = (7+3s)/2 * (2v) = (7+3s)*v.
    But we're computing M * (2v) which should give 2 * phi^4 * v = (7+3s) * v.
    Hmm, M * (2v) = 2 * (M * v) = 2 * phi^4 * v = (7+3s) * v.
    But (7+3s) * v is NOT the same as phi^4 * (2v) = (7+3s)/2 * (2v) = (7+3s) * v.
    OK so they match: M * (2v) = (7+3s) * v = phi^4 * (2v). Wait:
    phi^4 = (7+3s)/2, so phi^4 * (2v) = (7+3s) * v.
    But M * (2v) = 2 * M * v = 2 * phi^4 * v = 2 * (7+3s)/2 * v = (7+3s) * v. ✓

    So: M * hat_eigvec_2x = scale two_perron hat_eigvec_2x / 2.
    That doesn't simplify nicely. Instead, let's verify:
    2 * M * hat_eigvec_2x = two_perron * hat_eigvec_2x.
    No, that gives 4 * phi^4 * v.

    Simplest: verify M * (2v) componentwise equals (7+3s) * v where v = [1, ...].
    But v has irrational entries. Let me just check with the "raw" definition. *)

(** Direct verification: M * hat_eigvec_2x = q5_vec4_scale two_perron [1, ...].
    Actually: since 2v_i are elements of Z[sqrt(5)], M * (2v) is well-defined,
    and should equal phi^4 * (2v) = two_perron/2 * hat_eigvec_2x... this is circular.

    The cleanest approach: verify hat_mat_vec_mul hat_eigvec_2x = q5_vec4_scale half_perron hat_eigvec_2x
    where half_perron would require fractions. Since we're in Z, let's multiply both sides by 2:
    2 * hat_mat_vec_mul hat_eigvec_2x = q5_vec4_scale two_perron hat_eigvec_2x. *)

(** Verify the left eigenvector: M^T * (2v) = (7+3s) * v.
    Since phi^4 = (7+3s)/2 and v = [1, (7-3s)/2, ...], working in the 2x
    representation avoids fractions. We verify M^T * (2v) directly:

    M^T * (2v):
    Col 0: 3*2 + 1*(7-3s) + 2*(-12+6s) + 2*(9-3s) = 6+7-3s-24+12s+18-6s = (7, 3)
    Col 1: 1*2                                       = (2, 0)
    Col 2: 3*2 + (-12+6s) + (9-3s)                   = 6-12+6s+9-3s = (3, 3)
    Col 3: 3*2 + 2*(-12+6s) + 3*(9-3s)               = 6-24+12s+27-9s = (9, 3)

    And (7+3s) * v where v = [(1,0), (7,-3)/2, (-12,6)/2, (9,-3)/2]:
    For integer check: 2*(7+3s)*v = (7+3s)*(2v) should equal 2*(M^T * (2v)).
    (7+3s)*(2,0) = (14, 6)   vs  2*(7,3) = (14, 6) ✓
    (7+3s)*(7,-3) = (4, 0)   vs  2*(2,0) = (4, 0)  ✓
    (7+3s)*(-12,6) = (6, 6)  vs  2*(3,3) = (6, 6)  ✓
    (7+3s)*(9,-3) = (18, 6)  vs  2*(9,3) = (18, 6)  ✓ *)

(** M^T * (2v) computes to these specific values. *)
Theorem hat_perron_left_eigvec_MT :
  hat_mat_T_vec_mul hat_eigvec_2x =
  (mkQuad 7 3, mkQuad 2 0, mkQuad 3 3, mkQuad 9 3).
Proof. vm_compute. reflexivity. Qed.

(** (7+3s) * (2v) = 2 * (M^T * (2v)), confirming the eigenvector equation.
    This verifies v^T M = phi^4 v^T. *)
Theorem hat_perron_eigvec_scaled :
  q5_vec4_scale two_perron hat_eigvec_2x =
  (mkQuad 14 6, mkQuad 4 0, mkQuad 6 6, mkQuad 18 6).
Proof. vm_compute. reflexivity. Qed.

(** The eigenvector components sum to 3 (before normalization to frequencies). *)
Theorem hat_eigvec_sum :
  let '(v0, v1, v2, v3) := hat_eigvec_2x in
  quad_add 5 (quad_add 5 v0 v1) (quad_add 5 v2 v3) = mkQuad 6 0.
Proof. vm_compute. reflexivity. Qed.

(** ** GAB Frequency Equation

    The Gähler-Akiyama-Baake equation for hat tilings:
      q^2 - q + 1/5 = 0
    where q is the Sturmian slope / symbol density for the hat tiling.

    The two roots are:
      q- = (5 - sqrt(5)) / 10  -- the Sturmian slope, equal to the continued
                                    fraction [0; 3, 1, 1, 1, ...] = 1/(2 + phi)
      q+ = (5 + sqrt(5)) / 10  -- the complementary symbol density (= 1 - q-)

    Note: these are NOT the Perron-Frobenius metatile instance frequencies.
    The PF frequency of the H-type metatile is f_H = 1/3 ≈ 0.333, which is
    distinct from q+ ≈ 0.724.  The GAB roots measure spatial / symbolic
    density in the associated Sturmian word, not the metatile instance ratio.

    Over Z, we verify the equivalent: 5*q^2 - 5*q + 1 = 0.
    The roots are q = (5 +/- sqrt(5)) / 10.

    In the "times 10" representation: 10*q = 5 +/- sqrt(5) = (5, +/-1) in Z[sqrt(5)].
    Verify: (10*q)^2 - 10*(10*q) + 20 = 0 (multiply 5*q^2 - 5*q + 1 = 0 by 20). *)

Definition ten_q_plus : quad 5 := mkQuad 5 1.    (* 10*q = 5 + sqrt(5) *)
Definition ten_q_minus : quad 5 := mkQuad 5 (-1). (* 10*q = 5 - sqrt(5) *)

(** 5*(10*q)^2 - 50*(10*q) + 100 = 0  (cleared denominators). *)
Theorem gab_equation_plus :
  let q := ten_q_plus in
  let q2 := quad_mul 5 q q in
  quad_add 5 (quad_sub 5 q2 (quad_mul 5 (mkQuad 10 0) q)) (mkQuad 20 0) = mkQuad 0 0.
Proof. vm_compute. reflexivity. Qed.

Theorem gab_equation_minus :
  let q := ten_q_minus in
  let q2 := quad_mul 5 q q in
  quad_add 5 (quad_sub 5 q2 (quad_mul 5 (mkQuad 10 0) q)) (mkQuad 20 0) = mkQuad 0 0.
Proof. vm_compute. reflexivity. Qed.

(** Product of GAB roots: q+ * q- = 1/5.
    (10*q+)(10*q-) = (5+s)(5-s) = 25-5 = 20.
    So 100*q+*q- = 20, giving q+*q- = 1/5. *)
Theorem gab_roots_product :
  quad_mul 5 ten_q_plus ten_q_minus = mkQuad 20 0.
Proof. vm_compute. reflexivity. Qed.

(** Sum of GAB roots: q+ + q- = 1.
    (10*q+) + (10*q-) = (5+s) + (5-s) = 10.
    So 10*(q+ + q-) = 10, giving q+ + q- = 1. *)
Theorem gab_roots_sum :
  quad_add 5 ten_q_plus ten_q_minus = mkQuad 10 0.
Proof. vm_compute. reflexivity. Qed.

(** ** Matrix Powers

    The substitution matrix M satisfies M^2 - 7*M + I (restricted to certain invariants).
    More precisely, M^2 has specific properties we verify. *)

Theorem hat_matrix_squared :
  mat_mul hat_matrix hat_matrix =
  mkMatrix 4 4 [22; 3; 15; 24; 3; 1; 3; 3; 12; 2; 9; 14; 14; 2; 10; 17].
Proof. vm_compute. reflexivity. Qed.

(** Trace of M^2 = 22 + 1 + 9 + 17 = 49. *)
Theorem hat_trace_squared : mat_trace (mat_mul hat_matrix hat_matrix) = 49.
Proof. vm_compute. reflexivity. Qed.

(** ** Hat Counts per Metatile

    Each metatile type contains a known number of actual hat tiles.
    H: 4 hats, T: 1 hat, P: 2 hats, F: 2 hats.
    The total hats vector [4, 1, 2, 2] relates metatile counts to hat counts. *)

Definition hats_per_metatile : list Z := [4; 1; 2; 2].

(** Total hats in H supertile = 3*4 + 1*1 + 3*2 + 3*2 = 12+1+6+6 = 25. *)
Theorem total_hats_H_supertile :
  mat_get hat_matrix 0 0 * 4 + mat_get hat_matrix 0 1 * 1 +
  mat_get hat_matrix 0 2 * 2 + mat_get hat_matrix 0 3 * 2 = 25.
Proof. vm_compute. reflexivity. Qed.
