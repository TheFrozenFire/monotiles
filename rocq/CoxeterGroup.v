From Stdlib Require Import ZArith.
From Stdlib Require Import List.
From Stdlib Require Import Lia.
Import ListNotations.

Require Import RocqProofs.Primitives.
Require Import RocqProofs.ModularArithmetic.
Require Import RocqProofs.GroupTheory.

Open Scope Z_scope.

Set Default Proof Using "Type".

(** * Coxeter Group Gamma = Z^2 ⋊ D_6

    Formal verification of the triangle Coxeter group used in aperiodic
    monotile theory. This corresponds to the Rust implementation in
    crates/domain/src/coxeter.rs.

    The group Gamma = <alpha, beta, gamma | alpha^2, beta^2, gamma^2,
    (alpha*beta)^6, (beta*gamma)^3, (alpha*gamma)^2> is isomorphic to
    the semidirect product Z^2 ⋊ D_6, where:
    - Z^2 is the hexagonal lattice translation group
    - D_6 is the dihedral group of order 12 (6 rotations + 6 reflections)

    Normal form: (tx, ty, rotation, reflected) where
    - tx, ty in Z (hexagonal lattice coordinates)
    - rotation in {0,1,2,3,4,5} (rotation by rotation * 60 degrees)
    - reflected in {0,1} (reflection flag) *)

(** ** Rotation Action on Hexagonal Lattice

    R_6 maps (a, b) -> (-b, a+b) (60 degree rotation in hexagonal coordinates).
    The full rotation table for R_6^r: *)

Definition rotate_hex (a b : Z) (r : Z) : Z * Z :=
  let r_mod := r mod 6 in
  if r_mod =? 0 then (a, b)
  else if r_mod =? 1 then (-b, a + b)
  else if r_mod =? 2 then (-a - b, a)
  else if r_mod =? 3 then (-a, -b)
  else if r_mod =? 4 then (b, -a - b)
  else (* r_mod = 5 *) (a + b, -a).

(** Rotation by 0 is identity. *)
Lemma rotate_hex_0 : forall a b, rotate_hex a b 0 = (a, b).
Proof. intros. reflexivity. Qed.

(** Rotation is periodic with period 6. *)
Lemma rotate_hex_period : forall a b r,
  rotate_hex a b r = rotate_hex a b (r mod 6).
Proof.
  intros a b r. unfold rotate_hex.
  rewrite Z.mod_mod by lia. reflexivity.
Qed.

(** Full rotation (R^6 = id). *)
Lemma rotate_hex_6 : forall a b, rotate_hex a b 6 = (a, b).
Proof. intros. reflexivity. Qed.

(** ** Reflection on Hexagonal Lattice

    sigma maps (a, b) -> (a+b, -b). *)

Definition reflect_hex (a b : Z) : Z * Z := (a + b, -b).

(** Reflection is an involution: sigma^2 = id. *)
Lemma reflect_hex_involution : forall a b,
  let '(a', b') := reflect_hex a b in
  reflect_hex a' b' = (a, b).
Proof.
  intros a b. unfold reflect_hex. f_equal; lia.
Qed.

(** ** Combined Action phi(r, s)

    phi(r, s)(v) = R^r(sigma^s(v))
    First apply reflection if s=1, then rotate. *)

Definition act_on (rot : Z) (rfl : Z) (a b : Z) : Z * Z :=
  let '(a', b') := if rfl =? 1 then reflect_hex a b else (a, b) in
  rotate_hex a' b' rot.

(** ** Coxeter Element: Normal Form *)

(** A Coxeter element in normal form (tx, ty, rotation, reflected). *)
Definition coxeter_element := semidirect_element.
Definition mkCoxeter := mkSDE.
Definition cox_tx := sde_tx.
Definition cox_ty := sde_ty.
Definition cox_rot := sde_rot.
Definition cox_refl := sde_refl.

(** ** Identity Element *)

Definition cox_identity : coxeter_element := mkCoxeter 0 0 0 0.

(** ** Generators *)

(** alpha = (0, 0, 0, 1) -- pure reflection *)
Definition cox_alpha : coxeter_element := mkCoxeter 0 0 0 1.

(** beta = (0, 0, 1, 1) -- rotation by 60 degrees composed with reflection *)
Definition cox_beta : coxeter_element := mkCoxeter 0 0 1 1.

(** gamma = (1, 0, 3, 1) -- translation + rotation by 180 degrees + reflection *)
Definition cox_gamma : coxeter_element := mkCoxeter 1 0 3 1.

(** ** Composition

    (v1, r1, s1) * (v2, r2, s2) = (v1 + phi(r1,s1)(v2), r1 + (-1)^s1 * r2 mod 6, s1 xor s2)

    When s1 = 1 (reflected): new_rotation = (r1 - r2) mod 6
    When s1 = 0 (not reflected): new_rotation = (r1 + r2) mod 6
    Reflection composes via XOR. *)

Definition cox_compose (g h : coxeter_element) : coxeter_element :=
  let '(av, bv) := act_on (cox_rot g) (cox_refl g) (cox_tx h) (cox_ty h) in
  let new_tx := cox_tx g + av in
  let new_ty := cox_ty g + bv in
  let new_rot :=
    if cox_refl g =? 1
    then (cox_rot g - cox_rot h) mod 6
    else (cox_rot g + cox_rot h) mod 6 in
  let new_refl :=
    if (cox_refl g + cox_refl h) =? 0 then 0
    else if (cox_refl g + cox_refl h) =? 2 then 0
    else 1 in
  mkCoxeter new_tx new_ty new_rot new_refl.

(** ** Inverse

    For (v, r, s):
    - If reflected: inverse is (r, true)^-1 = (r, true)
    - If not reflected: inverse is (6-r mod 6, false)
    - Translation: negate after applying inverse point group action *)

Definition cox_inverse (g : coxeter_element) : coxeter_element :=
  let inv_rot := if cox_refl g =? 1 then cox_rot g
                 else (6 - cox_rot g) mod 6 in
  let inv_refl := cox_refl g in
  let '(neg_ax, neg_ay) := act_on inv_rot inv_refl (cox_tx g) (cox_ty g) in
  mkCoxeter (-neg_ax) (-neg_ay) inv_rot inv_refl.

(** Helper: iterated composition. *)
Fixpoint cox_pow (g : coxeter_element) (n : nat) : coxeter_element :=
  match n with
  | O => cox_identity
  | S n' => cox_compose g (cox_pow g n')
  end.

(** ** Coxeter Relations: Machine-Checked Proofs

    We verify all 6 defining relations of the Coxeter group Gamma:
    alpha^2 = beta^2 = gamma^2 = (alpha*beta)^6 = (beta*gamma)^3 = (alpha*gamma)^2 = id *)

(** *** Involution Relations *)

Theorem alpha_squared : cox_compose cox_alpha cox_alpha = cox_identity.
Proof. vm_compute. reflexivity. Qed.

Theorem beta_squared : cox_compose cox_beta cox_beta = cox_identity.
Proof. vm_compute. reflexivity. Qed.

Theorem gamma_squared : cox_compose cox_gamma cox_gamma = cox_identity.
Proof. vm_compute. reflexivity. Qed.

(** *** Order Relations *)

Theorem alpha_beta_order_six :
  cox_pow (cox_compose cox_alpha cox_beta) 6 = cox_identity.
Proof. vm_compute. reflexivity. Qed.

Theorem beta_gamma_order_three :
  cox_pow (cox_compose cox_beta cox_gamma) 3 = cox_identity.
Proof. vm_compute. reflexivity. Qed.

Theorem alpha_gamma_order_two :
  cox_pow (cox_compose cox_alpha cox_gamma) 2 = cox_identity.
Proof. vm_compute. reflexivity. Qed.

(** *** Exact Orders (not just divisors) *)

Theorem alpha_beta_exact_order :
  cox_compose cox_alpha cox_beta <> cox_identity /\
  cox_pow (cox_compose cox_alpha cox_beta) 2 <> cox_identity /\
  cox_pow (cox_compose cox_alpha cox_beta) 3 <> cox_identity.
Proof.
  vm_compute. repeat split; intro H; discriminate H.
Qed.

Theorem beta_gamma_exact_order :
  cox_compose cox_beta cox_gamma <> cox_identity.
Proof. vm_compute. intro H. discriminate H. Qed.

Theorem alpha_gamma_exact_order :
  cox_compose cox_alpha cox_gamma <> cox_identity.
Proof. vm_compute. intro H. discriminate H. Qed.

(** ** Identity Properties *)

(** Identity is neutral for generators. *)
Theorem cox_identity_left_alpha : cox_compose cox_identity cox_alpha = cox_alpha.
Proof. vm_compute. reflexivity. Qed.

Theorem cox_identity_left_beta : cox_compose cox_identity cox_beta = cox_beta.
Proof. vm_compute. reflexivity. Qed.

Theorem cox_identity_left_gamma : cox_compose cox_identity cox_gamma = cox_gamma.
Proof. vm_compute. reflexivity. Qed.

Theorem cox_identity_right_alpha : cox_compose cox_alpha cox_identity = cox_alpha.
Proof. vm_compute. reflexivity. Qed.

Theorem cox_identity_right_beta : cox_compose cox_beta cox_identity = cox_beta.
Proof. vm_compute. reflexivity. Qed.

Theorem cox_identity_right_gamma : cox_compose cox_gamma cox_identity = cox_gamma.
Proof. vm_compute. reflexivity. Qed.

(** ** Inverse Properties *)

Theorem alpha_inverse : cox_compose cox_alpha (cox_inverse cox_alpha) = cox_identity.
Proof. vm_compute. reflexivity. Qed.

Theorem beta_inverse : cox_compose cox_beta (cox_inverse cox_beta) = cox_identity.
Proof. vm_compute. reflexivity. Qed.

Theorem gamma_inverse : cox_compose cox_gamma (cox_inverse cox_gamma) = cox_identity.
Proof. vm_compute. reflexivity. Qed.

(** Generators are self-inverse (involutions). *)

Theorem alpha_self_inverse : cox_inverse cox_alpha = cox_alpha.
Proof. vm_compute. reflexivity. Qed.

Theorem beta_self_inverse : cox_inverse cox_beta = cox_beta.
Proof. vm_compute. reflexivity. Qed.

Theorem gamma_self_inverse : cox_inverse cox_gamma = cox_gamma.
Proof. vm_compute. reflexivity. Qed.

(** ** Associativity (spot-checked on generators) *)

Theorem assoc_alpha_beta_gamma :
  cox_compose (cox_compose cox_alpha cox_beta) cox_gamma =
  cox_compose cox_alpha (cox_compose cox_beta cox_gamma).
Proof. vm_compute. reflexivity. Qed.

Theorem assoc_gamma_alpha_beta :
  cox_compose (cox_compose cox_gamma cox_alpha) cox_beta =
  cox_compose cox_gamma (cox_compose cox_alpha cox_beta).
Proof. vm_compute. reflexivity. Qed.

Theorem assoc_beta_gamma_alpha :
  cox_compose (cox_compose cox_beta cox_gamma) cox_alpha =
  cox_compose cox_beta (cox_compose cox_gamma cox_alpha).
Proof. vm_compute. reflexivity. Qed.

(** ** D_6 Point Group *)

(** The 12 elements of D_6 = Z/6Z x| Z/2Z. *)
Definition d6_elements : list coxeter_element :=
  [ mkCoxeter 0 0 0 0;
    mkCoxeter 0 0 1 0;
    mkCoxeter 0 0 2 0;
    mkCoxeter 0 0 3 0;
    mkCoxeter 0 0 4 0;
    mkCoxeter 0 0 5 0;
    mkCoxeter 0 0 0 1;
    mkCoxeter 0 0 1 1;
    mkCoxeter 0 0 2 1;
    mkCoxeter 0 0 3 1;
    mkCoxeter 0 0 4 1;
    mkCoxeter 0 0 5 1
  ].

(** D_6 has exactly 12 elements. *)
Lemma d6_count : length d6_elements = 12%nat.
Proof. reflexivity. Qed.

(** Encode a coxeter element as a single integer for distinctness proofs. *)
Definition cox_encode (g : coxeter_element) : Z :=
  cox_tx g * 1000000 + cox_ty g * 10000 + cox_rot g * 100 + cox_refl g.

(** All 12 D_6 elements are distinct. *)
Theorem d6_all_distinct :
  NoDup d6_elements.
Proof.
  assert (Hencs : NoDup (map cox_encode d6_elements)).
  {
    vm_compute.
    repeat (constructor; [simpl; intuition lia |]).
    constructor.
  }
  apply NoDup_map_inv in Hencs.
  exact Hencs.
Qed.

(** D_6 is closed under composition. *)
Theorem d6_closed : forall g h,
  In g d6_elements -> In h d6_elements ->
  In (cox_compose g h) d6_elements.
Proof.
  intros g h Hg Hh.
  simpl in Hg, Hh.
  decompose [or] Hg; decompose [or] Hh; subst; try contradiction;
  vm_compute; intuition.
Qed.

(** ** Rotation Properties *)

Theorem rotation_period_6 : forall a b,
  rotate_hex a b 6 = (a, b).
Proof. intros. reflexivity. Qed.

(** Composition of rotations. *)
Theorem rotate_compose : forall a b r1 r2,
  0 <= r1 < 6 -> 0 <= r2 < 6 ->
  let '(a', b') := rotate_hex a b r1 in
  rotate_hex a' b' r2 = rotate_hex a b ((r1 + r2) mod 6).
Proof.
  intros a b r1 r2 Hr1 Hr2.
  assert (r1 = 0 \/ r1 = 1 \/ r1 = 2 \/ r1 = 3 \/ r1 = 4 \/ r1 = 5) by lia.
  assert (r2 = 0 \/ r2 = 1 \/ r2 = 2 \/ r2 = 3 \/ r2 = 4 \/ r2 = 5) by lia.
  decompose [or] H; decompose [or] H0; subst;
  unfold rotate_hex; simpl; f_equal; lia.
Qed.
