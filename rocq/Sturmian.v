From Stdlib Require Import ZArith.
From Stdlib Require Import List.
From Stdlib Require Import Lia.
From Stdlib Require Import NArith.
From Stdlib Require Import Bool.
Import ListNotations.

Require Import RocqProofs.Primitives.

Open Scope Z_scope.

Set Default Proof Using "Type".

(** * Sturmian Words and the Hat Tiling

    Formal verification of Sturmian word properties, corresponding to
    crates/analysis/src/sturmian.rs.

    A Sturmian word is the simplest aperiodic infinite word, characterized
    by the complexity function p(n) = n + 1 for all n >= 1.

    Key results:
    - Fibonacci word morphism and central word recurrence
    - Central word lengths follow Fibonacci numbers
    - Complexity p(n) = n + 1 verified for concrete prefixes
    - Hat tiling continued fraction [0; 3, 1, 1, 1, ...]
    - Balance property (1-counts differ by at most 1)

    Reference: Lothaire, "Algebraic Combinatorics on Words", Ch. 2;
    Smith et al. (2023), "An aperiodic monotile". *)

(** ** Fibonacci Word Morphism

    The Fibonacci morphism sigma: 0 -> 01, 1 -> 0.
    Iterating from "0" produces the Fibonacci word. *)

Definition fib_morphism (c : Z) : list Z :=
  if Z.eqb c 0 then [0; 1] else [0].

Definition apply_morphism (w : list Z) : list Z :=
  flat_map fib_morphism w.

(** Iterated morphism: sigma^n("0"). *)
Fixpoint fib_word_iter (n : nat) : list Z :=
  match n with
  | O => [0]
  | S k => apply_morphism (fib_word_iter k)
  end.

(** ** Central Word Recurrence

    Central words (standard words) for the Fibonacci case:
      w_{-1} = [1], w_0 = [0]
      w_{n+1} = w_n ++ w_{n-1}  (since all partial quotients d_i = 1)

    For general continued fraction [0; d_1, d_2, ...]:
      w_{n+1} = w_n^{d_{n+1}} ++ w_{n-1} *)

(** Concatenate n copies of a list. *)
Fixpoint repeat_list {A : Type} (l : list A) (n : nat) : list A :=
  match n with
  | O => []
  | S k => l ++ repeat_list l k
  end.

(** General central word recurrence with partial quotients. *)
Fixpoint central_words_aux (pqs : list nat) (w_prev w_curr : list Z)
  : list (list Z) :=
  match pqs with
  | [] => []
  | d :: rest =>
    let w_next := repeat_list w_curr d ++ w_prev in
    w_next :: central_words_aux rest w_curr w_next
  end.

Definition central_words (pqs : list nat) : list (list Z) :=
  [1] :: [0] :: central_words_aux pqs [1] [0].

(** Fibonacci central words: all partial quotients = 1. *)
Definition fib_central_words (levels : nat) : list (list Z) :=
  central_words (List.repeat 1%nat levels).

(** Hat tiling central words: partial quotients [3, 1, 1, 1, ...]. *)
Definition hat_central_words (levels : nat) : list (list Z) :=
  central_words (3%nat :: List.repeat 1%nat (Nat.pred levels)).

(** ** Complexity Function

    p(n) = number of distinct subwords of length n.
    For a Sturmian word, p(n) = n + 1 for all n >= 1. *)

(** Extract all subwords of length n from a word. *)
Fixpoint subwords_of_length (w : list Z) (n : nat) : list (list Z) :=
  match w with
  | [] => if (n =? 0)%nat then [[]] else []
  | x :: rest =>
    if (n =? 0)%nat then [[]]
    else if (length (x :: rest) <? n)%nat then []
    else firstn n (x :: rest) :: subwords_of_length rest n
  end.

(** Check if two Z-lists are equal (decidable). *)
Fixpoint list_Z_eqb (l1 l2 : list Z) : bool :=
  match l1, l2 with
  | [], [] => true
  | x :: xs, y :: ys => Z.eqb x y && list_Z_eqb xs ys
  | _, _ => false
  end.

(** Check if a list is already in a list of lists. *)
Fixpoint mem_list (x : list Z) (ls : list (list Z)) : bool :=
  match ls with
  | [] => false
  | h :: t => if list_Z_eqb x h then true else mem_list x t
  end.

(** Remove duplicates from a list of lists. *)
Fixpoint dedup_lists (ls : list (list Z)) : list (list Z) :=
  match ls with
  | [] => []
  | h :: t =>
    if mem_list h t then dedup_lists t
    else h :: dedup_lists t
  end.

(** Complexity function: number of distinct subwords of length n. *)
Definition complexity (w : list Z) (n : nat) : nat :=
  length (dedup_lists (subwords_of_length w n)).

(** Frequency counting. *)
Definition count_ones (w : list Z) : nat :=
  length (filter (Z.eqb 1) w).

(** ** Verified Properties *)

(** *** Fibonacci Morphism Iterations *)

Theorem fib_word_0 : fib_word_iter 0 = [0].
Proof. reflexivity. Qed.

Theorem fib_word_1 : fib_word_iter 1 = [0; 1].
Proof. vm_compute. reflexivity. Qed.

Theorem fib_word_2 : fib_word_iter 2 = [0; 1; 0].
Proof. vm_compute. reflexivity. Qed.

Theorem fib_word_3 : fib_word_iter 3 = [0; 1; 0; 0; 1].
Proof. vm_compute. reflexivity. Qed.

Theorem fib_word_4 : fib_word_iter 4 = [0; 1; 0; 0; 1; 0; 1; 0].
Proof. vm_compute. reflexivity. Qed.

Theorem fib_word_5 :
  fib_word_iter 5 = [0; 1; 0; 0; 1; 0; 1; 0; 0; 1; 0; 0; 1].
Proof. vm_compute. reflexivity. Qed.

(** *** Fibonacci Word Lengths

    length(sigma^n("0")) follows the Fibonacci sequence:
    1, 2, 3, 5, 8, 13, 21, 34, ... *)

Theorem fib_word_len_0 : length (fib_word_iter 0) = 1%nat.
Proof. vm_compute. reflexivity. Qed.

Theorem fib_word_len_1 : length (fib_word_iter 1) = 2%nat.
Proof. vm_compute. reflexivity. Qed.

Theorem fib_word_len_2 : length (fib_word_iter 2) = 3%nat.
Proof. vm_compute. reflexivity. Qed.

Theorem fib_word_len_3 : length (fib_word_iter 3) = 5%nat.
Proof. vm_compute. reflexivity. Qed.

Theorem fib_word_len_4 : length (fib_word_iter 4) = 8%nat.
Proof. vm_compute. reflexivity. Qed.

Theorem fib_word_len_5 : length (fib_word_iter 5) = 13%nat.
Proof. vm_compute. reflexivity. Qed.

Theorem fib_word_len_6 : length (fib_word_iter 6) = 21%nat.
Proof. vm_compute. reflexivity. Qed.

Theorem fib_word_len_7 : length (fib_word_iter 7) = 34%nat.
Proof. vm_compute. reflexivity. Qed.

(** The length recurrence: len(sigma^{n+1}) = len(sigma^n) + len(sigma^{n-1}). *)
Theorem fib_word_len_recurrence_5 :
  length (fib_word_iter 5) =
  (length (fib_word_iter 4) + length (fib_word_iter 3))%nat.
Proof. vm_compute. reflexivity. Qed.

Theorem fib_word_len_recurrence_6 :
  length (fib_word_iter 6) =
  (length (fib_word_iter 5) + length (fib_word_iter 4))%nat.
Proof. vm_compute. reflexivity. Qed.

Theorem fib_word_len_recurrence_7 :
  length (fib_word_iter 7) =
  (length (fib_word_iter 6) + length (fib_word_iter 5))%nat.
Proof. vm_compute. reflexivity. Qed.

(** *** Central Word Properties *)

(** Fibonacci central words match expected values. *)
Theorem fib_central_w_neg1 : nth 0 (fib_central_words 6) [] = [1].
Proof. vm_compute. reflexivity. Qed.

Theorem fib_central_w_0 : nth 1 (fib_central_words 6) [] = [0].
Proof. vm_compute. reflexivity. Qed.

Theorem fib_central_w_1 : nth 2 (fib_central_words 6) [] = [0; 1].
Proof. vm_compute. reflexivity. Qed.

Theorem fib_central_w_2 : nth 3 (fib_central_words 6) [] = [0; 1; 0].
Proof. vm_compute. reflexivity. Qed.

Theorem fib_central_w_3 : nth 4 (fib_central_words 6) [] = [0; 1; 0; 0; 1].
Proof. vm_compute. reflexivity. Qed.

(** Central word lengths follow Fibonacci sequence. *)
Theorem fib_central_lengths :
  map (@length Z) (fib_central_words 8) =
  [1%nat; 1%nat; 2%nat; 3%nat; 5%nat; 8%nat; 13%nat; 21%nat; 34%nat; 55%nat].
Proof. vm_compute. reflexivity. Qed.

(** *** Morphism-Central Word Agreement

    The Fibonacci word (from morphism iteration) agrees with
    the central word recurrence: sigma^n("0") = w_n. *)

Theorem morphism_central_agree_2 :
  fib_word_iter 2 = nth 3 (fib_central_words 6) [].
Proof. vm_compute. reflexivity. Qed.

Theorem morphism_central_agree_3 :
  fib_word_iter 3 = nth 4 (fib_central_words 6) [].
Proof. vm_compute. reflexivity. Qed.

Theorem morphism_central_agree_4 :
  fib_word_iter 4 = nth 5 (fib_central_words 6) [].
Proof. vm_compute. reflexivity. Qed.

Theorem morphism_central_agree_5 :
  fib_word_iter 5 = nth 6 (fib_central_words 6) [].
Proof. vm_compute. reflexivity. Qed.

(** *** Sturmian Complexity: p(n) = n + 1

    We verify the fundamental Sturmian property on a concrete prefix.
    Using fib_word_iter 7 (length 34) gives sufficient room. *)

Definition fib_test_word : list Z := fib_word_iter 7.

Theorem fib_test_word_length : length fib_test_word = 34%nat.
Proof. vm_compute. reflexivity. Qed.

(** p(n) = n + 1 for n = 1..10. *)
Theorem sturmian_complexity_1 : complexity fib_test_word 1 = 2%nat.
Proof. vm_compute. reflexivity. Qed.

Theorem sturmian_complexity_2 : complexity fib_test_word 2 = 3%nat.
Proof. vm_compute. reflexivity. Qed.

Theorem sturmian_complexity_3 : complexity fib_test_word 3 = 4%nat.
Proof. vm_compute. reflexivity. Qed.

Theorem sturmian_complexity_4 : complexity fib_test_word 4 = 5%nat.
Proof. vm_compute. reflexivity. Qed.

Theorem sturmian_complexity_5 : complexity fib_test_word 5 = 6%nat.
Proof. vm_compute. reflexivity. Qed.

Theorem sturmian_complexity_6 : complexity fib_test_word 6 = 7%nat.
Proof. vm_compute. reflexivity. Qed.

Theorem sturmian_complexity_7 : complexity fib_test_word 7 = 8%nat.
Proof. vm_compute. reflexivity. Qed.

Theorem sturmian_complexity_8 : complexity fib_test_word 8 = 9%nat.
Proof. vm_compute. reflexivity. Qed.

Theorem sturmian_complexity_9 : complexity fib_test_word 9 = 10%nat.
Proof. vm_compute. reflexivity. Qed.

Theorem sturmian_complexity_10 : complexity fib_test_word 10 = 11%nat.
Proof. vm_compute. reflexivity. Qed.

(** *** Frequency Counting

    The Fibonacci word has symbol frequencies approaching 1/phi^2 (ones)
    and 1/phi (zeros). For fib_word_iter 7 (length 34):
    - 13 ones (freq ~0.382 ~ 1/phi^2)
    - 21 zeros (freq ~0.618 ~ 1/phi) *)

Theorem fib_word_7_ones : count_ones (fib_word_iter 7) = 13%nat.
Proof. vm_compute. reflexivity. Qed.

Theorem fib_word_7_zeros :
  length (filter (Z.eqb 0) (fib_word_iter 7)) = 21%nat.
Proof. vm_compute. reflexivity. Qed.

(** The counts are consecutive Fibonacci numbers: 13 + 21 = 34. *)
Theorem fib_word_7_total : (13 + 21 = 34)%nat.
Proof. reflexivity. Qed.

(** *** Hat Tiling Central Words

    The hat tiling slope (5 - sqrt(5))/10 has continued fraction
    [0; 3, 1, 1, 1, ...]. The first partial quotient is 3,
    then all subsequent ones are 1 (golden continued fraction). *)

(** w_1 = w_0^3 w_{-1} = "000" ++ "1" = [0,0,0,1]. *)
Theorem hat_central_w_1 : nth 2 (hat_central_words 4) [] = [0; 0; 0; 1].
Proof. vm_compute. reflexivity. Qed.

(** w_2 = w_1 w_0 = [0,0,0,1] ++ [0] = [0,0,0,1,0]. *)
Theorem hat_central_w_2 : nth 3 (hat_central_words 4) [] = [0; 0; 0; 1; 0].
Proof. vm_compute. reflexivity. Qed.

(** w_3 = w_2 w_1 = [0,0,0,1,0] ++ [0,0,0,1] = [0,0,0,1,0,0,0,0,1]. *)
Theorem hat_central_w_3 :
  nth 4 (hat_central_words 4) [] = [0; 0; 0; 1; 0; 0; 0; 0; 1].
Proof. vm_compute. reflexivity. Qed.

(** Hat central word lengths. The sequence starts 1, 1, 4, 5, 9, 14, 23, 37
    following the generalized Fibonacci recurrence a_{n+1} = a_n + a_{n-1}
    but with a_1 = 4 (due to d_1 = 3). *)
Theorem hat_central_lengths :
  map (@length Z) (hat_central_words 6) =
  [1%nat; 1%nat; 4%nat; 5%nat; 9%nat; 14%nat; 23%nat; 37%nat].
Proof. vm_compute. reflexivity. Qed.

(** *** Balance Property

    A binary word is balanced if for every n, all subwords of length n
    have 1-counts differing by at most 1. This is equivalent to
    being Sturmian (for an infinite word).

    We verify this for small n on a concrete prefix. *)

Definition subword_ones_range (w : list Z) (n : nat) : (nat * nat) :=
  let subs := dedup_lists (subwords_of_length w n) in
  let counts := map (fun s => count_ones s) subs in
  (fold_left Nat.min (tl counts) (hd 0%nat counts),
   fold_left Nat.max (tl counts) (hd 0%nat counts)).

(** For n=3: min ones = 1, max ones = 2, difference = 1. *)
Theorem fib_balanced_3 :
  subword_ones_range fib_test_word 3 = (1%nat, 2%nat).
Proof. vm_compute. reflexivity. Qed.

(** For n=5: min ones = 1, max ones = 2, difference = 1. *)
Theorem fib_balanced_5 :
  subword_ones_range fib_test_word 5 = (1%nat, 2%nat).
Proof. vm_compute. reflexivity. Qed.

(** For n=8: min ones = 3, max ones = 4, difference = 1. *)
Theorem fib_balanced_8 :
  subword_ones_range fib_test_word 8 = (3%nat, 4%nat).
Proof. vm_compute. reflexivity. Qed.
