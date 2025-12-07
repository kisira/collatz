From Stdlib Require Import Arith.Arith Arith.PeanoNat Lia.

Module Sec21_Same_family_steering_menu_and_monotone_padding_across_columns.

(* A small helper for powers of 2 *)
Definition pow2 (k : nat) : nat := Nat.pow 2 k.

(* ---------------------------------------------------------------------- *)
(* Lemma 1: One-step composition with floor (algebraic core)             *)
(* ---------------------------------------------------------------------- *)

(**
   This is the algebraic heart of Lemma 21.1 (lem:one-step-floor):

   We assume we are at step t with
     x_t(m) = 6 (A m + B) + δ_t.
   Along the certified class, we know that
     A m + B = 3 * (A3 * m + B3) + r
   for some remainder r ∈ {0,1,2} and integers A3, B3.

   We now feed a next token T in column p of unified form
     x' = 6 ( 2^{α_p} u + k ) + δ_T
   where the floor input is u = m_t = A3*m + B3.

   The lemma states that x'(m) again has the invariant linear form
     x'(m) = 6 ( A' m + B' ) + δ_T
   with the explicit update
     A' = 2^{α_p} * A3,
     B' = 2^{α_p} * B3 + k.
*)

Lemma lem_one_step_floor :
  forall (A B r α_p k δ_t δ_T : nat) (m A3 B3 : nat),
    (* Decomposition of A m + B along the certified class *)
    A * m + B = 3 * (A3 * m + B3) + r ->
    r <= 2 ->  (* router remainder, not actually used algebraically here *)
    let m_t := A3 * m + B3 in
    let x_t := 6 * (A * m + B) + δ_t in
    let x'  := 6 * (pow2 α_p * m_t + k) + δ_T in
    exists A' B',
      x' = 6 * (A' * m + B') + δ_T
      /\ A' = pow2 α_p * A3
      /\ B' = pow2 α_p * B3 + k.
Proof.
  intros A B r α_p k δ_t δ_T m A3 B3 Hdecomp Hr_le2 m_t x_t x'.
  (* Expand x' using the definition of m_t *)
  unfold m_t, x' in *.
  (* x' = 6 * (2^{α_p} * (A3*m + B3) + k) + δ_T *)
  repeat rewrite Nat.mul_add_distr_l.
  repeat rewrite Nat.mul_add_distr_r.
  (* x' = 6 * (pow2 α_p * (A3*m) + pow2 α_p * B3 + k) + δ_T *)
  repeat rewrite Nat.mul_assoc.
  (* Now isolate the "A' m + B'" shape *)
  set (A' := pow2 α_p * A3).
  set (B' := pow2 α_p * B3 + k).
  exists A', B'.
  split.
  - (* main identity x' = 6 (A' m + B') + δ_T *)
    unfold A', B'.
    (* 6 * (pow2 α_p * (A3 * m) + (pow2 α_p * B3 + k)) + δ_T *)
    rewrite <- Nat.mul_assoc with (n := pow2 α_p) (m := A3) (p := m).
    lia.
  - split; reflexivity.
Qed.

(* ---------------------------------------------------------------------- *)
(* Lemma 2: Integrality of the floor-driven update                        *)
(* ---------------------------------------------------------------------- *)

(**
   This matches Lemma 21.2 (lem:integrality-floor-update) in spirit.

   We encode “(B - r)/3 and A/3 exist in ℤ” by giving witnesses A3,B3 with:
     A = 3 * A3,
     B - r = 3 * B3.

   Then:
     2^{α_p} * A  is still divisible by 3,
     2^{α_p} * (B - r) is still divisible by 3,

   and we can write
     A' = (2^{α_p}/3) A = 2^{α_p} * A3,
     B' = (2^{α_p}/3)(B - r) + k = 2^{α_p} * B3 + k
   as honest [nat] expressions.
*)

Lemma lem_integrality_floor_update :
  forall (A B r α_p : nat),
    forall A3 B3 : nat,
      A = 3 * A3 ->
      B - r = 3 * B3 ->
      Nat.divide 3 (pow2 α_p * A)
      /\ Nat.divide 3 (pow2 α_p * (B - r)).
Proof.
  intros A B r α_p A3 B3 HA HB.
  split.
  - (* 3 | 2^{α_p} * A *)
    unfold pow2.
    subst A.
    (* 2^α_p * (3*A3) = 3 * (2^α_p * A3) *)
    rewrite Nat.mul_assoc.
    assert (HdA : Nat.divide 3 (2 ^ α_p * 3 * A3)).
    {
      unfold Nat.divide.
      exists (2 ^ α_p * A3).
      lia.      
    }
    exact HdA.    
  - (* 3 | 2^{α_p} * (B - r) *)
    unfold pow2.    
    (* B - r = 3*B3 by hypothesis, so directly: *)
    rewrite HB.
    rewrite Nat.mul_assoc.
    unfold Nat.divide.
    exists (2 ^ α_p * B3).
    lia.    
Qed.

(* ---------------------------------------------------------------------- *)
(* Lemma 3: Monotone two-adic lift (pure arithmetic form)                 *)
(* ---------------------------------------------------------------------- *)

(**
   This is the arithmetic engine behind Lemma 21.3 (lem:monotone-lift):

   If a tail block in some same-family menu raises v2(A) by a fixed
   positive increment [delta], then by repeating it enough times you can
   make v2(A) exceed any target K.

   Here we abstract away the family and just prove the numeric fact:
   given an initial exponent v, a target K, and a positive delta, there
   exists n such that v + n*delta >= K.
*)

Lemma lem_monotone_lift :
  forall (v K delta : nat),
    delta > 0 ->
    exists n, v + n * delta >= K.
Proof.
  intros v K delta Hdelta.
  (* Very simple choice: take n = K. *)
  exists K.
  assert (Hdelta_ge1 : delta >= 1) by lia.
  assert (HKdelta : K * delta >= K * 1) by (apply Nat.mul_le_mono_nonneg_l; lia).
  simpl in HKdelta.
  lia.
Qed.

End Sec21_Same_family_steering_menu_and_monotone_padding_across_columns.
