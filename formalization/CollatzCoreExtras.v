(** CollatzCoreExtras.v *)
From Coq Require Import Arith.PeanoNat Arith.Arith.
From Coq Require Import micromega.Lia.
From Stdlib Require Import QArith Lqa Lia.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope nat_scope.

(** Small, re-usable facts (nat). *)

Lemma div_exact_by_mod (a d : nat) :
  d <> 0 ->
  a mod d = 0 ->
  d * (a / d) = a.
Proof.
  intros Hd Hz.
  pose proof (Nat.div_mod a d Hd) as H.
  rewrite Hz, Nat.add_0_r in H.
  symmetry. exact H.
Qed.

Lemma divide_mod0 (a d : nat) :
  d <> 0 -> a mod d = 0 -> Nat.divide d a.
Proof.
  intros Hd Hz.
  exists (a / d).
  rewrite Nat.mul_comm.
  symmetry. apply div_exact_by_mod; assumption.
Qed.

Corollary divides_iff_mod0 (a d : nat) :
  d <> 0 -> (Nat.divide d a <-> a mod d = 0).
Proof.
  intro Hd; split.
  - intros [q ->]. now rewrite Nat.Div0.mod_mul by exact Hd.
  - intro Hz. apply divide_mod0; assumption.
Qed.

Lemma mod_of_multiple_left (a d m : nat) :
  Nat.divide d a -> (a * m) mod d = 0.
Proof.
  intros [q Hq].                      (* a = d*q *)
  subst a.
  destruct d as [|d'].
  - (* d = 0 *) simpl. lia.   (* (0*m) mod 0 = 0 in Coq's nat semantics *)
  - (* d = S d' *)
    assert (Hassoc : (q * S d') * m = S d' * (q * m)).
    { rewrite Nat.mul_comm with (n := q) (m := S d').
      rewrite <- Nat.mul_assoc.
      reflexivity.
    }
    rewrite Hassoc.            (* (q * S d') * m = S d' * (q * m) *)
    rewrite Nat.mul_comm with (n := S d') (m := q * m).
    apply Nat.Div0.mod_mul.                (* (a*b) mod a = 0 when a<>0 *)    
Qed.

Lemma mod_of_multiple (a d m n : nat) :
  Nat.divide d a -> (m * a * n) mod d = 0.
Proof.
  intro Hd.
  rewrite (Nat.mul_comm m a).
  rewrite <- Nat.mul_assoc.
  apply mod_of_multiple_left.
  exact Hd.
Qed.

(** A simple “kill the multiple inside a mod” utility:
    (x + d*y) mod d = x mod d  *)
Lemma mod_add_kill_multiple (x y d : nat) :
  (x + d * y) mod d = x mod d.
Proof.
  destruct d as [|d'].
  - simpl. lia.
  -
  (* ensure the exact shape (x + y*d) mod d *)
  rewrite Nat.mul_comm.
  now rewrite (Nat.Div0.mod_add x y (S d')).  
Qed.

Lemma mod_idem_same' a d : (a mod d) mod d = a mod d.
Proof.
  destruct d as [|d']; [reflexivity|].
  now apply Nat.Div0.mod_mod.
Qed.

(** Classic factor reduction:
    ((x mod (d*c)) mod d) = x mod d, for c>0. *)
Lemma mod_reduce_factor
  (x d c : nat) :
  c > 0 ->
  (x mod (d * c)) mod d = x mod d.
Proof.
  intros Hcpos.
  destruct d as [|d'].
  - (* d = 0 *)
    (* In Coq, a mod 0 = a, so both sides are x. *)
    simpl. reflexivity.
  - (* d = S d' *)
    set (D := S d' * c).
    assert (HD : D <> 0) by (unfold D; nia).
    (* Division algorithm at modulus D: x = D * (x / D) + (x mod D) *)
    pose proof (Nat.div_mod x D HD) as Hdecomp.
    (* Rewrite the RHS “x mod (S d')” using the decomposition of x at modulus D *)
    replace (x mod (S d')) with
      (((D * (x / D)) + (x mod D)) mod (S d'))
      by (rewrite <- Hdecomp; reflexivity).
    (* Split the sum under mod (S d') *)
    rewrite (Nat.Div0.add_mod (D * (x / D)) (x mod D) (S d')) by lia.
    assert (Hzero : (D * (x / D)) mod (S d') = 0).
    { apply mod_of_multiple_left.
      exists c. unfold D. lia.
    }
    rewrite Hzero.
    rewrite Nat.add_0_l.
    rewrite mod_idem_same'.
    reflexivity.
Qed.

(** Squeeze a multiple away on the left inside a sum of mods, then reduce *)
Lemma simplify_mod :
  forall k d x,
    d <> 0 ->
    ((k * d * (x / (k * d))) mod d + (x mod (k * d)) mod d) mod d
    = (x mod (k * d)) mod d.
Proof.
  intros k d x Hd.
  (* Name the two summands to apply add_mod comfortably. *)
  set (A := k * d * (x / (k * d))).
  set (B := x mod (k * d)).
  (* Turn (A mod d + B mod d) mod d back into (A + B) mod d. *)
  rewrite <- (Nat.Div0.add_mod A B d) by lia.
  (* Now split again to isolate the remainder of A. *)
  rewrite (Nat.Div0.add_mod A B d) by lia.
  (* Reduce A mod d to 0 since A is a multiple of d. *)
  unfold A.
  rewrite (Nat.mul_comm k d).            (* swap to expose d *)
  rewrite <- Nat.mul_assoc.              (* regroup as d * (k * ...) *)
  rewrite (Nat.mul_comm d k) in *.
  (* 2) Put the divisor d on the right so (X * d) mod d appears *)
  rewrite (Nat.mul_comm d (k * (x / (k * d)))).
  (* 3) Now (k * (x / (k*d)) * d) mod d = 0 *)
  rewrite (Nat.Div0.mod_mul (k * (x / (k * d))) d) by exact Hd.
  (* 4) Clean up the sum and the outer mod *)
  rewrite Nat.add_0_l.
  rewrite (Nat.Div0.mod_mod B d) by exact Hd.
  reflexivity.
Qed.
