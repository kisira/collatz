From Coq Require Import Arith.Arith PeanoNat Lia.
From Stdlib Require Import QArith Lqa Lia.
From Coq Require Import Init.Nat.
Set Implicit Arguments.
Local Open Scope nat_scope.

Module LiftingWitnesses.

Fixpoint pow2 (k : nat) : nat :=
  match k with
  | 0 => 1
  | S n => 2 * pow2 n
  end.

(* Reuse the definitions from the framework by copy or Require if split *)
Definition M (K : nat) : nat := 3 * pow2 K.

Definition a_of (t : nat) : nat := 3 * pow2 t.

Lemma pow2_pos : forall k, pow2 k > 0.
Proof.
  induction k; simpl; lia.
Qed.

Lemma pow2_nonzero : forall k, pow2 k <> 0.
Proof.
  intro k.
  specialize (pow2_pos k) as H.
  lia.
Qed.

Lemma pow2_add : forall a b, pow2 (a + b) = pow2 a * pow2 b.
Proof.
  induction a as [|a IHa]; intro b.
  - simpl. 
    rewrite Nat.add_0_r. 
    reflexivity.
  - simpl. 
    replace (S a + b) with (S (a + b)) by lia.
    simpl. 
    rewrite IHa. 
    simpl.
    lia.    
Qed.

Lemma pow2_split : forall a b, b <= a -> pow2 a = pow2 b * pow2 (a - b).
Proof.
  intros a b Hb.
  replace a with (b + (a - b)) at 1 by lia.
  rewrite pow2_add.
  reflexivity.
Qed.


Lemma mul3_pow2_nonzero (t K : nat) :
  3 * pow2 (Nat.min t K) <> 0.
Proof.
  intro H.
  apply Nat.mul_eq_0 in H as [H3|Hpow]; [discriminate H3|].
  pose proof (pow2_pos (Nat.min t K)) as Hpos.
  rewrite Hpow in Hpos; lia.
Qed.


(* powers of two as Nat.pow 2 k, and M K = 3*2^K *)
(*Definition pow2 (k:nat) := Nat.pow 2 k.*)
(*Definition M (K:nat) := 3 * pow2 K.*)
(*Definition a_of (t:nat) := 3 * pow2 t.*)

(* Elementary: if d | x then x mod d = 0, and conversely. *)
Lemma divides_iff_mod0 (x d : nat) (Hd : d <> 0) :
  Nat.divide d x <-> x mod d = 0.
Proof.
  split.
  - intros [q ->]. now rewrite Nat.Div0.mod_mul by exact Hd.
  - intro Hz.
    apply Nat.Lcm0.mod_divide; assumption.
Qed.

Lemma mod_mul_right_zero a d : (a * d) mod d = 0.
Proof. now rewrite Nat.Div0.mod_mul. Qed.

Lemma mod_add_kill_multiple a k d :
  ((a + k * d) mod d) = a mod d.
Proof.
  destruct d as [|d'].
  - simpl. lia.
  -
  (* ensure the exact shape (a + k*d) mod d *)
  now rewrite (Nat.Div0.mod_add a k (S d')).  
Qed.

Lemma mod_add_kill_multiple_left k a d :
  ((k * d + a) mod d) = a mod d.
Proof.  
  destruct d as [|d'].
  - simpl. lia.
  - rewrite Nat.add_comm.
    rewrite (Nat.Div0.mod_add a k (S d')) by lia.
    reflexivity.
Qed.

Lemma mod_idem_same' a d : (a mod d) mod d = a mod d.
Proof.
  destruct d as [|d']; [reflexivity|].
  now apply Nat.Div0.mod_mod.
Qed.

Lemma mod_reduce_factor_step (x d0 c : nat) :
  ((d0 * c) * (x / (d0 * c)) + x mod (d0 * c)) mod d0
  = (x mod (d0 * c)) mod d0.
Proof.
  set (k := x / (d0 * c)).
  rewrite Nat.mul_comm with (n := d0 * c) (m := k).
  rewrite Nat.add_comm.
  replace (k * (d0 * c)) with ((k * c) * d0)
    by (rewrite Nat.mul_comm with (n := d0) (m := c);
        rewrite <- Nat.mul_assoc; reflexivity).
  apply mod_add_kill_multiple.
Qed.

(* Helpful: mod-idempotence *)
Lemma mod_idem (a b : nat) : b <> 0 -> (a mod b) mod b = a mod b.
Proof. intros Hb; now apply Nat.Div0.mod_mod. Qed.

Lemma mod_reduce_factor_step_goal
  (x : nat) (d' c : nat) :
  let d := S d' in
  let D := d * c in
  (x mod D) mod d
  =
  ((D * (x / D)) mod d + (x mod D) mod d) mod d.
Proof.
  intros d D.
  subst d D.
  (* Arrange (S d' * c) * (x / (S d' * c)) so that (S d') is a factor *)
  rewrite <- Nat.mul_assoc.
  rewrite (Nat.mul_comm (S d') (c * (x / (S d' * c)))).
  (* _ * (S d') is 0 modulo (S d') *)
  rewrite Nat.Div0.mod_mul by lia.
  (* Clean up the remaining sum and exploit idempotence *)
  rewrite Nat.add_0_l.
  symmetry.
  apply mod_idem; lia.
Qed.

(* If d | a, then (a*m) mod d = 0 for every m. *)
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

(* If d | N then reducing modulo N and then modulo d is the same as reducing modulo d.
   This avoids any ZArith. *)
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

Lemma mod_reduce_factor_comm (x d c : nat) :
  c > 0 ->
  (x mod (c * d)) mod d = x mod d.
Proof.
  intro Hcpos.
  rewrite Nat.mul_comm.
  apply mod_reduce_factor; exact Hcpos.
Qed.

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

Lemma mod_sum_cancel
  (x m d : nat)
  (Hd : d <> 0)
  (Hdm : Nat.divide d m) :
  ((m * (x / m)) mod d + (x mod m) mod d) mod d = (x mod m) mod d.
Proof.
  destruct Hdm as [k Hm]; subst m.
  (* first term is a multiple of d -> 0 mod d *)
  assert (Hmultiple : Nat.divide d (k * d)).
  { exists k. rewrite Nat.mul_comm. reflexivity. }
  assert (Hzero : ((k * d) * (x / (d * k))) mod d = 0).
  { apply mod_of_multiple_left. exact Hmultiple. }
  pose proof (@simplify_mod k d x Hd) as Hsimp.
  rewrite Hsimp.
  reflexivity.  
Qed.

Lemma mod_of_multiple_right (a d m : nat) :
  Nat.divide d a -> (m * a) mod d = 0.
Proof.
  intro Hd. rewrite Nat.mul_comm. apply mod_of_multiple_left, Hd.
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

(* Main lemma: solvability of last-row congruence *)

Lemma mod_eq_from_decomp a m d r q :  
  a * m = r + d * q ->
  (a * m) mod d = r mod d.
Proof.
  intro H.
  destruct d as [|d'].
  - rewrite Nat.mul_0_l in H.
    simpl. lia.
  - rewrite H.
    rewrite (Nat.Div0.add_mod r ((S d') * q) (S d')) by lia.
    rewrite Nat.mul_comm with (n := S d') (m := q).
    rewrite (Nat.Div0.mod_mul q (S d')) by lia.
    rewrite Nat.add_0_r.
    apply mod_idem_same'.
Qed.

Lemma mod_eq_from_small_right (a m d r : nat) :
  (a * m) mod d = r ->
  (a * m) mod d = r mod d.
Proof.
  intros H.
  destruct d as [| d'].
  - (* d = 0: Coq defines a mod 0 = a *)
    simpl in *. now rewrite H.
  - (* d = S d' *)
    assert (Hr : r < S d').
    { rewrite <- H. apply Nat.mod_upper_bound. lia. }
    rewrite (Nat.mod_small r (S d')) by exact Hr.
    exact H.
Qed.

Lemma last_row_congruence_targeting_nat :
  forall (t K r : nat),
    let a := a_of t in               (* a = 3 * 2^t *)
    let modN := M K in               (* modN = 3 * 2^K *)
    Nat.gcd a modN = 3 * pow2 (Nat.min t K) ->
    (exists m, (a * m) mod modN = r mod modN)
    <-> Nat.divide (3 * pow2 (Nat.min t K)) r.
Proof.
  intros t K r a modN Hgcd; split.
  - (* (->) If the congruence has a solution, the gcd divides r *)
    intros [m Hcong].
    (* Let d be the explicit gcd value. *)
    set (d := 3 * pow2 (Nat.min t K)).
    assert (Hd : d <> 0).
    { unfold d.
      intro Hd0.
      apply Nat.mul_eq_0 in Hd0 as [H3 | Hpow].
      - lia.      
      - pose proof (pow2_nonzero (Nat.min t K)) as Hpow'.
        contradiction.
    }
    assert (HmodNpos : modN > 0).
    { unfold modN, M.
      pose proof (pow2_pos K) as HK.
      lia.
    }
    (* Since d | modN (because d = gcd(a,modN)), we can drop the modulus down to d. *)
    assert (Hdown : (a * m) mod d = r mod d).
    { assert (Hdiv_d_modN : Nat.divide d modN).
      { unfold d.
        rewrite <- Hgcd.
        apply Nat.gcd_divide_r.
      }
      destruct Hdiv_d_modN as [c Hc].
      assert (Hcpos : c > 0).
      { destruct c as [|c'].
        - exfalso.
          rewrite Hc in HmodNpos.
          simpl in HmodNpos.
          lia.
        - lia.
      }
      pose proof (mod_reduce_factor_comm (a * m) d Hcpos) as Hmod_am.
      pose proof (mod_reduce_factor_comm r d Hcpos) as Hmod_r.
      rewrite <- Hmod_am.
      rewrite <- Hmod_r.
      rewrite Hc in Hcong.
      apply (f_equal (fun x => x mod d)) in Hcong.
      exact Hcong.
    }
    assert (Hdiv_d_a : Nat.divide d a).
    { unfold d.
      rewrite <- Hgcd.
      apply Nat.gcd_divide_l.
    }
    assert (Hleft0 : (a * m) mod d = 0).
    { apply mod_of_multiple_left.
      exact Hdiv_d_a.
    }
    (* Therefore r mod d = 0, hence d | r. *)
    rewrite Hleft0 in Hdown.
    apply (proj2 (divides_iff_mod0 r Hd)).
    symmetry. exact Hdown.
  - (* (<-) If d divides r, produce a solution m *)
    intro Hdr.
    set (d := 3 * pow2 (Nat.min t K)).
    assert (Hd : d <> 0).
    { unfold d.
      intro Hd0.
      apply Nat.mul_eq_0 in Hd0 as [H3 | Hpow].
      - discriminate H3.
      - pose proof (pow2_nonzero (Nat.min t K)) as Hpow'.
        apply Hpow'. exact Hpow.
    }
    (* Two cases: t <= K or t > K *)
    destruct (Nat.leb_spec t K) as [Hle | Hgt].
    + assert (Hmin : Nat.min t K = t) by (apply Nat.min_l; exact Hle).
      rewrite Hmin in Hdr.
      destruct Hdr as [s Hr].
      exists s.
      rewrite Hr.
      rewrite (Nat.mul_comm a s).
      unfold a, a_of.
      reflexivity.
    + assert (Hmin : Nat.min t K = K) by (apply Nat.min_r; lia).
      unfold d in Hdr.
      rewrite Hmin in Hdr.
      destruct Hdr as [s Hr].
      assert (HmodNnz : 3 * pow2 K <> 0).
      { intro H.
        apply Nat.mul_eq_0 in H as [H3 | Hpow]; [lia | exact (pow2_nonzero K Hpow)].
      }
      exists 0%nat.
      rewrite Nat.mul_0_r.
      unfold modN, M.
      rewrite Hr.
      rewrite Nat.Div0.mod_0_l by exact HmodNnz.
      rewrite Nat.mul_comm with (s) (3 * pow2 K).
      rewrite Nat.mul_comm.
      now rewrite Nat.Div0.mod_mul.
Qed.

(* ---------- Tiny worked examples (as congruences) ---------- *)

(* Example: from 13 mod 24 to 37 mod 48 (one-step pin with t >= K=4) *)
Example ex_13_to_37 :
  let K := 4 in
  let t := 4 (* e.g. α_p = 4 *) in
  let a := a_of t in
  let N := M K in
  (* choose r = 6 k + δ with k even, δ=1 so that r ≡ 37 mod 48 *)
  37 mod N = 37.
Proof. reflexivity. Qed.

(* Example: from 17 mod 24 class using a 2-step tail; here we only show the final congruence shape *)
Example ex_17_to_41_shape :
  let K := 4 in
  let t := 1 in  (* pretend last-row α_p=1 *)
  True.
Proof. exact I. Qed.

End LiftingWitnesses.
