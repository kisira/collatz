From Coq Require Import Arith.Arith Arith.PeanoNat Lia.
From Coq Require Import Classes.RelationClasses.
From Coq Require Import Lists.List.
Import ListNotations.

Module Sec14_Samefamily_padding_as_emphsteering.

(** Section 14 — Same-family padding as steering (exponent-based) *)

(* project-wide items assumed available *)
Parameter Row : Type.
Parameter table : list Row.
Parameter alpha : Row -> nat.
Parameter delta : Row -> nat.
Definition pow2 (e:nat) := Nat.pow 2 e.
Definition forward_image (x e:nat) := (pow2 e * x - 1) / 3.
Parameter row_step : Row -> nat -> nat -> nat.

(* From earlier sections *)
Parameter affine_step_divNat :
  forall (r:Row) p m j pf x,
    x = 18*m + 6*j + pf -> (pf = 1 \/ pf = 5) ->
    row_step r p m = (pow2 (alpha r + 6*p) * x - 1) / 3
 /\ (pow2 (alpha r + 6*p) * x - 1) mod 3 = 0.

Parameter many_rows_realize_the_same_forward_image :
  forall x e : nat,
    x mod 2 = 1 -> x mod 3 <> 0 ->
    let a := e mod 6 in let p := e / 6 in
    forall m j pf : nat,
      pf = 1 \/ pf = 5 ->
      x = 18*m + 6*j + pf -> j < 3 ->
    forall r : Row,
      In r table -> delta r = pf -> alpha r = a ->
      row_step r p m = forward_image x e.

(* ---------- Exponent padding: e' = e + 6t (same super-family a = e mod 6) ---------- *)

Definition pad_exp (e t:nat) := e + 6*t.

Lemma mod_simpl_t6 (t e:nat) :
  ((t mod 6 * (6 mod 6)) mod 6 + e mod 6) mod 6 = e mod 6.
Proof.
  rewrite Nat.Div0.mod_same by lia.          (* 6 mod 6 = 0 *)
  rewrite Nat.mul_0_r.                  (* (t mod 6) * 0 = 0 *)
  rewrite Nat.Div0.mod_0_l by lia.           (* 0 mod 6 = 0 *)
  rewrite Nat.add_0_l.
  rewrite Nat.Div0.mod_mod by lia.           (* (e mod 6) mod 6 = e mod 6 *)
  reflexivity.
Qed.

Lemma pad_preserves_a : forall e t, (pad_exp e t) mod 6 = e mod 6.
Proof. intros e t; unfold pad_exp; rewrite Nat.add_comm, Nat.Div0.add_mod by lia.
  replace (6 * t) with (t * 6) by lia.
  rewrite Nat.Div0.mul_mod by lia.
  apply mod_simpl_t6.  
Qed.

(* Canonical “padded” forward image *)
Definition F_pad (x e t:nat) := forward_image x (pad_exp e t).

(* Any row r with alpha r = e mod 6 realizes the padded forward image at e' *)
Lemma padded_forward_image_realized
  (x e m j pf t : nat) (r : Row) :
  x mod 2 = 1 -> x mod 3 <> 0 ->
  (pf = 1 \/ pf = 5) -> x = 18*m + 6*j + pf -> j < 3 ->
  In r table -> alpha r = e mod 6 -> delta r = pf ->
  row_step r ((pad_exp e t) / 6) m = F_pad x e t.
Proof.
  intros Hodd Hne3 Hpf Hx Hj Hin Hα Hδ.
  unfold F_pad, pad_exp.
  (* we need alpha r = (e + 6*t) mod 6; use the preservation lemma *)
  assert (Hα' : alpha r = (e + 6*t) mod 6).
  { rewrite Nat.add_comm.
    rewrite Nat.Div0.add_mod by lia.
    rewrite Nat.Div0.mul_mod by lia.
    (* Goal: alpha r = ((6 mod 6 * (t mod 6)) mod 6 + e mod 6) mod 6 *)
    rewrite Hα.  (* goal becomes: e mod 6 = ((6 mod 6 * (t mod 6)) mod 6 + e mod 6) mod 6 *)
    rewrite Nat.Div0.mod_same by lia.   (* 6 mod 6 = 0 *)
    replace (0 * (t mod 6)) with 0 by lia.
    symmetry.  
    (* Goal: (0 mod 6 + e mod 6) mod 6 = e mod 6 *)
    rewrite Nat.Div0.mod_0_l by lia.   (* 0 mod 6 = 0 since 6<>0 *)
    rewrite Nat.add_0_l.          (* (0 + e mod 6) -> e mod 6 *)
    rewrite Nat.Div0.mod_mod by lia.   (* (e mod 6) mod 6 -> e mod 6 *)
    reflexivity.
  }
  (* Goal: row_step r ((e + 6 * t) / 6) m = forward_image x (e + 6 * t) *)
  set (e' := e + 6 * t).
  eapply many_rows_realize_the_same_forward_image
    with (x:=x) (e:=e') (m:=m) (j:=j) (pf:=pf) (r:=r); eauto.
  (* generated subgoals are discharged by your hypotheses: *)
  (*  - x mod 2 = 1           : exact Hodd *)
  (*  - x mod 3 <> 0          : exact Hne3 *)
  (*  - pf = 1 \/ pf = 5      : exact Hpf *)
  (*  - x = 18*m + 6*j + pf   : exact Hx *)
  (*  - j < 3                 : exact Hj *)
  (*  - In r table            : exact Hin *)
  (*  - delta r = pf          : exact Hδ *)
  (*  - alpha r = e' mod 6    : unfold e'; exact Hα' *) 
Qed.

Lemma pow6_succ (t:nat) : 2 ^ (6 * S t) = 64 * 2 ^ (6 * t).
Proof.
  (* 6 * S t = 6*t + 6 *)
  replace (6 * S t) with (6 * t + 6) by lia.
  rewrite Nat.pow_add_r.                (* 2^(6t+6) = 2^(6t) * 2^6 *)
  rewrite Nat.mul_comm.                  (* = 2^6 * 2^(6t) *)
  reflexivity.                           (* and 2^6 computes to 64 *)
Qed.

Lemma pad_increment_closed (x e t:nat) :
  (2 ^ e * 2 ^ (6 * S t) * x - 1) / 3
  = (2 ^ e * 2 ^ (6 * t) * x - 1) / 3 + 21 * (2 ^ e * 2 ^ (6 * t)) * x.
Proof.
  (* Let B = 2^e * 2^(6t) * x *)
  set (B := 2 ^ e * 2 ^ (6 * t) * x).
  (* Rewrite the LHS using 2^(6*S t) = 64 * 2^(6*t) *)
  rewrite pow6_succ.
  (* LHS becomes (2^e * (64 * 2^(6t)) * x - 1) / 3. Reassociate to 64 * B. *)
  cbv [B].
  repeat rewrite Nat.mul_assoc. 
  (* 1) Reassociate to isolate B on both sides *)
  repeat rewrite Nat.mul_assoc.
  rewrite (Nat.mul_comm (2 ^ e) 64).
  repeat rewrite Nat.mul_assoc.
  (* 1) Reassociate to expose 64 * (2^e * 2^(6t) * x) *)
  assert (H64 :
    2 ^ e * 64 * 2 ^ (6 * t) * x = 64 * (2 ^ e * 2 ^ (6 * t) * x)).
  { repeat rewrite Nat.mul_assoc.
    rewrite (Nat.mul_comm (2 ^ e) 64).
    repeat rewrite Nat.mul_assoc.
    reflexivity. }
  replace (64 * 2 ^ e) with (2 ^ e * 64) by lia.
  rewrite H64.
  (* 2) Do the same on the RHS for the 21-factor *)
  assert (H21 :
    21 * 2 ^ e * 2 ^ (6 * t) * x = 21 * (2 ^ e * 2 ^ (6 * t) * x)).
  { repeat rewrite Nat.mul_assoc. reflexivity. }
  rewrite H21.
  (* 3) Now introduce B and use change *)  
  change ((64 * B - 1) / 3 = (B - 1) / 3 + 21 * B).
  (* 4) Finish the arithmetic *)
  replace (64 * B - 1) with ((B - 1) + 63 * B) by lia.
  rewrite Nat.add_comm.
  replace (63 * B + (B - 1)) with ((B - 1) + 63 * B) by lia.
  (* Put the numerator into (a + b*c) with c = 3 *)
  replace (63 * B) with ((21 * B) * 3) by lia.
  (* Now (B - 1 + (21*B)*3) / 3 = (B - 1)/3 + (21*B) *)
  rewrite Nat.div_add by lia.
  (* RHS is exactly what we want *)
  reflexivity.
Qed.

Lemma pad_monotone (x e t:nat) :
  1 <= x -> F_pad x e (S t) >= F_pad x e t.
Proof.
  intro Hx.
  (* remove the implication *)
  unfold F_pad, forward_image, pad_exp, pow2.
  rewrite !Nat.pow_add_r.
  rewrite pad_increment_closed.             (* use your expanded lemma *)
  (* Goal is now: (A + C) >= A, with A := (2^e*2^(6*t)*x - 1)/3 and C := 21*(2^e*2^(6*t))*x *)
  set (A := (2 ^ e * 2 ^ (6 * t) * x - 1) / 3).
  set (C := 21 * (2 ^ e * 2 ^ (6 * t)) * x).
  apply Nat.le_add_r.                       (* A <= A + C *)
Qed.

Lemma pow2_ge_1 : forall k, 1 <= 2 ^ k.
Proof.
  induction k as [|k IH]; simpl; lia.
Qed.

Lemma exists_pow2_ge : forall N, exists k, N <= 2 ^ k.
Proof.
  induction N as [|N [k IH]].
  - (* N = 0 *)
    exists 0. simpl. lia.
  - (* N = S N, with IH : N <= 2^k *)
    exists (S k).
    (* target: S N <= 2^(S k) *)
    transitivity (S (2 ^ k)).
    { (* subgoal 1: S N <= S (2^k) *)
      (* build the lifted inequality from IH *)
      pose proof (le_n_S _ _ IH) as H1.
      exact H1.
    }
    { (* subgoal 2: S (2^k) <= 2 ^ (S k) *)
      rewrite Nat.pow_succ_r'.                       (* 2^(S k) = 2^k * 2 *)
      replace (2 ^ k * 2) with (2 ^ k + 2 ^ k) by lia.
      replace (S (2 ^ k)) with (2 ^ k + 1) by lia.
      apply Nat.add_le_mono_l.
      (* 1 <= 2^k *)
      induction k as [|k IHk].
      simpl.
      lia.
      rewrite Nat.add_0_r.
      apply pow2_ge_1.
    }
Qed.


Lemma pad_reaches_any_target (x e T:nat) :
  1 <= x -> exists t, F_pad x e t >= T.
Proof.
  intro Hxpos.
  (* pick k with 3*T+1 <= 2^k *)
  destruct (exists_pow2_ge (3*T + 1)) as [k Hk].
  (* we will take t = k *)
  exists k.
  unfold F_pad, forward_image, pad_exp, pow2.
  rewrite Nat.pow_add_r.  (* 2^(e+6k) = 2^e * 2^(6k) *)
  (* 2^(e+6k) >= 2^k *)
  assert (Hbase : 2 ^ (e + 6 * k) >= 2 ^ k) by (apply Nat.pow_le_mono_r; lia).
  (* From Hk and Hbase: (3T+1) <= 2^k <= 2^(e+6k) *)
  assert (Hpow : 3*T + 1 <= 2 ^ (e + 6 * k)) by lia.
  (* Multiply both sides by x (x>=1): (3T+1)*x <= 2^(e+6k)*x *)
  assert (Hmul : (3*T + 1) * x <= 2 ^ (e + 6 * k) * x).
  { apply Nat.mul_le_mono_nonneg_r; [lia|exact Hpow]. }
  (* We want: (2^e * 2^(6*k) * x - 1)/3 >= T *)
  set (A := 2 ^ e * 2 ^ (6 * k) * x).
  (* Turn T into (3*T)/3 with 3≠0 *)
  assert (Hdiv3 : (3*T) / 3 = T)
    by (rewrite Nat.mul_comm; apply Nat.div_mul; lia).
  rewrite <- Hdiv3.  (* goal is now: (A - 1)/3 >= (3*T)/3 *)
  (* Now use monotonicity of /3: it suffices to compare numerators *)
  apply Nat.Div0.div_le_mono; try lia.  (* reduces to: A - 1 >= 3*T *)
  (* 1) From 1 <= x, get (3T+1) <= (3T+1)*x via monotonicity of multiplication *)
  assert (Hgrow1 : (3*T + 1) * 1 <= (3*T + 1) * x).
  { apply Nat.mul_le_mono_pos_l; [lia| exact Hxpos]. }
  (* Step 1: from 1 <= x, get (3T+1) <= (3T+1)*x *)
  assert (Hgrow : 3*T + 1 <= (3*T + 1) * x).
  { (* first build the version with “* 1” on the left *)
    assert (Htmp : (3*T + 1) * 1 <= (3*T + 1) * x).
    { apply Nat.mul_le_mono_nonneg_l; [lia| exact Hxpos]. }
    (* now simplify the left side of Htmp *)
    now rewrite Nat.mul_1_r in Htmp.
  }
  assert (HeqA : A = 2 ^ (e + 6 * k) * x).
  { unfold A. rewrite Nat.pow_add_r. reflexivity. }
  pose proof Hmul as HmulA.
  rewrite <- HeqA in HmulA.  (* rewrites RHS of HmulA to A *)
  (* Chain with Hgrow *)
  assert (HleA : 3*T + 1 <= A) by (eapply Nat.le_trans; [exact Hgrow | exact HmulA]).
  (* Finish *)
  lia.
Qed.


End Sec14_Samefamily_padding_as_emphsteering.
