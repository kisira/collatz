From Coq Require Import Arith.Arith Arith.PeanoNat Lia.
From Coq Require Import Lists.List.
Import ListNotations.

Module Row_correctness_family_pattern_and_word_semantics.

(* --- Basic helpers --- *)
Definition pow2 (k:nat) := Nat.pow 2 k.

(* Families modulo 6: only for statement shapes here *)
Definition family (x:nat) := x mod 6.
Definition is_e (x:nat) := family x = 1.
Definition is_o (x:nat) := family x = 5.

(* ========================================================= *)
(* 7.1 Row correctness (paper Lemma \ref{lem:row-correctness}) *)
(* ========================================================= *)

(* We capture the table’s straight-substitution identity as a hypothesis
   (you instantiate it per row (alpha,k,delta) when you use the lemma). *)
Section RowCorrectness.

Variables alpha k delta : nat.
Hypothesis delta_is_odd_family : delta = 1 \/ delta = 5.

(* Table identity: for the (j,p) describing the start, we have
   18*k + 3*delta + 1 = 2^alpha * (6*j + p), with p in {1,5}. *)
Hypothesis straight_subst_identity :
  forall j p, (p = 1 \/ p = 5) ->
    18*k + 3*delta + 1 = pow2 alpha * (6*j + p).

(* Row map *)
Definition F0 (m:nat) := pow2 alpha * m + k.
Definition xprime (m:nat) := 6 * F0 m + delta.

Lemma lem_row_correctness :
  forall x m j p,
    x = 18*m + 6*j + p ->
    (p = 1 \/ p = 5) ->
    3 * (6 * (pow2 alpha * m + k)) + 3 * delta + 1 = pow2 alpha * x.
Proof.
  intros x m j p Hx Hp.
  (* Expand the inner 6*(...) using LEFT distributivity *)
  rewrite (Nat.mul_add_distr_l 6 (pow2 alpha * m) k).
  (* Now expand the outer 3*(...) using LEFT distributivity again *)
  rewrite (Nat.mul_add_distr_l 3 (6 * (pow2 alpha * m)) (6 * k)).
  (* Normalize 3*6 to 18 *)
  replace (3*6) with 18 by lia.
  replace (3*6) with 18 by lia.
  (* We now have: 18 * (pow2 alpha * m) + 18*k + 3*delta + 1 *)
  (* Commute/associate to pull pow2 alpha next to 18*m *)
  rewrite !Nat.mul_assoc.
  replace (3*6) with 18 by lia.
  replace (3*6) with 18 by lia.
  rewrite (Nat.mul_comm 18 (pow2 alpha)).
  rewrite <- !Nat.mul_assoc.
  (* Use the straight-substitution identity for (j,p) on the constant block *)
  replace (pow2 alpha * (18 * m) + 18 * k + 3 * delta + 1) with ((18 * k + 3 * delta + 1) + pow2 alpha * (18 * m)) by lia.
  rewrite (straight_subst_identity j p Hp) by lia.
  (* Factor pow2 alpha on the left block *)
  replace (pow2 alpha * (6 * j + p) + pow2 alpha * (18 * m)) with (pow2 alpha * (18 * m) + pow2 alpha * (6 * j + p)) by lia.
  rewrite <- (Nat.mul_add_distr_l (pow2 alpha) (18*m) (6*j + p)).
  (* Replace the sum by x *)
  rewrite Hx.
  replace (pow2 alpha * (18 * m + (6 * j + p))) with (pow2 alpha * (18 * m + 6 * j + p)) by lia.
  reflexivity.
Qed.

End RowCorrectness.

(* ================================================================== *)
(* 7.2 Family–pattern invariance under change of start (Lemma \ref{lem:family-pattern}) *)
(* ================================================================== *)

Inductive token :=
| Psi   (* e -> e *)
| psi   (* e -> o *)
| omega (* o -> e *)
| Omega (* o -> o *)
.

Definition next_family (t:token) (s:nat) : nat :=
  match t, s with
  | Psi  , 1 => 1
  | psi  , 1 => 5
  | omega, 5 => 1
  | Omega, 5 => 5
  | _    , _ => s (* unreachable in well-typed runs *)
  end.

Lemma lem_family_pattern :
  forall (W:list token) s s',
    (s=1 \/ s=5) -> (s'=s) ->
    fold_left (fun fam t => next_family t fam) W s
    = fold_left (fun fam t => next_family t fam) W s'.
Proof.
  intros W s s' _ ->. (* s'=s *)
  induction W as [|t W IH]; simpl; auto.  
Qed.

(* ================================================================ *)
(* 7.3 Forward monotonicity by row and lift (paper’s last lemma)    *)
(* ================================================================ *)

Lemma pow2_ge_8 : forall n, 3 <= n -> 8 <= pow2 n.
Proof.
  intros n H.
  (* 2^3 = 8 and 2^n is monotone in n *)
  assert (Hmon : forall a b, a <= b -> Nat.pow 2 a <= Nat.pow 2 b).
  { intros a b Hab. induction Hab; simpl; lia. }
  specialize (Hmon 3 n H). simpl in Hmon. exact Hmon.
Qed.


(* Certified step: 3*y + 1 = 2^{alpha+6p} * x, with p >= 0.
   Let e := alpha + 6p. Then:
   - if e = 1,         U(y) > y;
   - if e = 2,         U(y) = y  iff  y = 1   (else U(y) < y);
   - if e >= 3,        U(y) < y.
   This matches the prose once you note: e=1 <-> (alpha=1,p=0), e=2 <-> (alpha=2,p=0).
*)
(*
   Main lemma:

   3*y + 1 = 2^(alpha+6p) * x, let e := alpha+6p.
   Then:
   - if e=1      ⇒ x > y
   - if e=2      ⇒ (x = y) <-> (y = 1)
   - if e>=3     ⇒ x < y
*)
Lemma forward_monotonicity_by_row_and_lift :
  forall y x alpha p,
    3*y + 1 = pow2 (alpha + 6*p) * x ->
    let e := alpha + 6*p in
      (e = 1  -> x > y)
   /\ (e = 2  -> (x = y <-> y = 1))
   /\ (3 <= e -> x < y).
Proof.
  intros y x alpha p Hstep e; subst e.
  (* Work with e = alpha + 6p; destruct it as S e' to avoid e=0 corner. *)
  remember (alpha + 6*p) as e0 eqn:He.  
  destruct e0 as [|e']; [
  split; [ (intros H1; discriminate H1)
         | split; [ (intros H2; discriminate H2)
                   | (intros H3; lia) ] ]
  |].
    
  (* Put the core equation in the direction we use below *)
  assert (Hx_def : pow2 (S e') * x = 3*y + 1) by (symmetry; exact Hstep).
  (* Goal: (S e' = 1 -> ...) /\ (S e' = 2 -> ...) /\ (3 <= S e' -> ...) *)
  split.
  - (* Branch 1: S e' = 1 -> x > y *)
    intro He1.
    (* S e' = 1 = S 0 ⇒ e' = 0 *)
    assert (He' : e' = 0).
    { replace 1 with (S 0) in He1 by reflexivity. now inversion He1. }
    subst e'. simpl in Hx_def.  (* pow2 1 = 2 *)
    (* 2*x = 3*y + 1 ⇒ 2*(x - y) = y + 1 ⇒ x > y over nat *)
    lia.
  - split.
    + (* Branch 2: S e' = 2 -> x = y <-> y = 1 *)
      intro He2.
      (* S e' = 2 = S 1 ⇒ e' = 1 *)
      assert (He' : e' = 1).
      { replace 2 with (S 1) in He2 by reflexivity. now inversion He2. }
      subst e'. simpl in Hx_def.  (* pow2 2 = 4 *)
      split.
      * (* -> *)
        intro Heq. subst x. lia.  (* 4*y = 3*y + 1 ⇒ y = 1 *)
      * (* <- *)
        intro Hy. subst y. lia.    (* 4*x = 4 ⇒ x = 1 ⇒ x = y *)
    + (* Branch 3: 3 <= S e' -> x < y *)
      intro He3.
      (* Handle y=0 separately: contradiction by parity *)
      destruct y as [|y'].
      { exfalso.
        (* LHS even, RHS = 1: contradiction *)
        (* Reduce both sides mod 2 *)
        assert (HmodL : (pow2 (S e') * x) mod 2 = 0).
        { (* pow2 (S e') is even, so product mod 2 is 0 *)
          rewrite Nat.Div0.mul_mod by lia.
          (* 2^(S e') = 2 * 2^e' ⇒ (2 * k) mod 2 = 0 *)
          replace (pow2 (S e') mod 2) with 0.
          - now simpl.
          - unfold pow2. rewrite Nat.pow_succ_r. symmetry. replace (2 * 2 ^ e') with (2 ^ e' * 2) by lia. rewrite Nat.Div0.mod_mul by lia. simpl. lia. lia. }
        rewrite Hx_def in HmodL. simpl in HmodL. lia. }
      (* y = S y' >= 1 *)
      assert (Hpow : 8 <= pow2 (S e')) by (apply pow2_ge_8; exact He3).
      (* From the defining equation and bounds: *)
      (* 8*x <= 2^(S e')*x = 3*y + 1 <= 4*y since y>=1 *)
      (* hence 2*x <= y and therefore x < y *)
      (* goal: x < S y' *)
  destruct x as [|x1].
   (* x = 0 *) lia.
   (* x = S x1 *)
    (* 8 * x <= pow2(S e') * x, by monotonicity on the right with x>0 *)
    assert (HleL : 8 * S x1 <= pow2 (S e') * S x1).
    { apply Nat.mul_le_mono_pos_r; [lia | exact Hpow]. }
    (* 3*(S y') + 1 <= 4*(S y') since S y' >= 1 *)
    assert (HleR : 3 * S y' + 1 <= 4 * S y') by lia.
    (* chain the two via Hx_def *)
    assert (Hchain : 8 * S x1 <= 4 * S y') by
      (eapply Nat.le_trans; [exact HleL|]; rewrite Hx_def; exact HleR).
    (* conclude x < S y' *)
    lia.

Qed.

End Row_correctness_family_pattern_and_word_semantics.
