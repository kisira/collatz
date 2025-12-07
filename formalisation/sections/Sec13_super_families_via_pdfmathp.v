From Coq Require Import Arith.Arith Arith.PeanoNat Lia.
From Coq Require Import Lists.List.
Import ListNotations.

Module Sec13_Super_families_via_pdfmathp.

(** * Section 13 — Super-families via parameter (pf, a) *)

(* Project-wide defs (assumed already available in prior sections) *)
Parameter Row : Type.
Parameter table : list Row.

Parameter alpha : Row -> nat.
Parameter delta : Row -> nat.
Parameter krow  : Row -> nat.

Definition pow2 (e:nat) := Nat.pow 2 e.
Definition forward_image (x e:nat) := (pow2 e * x - 1) / 3.

(* Row machinery proved earlier *)
Parameter row_step : Row -> nat (* p *) -> nat (* m *) -> nat.
Axiom row_soundness :
  forall (r:Row) p m j pf x,
    x = 18*m + 6*j + pf -> (pf = 1 \/ pf = 5) ->
    3 * row_step r p m + 1 = pow2 (alpha r + 6*p) * x.

Axiom affine_step_divNat :
  forall (r:Row) p m j pf x,
    x = 18*m + 6*j + pf -> (pf = 1 \/ pf = 5) ->
    row_step r p m = (pow2 (alpha r + 6*p) * x - 1) / 3
 /\ (pow2 (alpha r + 6*p) * x - 1) mod 3 = 0.

Axiom table_covers_family_alpha :
  forall pf a, pf = 1 \/ pf = 5 -> a < 6 ->
  exists r : Row, In r table /\ delta r = pf /\ alpha r = a.

Axiom rows_and_lifts_are_complete_odd :
  forall y x e,
    3*y + 1 = pow2 e * x -> x mod 2 = 1 -> x mod 3 <> 0 ->
    exists p r m j pf,
      In r table /\ delta r = pf /\ (pf = 1 \/ pf = 5)
      /\ e = alpha r + 6*p
      /\ x = 18*m + 6*j + pf /\ j < 3
      /\ 3 * row_step r p m + 1 = pow2 e * x.

(* ----------------------- Super-family predicate ----------------------- *)

Definition super_family (pf a:nat) (r:Row) :=
  delta r = pf /\ alpha r = a.

(* Sanity: every (pf,a) with pf∈{1,5}, a<6 has a representative in table. *)
Lemma super_family_covers_pair :
  forall pf a, (pf = 1 \/ pf = 5) -> a < 6 ->
  exists r, In r table /\ super_family pf a r.
Proof.
  intros pf a Hpf Ha.
  destruct (table_covers_family_alpha pf a Hpf Ha) as (r & Hin & Hδ & Hα).
  exists r; split; [exact Hin|split; [exact Hδ|exact Hα]].
Qed.

(* Given x,e and their split a:=e mod 6, p:=e/6, any row in the same (pf,a)
   realizes the SAME forward image. *)
Lemma many_rows_realize_the_same_forward_image:
  forall x e, x mod 2 = 1 -> x mod 3 <> 0 ->
  let a := e mod 6 in let p := e / 6 in
  forall m j pf, (pf = 1 \/ pf = 5) ->
  x = 18*m + 6*j + pf -> j < 3 ->
  forall r, In r table -> delta r = pf -> alpha r = a ->
  row_step r p m = forward_image x e.
Proof.
  intros x e Hodd Hne3 a p m j pf Hpf Hx Hj r Hin Hδ Hα.
  (* Align e with alpha r + 6p *)
  assert (HeDM : e = 6*(e/6) + e mod 6) by (apply Nat.div_mod; lia).
  assert (He : e = alpha r + 6*p).
  { symmetry in Hα. subst a p. rewrite <- Hα. rewrite Nat.add_comm. exact HeDM. }
  (* Exact division form for this row *)
  destruct (affine_step_divNat r p m j pf x Hx Hpf) as [Hdiv _].
  unfold forward_image. now rewrite He.
Qed.

Lemma many_rows_realize_same_FI_call
  (x e m j pf : nat) (r : Row)
  (Hodd : x mod 2 = 1) (Hne3 : x mod 3 <> 0)
  (Hpf  : pf = 1 \/ pf = 5)
  (Hx   : x = 18*m + 6*j + pf) (Hj : j < 3)
  (Hin  : In r table) (Hδ : delta r = pf) (Hα : alpha r = e mod 6)
: row_step r (e / 6) m = forward_image x e.
Proof.
  (* reuse your core lemma once, with the right instantiations *)
  set (a := e mod 6). set (p := e / 6).
  (* your original lemma, in the correct order: m j pf — Hpf Hx Hj — r Hin Hδ Hα *)
  eapply many_rows_realize_the_same_forward_image
  with (x:=x) (e:=e) (m:=m) (j:=j) (pf:=pf) (r:=r);
  eauto.  
Qed.


(* Two different rows with the same (pf,a) give identical row_step values,
   hence a canonical “super-family forward image”. *)
Lemma super_family_forward_image_unique :
  forall x e, x mod 2 = 1 -> x mod 3 <> 0 ->
  let a := e mod 6 in let p := e / 6 in
  forall m j pf, (pf = 1 \/ pf = 5) ->
  x = 18*m + 6*j + pf -> j < 3 ->
  forall r1 r2,
    In r1 table -> super_family pf a r1 ->
    In r2 table -> super_family pf a r2 ->
    row_step r1 p m = row_step r2 p m
 /\ row_step r1 p m = forward_image x e.
Proof.
  intros x e Hodd Hne3 a p m j pf Hpf Hx Hj r1 r2
         Hin1 [Hδ1 Hα1] Hin2 [Hδ2 Hα2].
  pose proof (many_rows_realize_the_same_forward_image
              x e
              Hodd Hne3
              m j pf
              Hpf Hx Hj
              r1 Hin1 Hδ1 Hα1) as H1.

pose proof (many_rows_realize_the_same_forward_image
              x e
              Hodd Hne3
              m j pf
              Hpf Hx Hj
              r2 Hin2 Hδ2 Hα2) as H2.  
  split.
  - (* same value for any row in the same super-family *)
    change (row_step r1 p m) with (row_step r1 (e/6) m).
    change (row_step r2 p m) with (row_step r2 (e/6) m).
    now rewrite H1, H2.
  - (* and that common value is the forward image *)
    change (row_step r1 p m) with (row_step r1 (e/6) m).
    exact H1.  
Qed.

Lemma odd_lt6_cases :
    forall n, n < 6 -> n mod 2 = 1 -> n = 1 \/ n = 3 \/ n = 5.
  Proof.
    intros n Hlt Hodd.  
  (* enumerate n=0..5; kill evens using Hodd *)
    destruct n as [|n1]; [simpl in Hodd; lia|].
    destruct n1 as [|n2]; [left; reflexivity|].
    destruct n2 as [|n3]; [simpl in Hodd; lia|].
    destruct n3 as [|n4]; [right; left; reflexivity|].
    destruct n4 as [|n5]; [simpl in Hodd; lia|].
    destruct n5 as [|n].                                  (* n = 5 or 6+ *)
    - (* n = 5 *) right; right.
      reflexivity.
    - (* n >= 6 contradicts n<6 *)
      exfalso; lia.
  Qed.


Lemma odd_input_decomposition_no3 :
    forall x, x mod 2 = 1 -> x mod 3 <> 0 ->
    exists (m j pf:nat),
        (pf = 1 \/ pf = 5)
    /\ x = 18*m + 6*j + pf
    /\ j < 3.
  Proof.
    intros x Hodd Hmod3.
    (* Define q := x/6 and pf := x mod 6, and get the Euclidean split *)
    remember (x / 6)  as q  eqn:Hq.
    remember (x mod 6) as pf eqn:Hpf.
    assert (Hx : x = 6*q + pf) by (subst; apply Nat.div_mod; lia).
    assert (Hpf_lt : pf < 6)    by (rewrite Hpf; apply Nat.mod_upper_bound; lia).
    (* pf is odd because x is odd and x = 6*q + pf *)
    assert (Hpf_odd : pf mod 2 = 1).
    { rewrite Hx in Hodd.
      rewrite Nat.Div0.add_mod  in Hodd by lia.
      rewrite Nat.Div0.mul_mod  in Hodd by lia.
      replace (6 mod 2) with 0 in Hodd by (now compute).
      rewrite Nat.add_0_l in Hodd.
      now rewrite Nat.Div0.mod_mod in Hodd by lia. }
    (* pf ∈ {1,3,5} from pf<6 and oddness *)
    pose proof (odd_lt6_cases pf Hpf_lt Hpf_odd) as Hpf_135.
    (* Exclude pf = 3 using x mod 3 <> 0 *)
    assert (Hpf_ne3 : pf <> 3).
    { intro Hpf3. subst pf.
      rewrite Hx in Hmod3.
      rewrite Nat.Div0.add_mod  in Hmod3 by lia.
      rewrite Nat.Div0.mul_mod  in Hmod3 by lia.
      replace (6 mod 3) with 0 in Hmod3 by (now compute).      
      rewrite Nat.add_0_l in Hmod3.       (* ((x mod 6) mod 3) mod 3 <> 0 *)
      rewrite Nat.Div0.mod_mod in Hmod3 by lia. (*  (x mod 6) mod 3 <> 0 *)
      rewrite Hpf3 in Hmod3.              (*  3 mod 3 <> 0 *)
      rewrite Nat.Div0.mod_same in Hmod3 by lia.                     (*  0 <> 0 *)
      contradiction.      
    }
    (* So pf ∈ {1,5} *)
    assert (Hpf_15 : pf = 1 \/ pf = 5).
    { destruct Hpf_135 as [-> | [H3 | ->]];
        [left; reflexivity | exfalso; exact (Hpf_ne3 H3) | right; reflexivity]. }
    (* Split q as 3*m + j with j<3 *)
    remember (q / 3) as m eqn:Hm.
    remember (q mod 3) as j eqn:Hj.
    assert (Hq_split : q = 3*m + j) by (subst; apply Nat.div_mod; lia).
    assert (Hj_lt : j < 3)          by (subst; apply Nat.mod_upper_bound; lia).
    (* Assemble the witnesses *)
    destruct Hpf_15 as [Hpf_is1 | Hpf_is5].
    - (* pf = 1 *)
      exists m, j, 1. repeat split; try now left.
      + rewrite Hx, Hq_split. lia.
      + exact Hj_lt.
    - (* pf = 5 *)
      exists m, j, 5. repeat split; try now right.
      + rewrite Hx, Hq_split. lia.
      + exact Hj_lt.
  Qed.


Theorem super_family_completeness :
  forall y x e,
    3*y + 1 = pow2 e * x ->        (* not used in the construction, but consistent *)
    x mod 2 = 1 -> x mod 3 <> 0 ->
  exists pf a p r m j,
    a = e mod 6 /\ p = e / 6 /\
    (pf = 1 \/ pf = 5) /\
    In r table /\ super_family pf a r /\
    x = 18*m + 6*j + pf /\ j < 3 /\
    row_step r p m = forward_image x e.
Proof.
  intros y x e Heq Hodd Hne3.
  (* Coordinates from e *)
  set (a := e mod 6).
  set (p := e / 6).

  (* Decompose x as 18m + 6j + pf with pf ∈ {1,5}, j<3 *)
  destruct (odd_input_decomposition_no3 x Hodd Hne3)
    as (m & j & pf & Hpf & Hx & Hj).

  (* Pick a row r in the super-family (pf,a) *)
  assert (Ha : a < 6) by (subst a; apply Nat.mod_upper_bound; lia).
  destruct (table_covers_family_alpha pf a Hpf Ha)
    as (r & Hin & Hδ & Hα).

  (* The row-step equals the canonical forward image *)
  pose proof (many_rows_realize_the_same_forward_image
                x e Hodd Hne3 m j pf Hpf Hx Hj r Hin Hδ ltac:(subst a; exact Hα))
    as Hfi.

  (* Assemble witnesses and properties *)
  exists pf, a, p, r, m, j.  
  repeat split; try reflexivity; try assumption.
Qed.
  
(* Stability under e that share the same (a,p) coordinates:
   if e = a + 6p and e' = a + 6p, forward images coincide (same x,m). *)
Lemma same_coordinates_same_forward_image :
  forall x a p e e' m j pf r,
    e  = a + 6*p -> e' = a + 6*p ->
    In r table -> super_family pf a r ->
    x = 18*m + 6*j + pf -> (pf = 1 \/ pf = 5) -> j < 3 ->
    forward_image x e = forward_image x e'.
Proof.
  intros x a p e e' m j pf r He He' Hin [Hδ Hα] Hx Hpf Hj.
  unfold forward_image. now rewrite He, He'.
Qed.

End Sec13_Super_families_via_pdfmathp.
