From Coq Require Import Arith.Arith Arith.PeanoNat Lia Lists.List.
Import ListNotations.

(*********************************************************************)
(* Section 11 — Row-level invariance and many realizations           *)
(* This section formalizes that:                                     *)
(*  1) the next odd image y is uniquely determined by (x,e) via      *)
(*     y = (2^e * x - 1)/3, independent of the chosen row/lift;      *)
(*  2) different rows that match the same (alpha mod 6, delta) and   *)
(*     same lift exponent e realize the same certified step;         *)
(*  3) there are many realizations: once (x,e) is fixed, any table   *)
(*     row with matching (delta, alpha mod 6) can be used to realize *)
(*     the step, and all realizations produce the same y.            *)
(*********************************************************************)



(* We assume existing definitions from earlier sections: *)
(*   pow2 : nat -> nat                     (2^n)                         *)
(*   Record Row := { alpha; krow; delta; straight_subst; delta_ok }     *)
(*   row_step (r:Row) (p m:nat) : nat                                   *)
(*   row_soundness :                                                    *)
(*     forall r p m j pf x,                                             *)
(*       x = 18*m + 6*j + pf -> (pf=1 \/ pf=5) ->                       *)
(*       3*row_step r p m + 1 = pow2 (alpha r + 6*p) * x                *)
(*   odd_input_decomposition_no3 :                                      *)
(*     forall x, x mod 2 = 1 -> x mod 3 <> 0 ->                         *)
(*     exists m j pf, (pf=1\/pf=5) /\ x = 18*m + 6*j + pf /\ j < 3.     *)
(*   table_covers_family_alpha :                                        *)
(*     forall pf a, (pf=1\/pf=5) -> a<6 ->                              *)
(*     exists r, In r table /\ delta r = pf /\ alpha r = a.             *)

Section RowLevelInvariance.

Definition pow2 (n:nat) := Nat.pow 2 n.

Record Row := {
  alpha  : nat;
  krow   : nat;
  delta  : nat;
  delta_ok : delta = 1 \/ delta = 5;

  (* lift-aware: exponent alpha+6p *)
  straight_subst :
    forall (p j pf:nat), (pf = 1 \/ pf = 5) ->
      18 * krow + 3 * delta + 1 = pow2 (alpha + 6*p) * (6*j + pf)
}.


Context
  (table : list Row)
  (table_covers_family_alpha :
     forall (pf a:nat), (pf=1 \/ pf=5) -> a<6 ->
       exists r, In r table /\ delta r = pf /\ alpha r = a).

(* A single “row map” at lift p: m ↦ 6*(2^(alpha+6p)*m + K) + delta *)
Definition row_step (r:Row) (p m:nat) : nat :=
  6 * (pow2 (alpha r + 6*p) * m + krow r) + delta r.

Lemma row_soundness :
  forall (r:Row) p m j pfam x,
    x = 18*m + 6*j + pfam ->
    (pfam = 1 \/ pfam = 5) ->
    3 * row_step r p m + 1 = pow2 (alpha r + 6*p) * x.
Proof.
  intros r p m j pfam x Hx Hfam.
  unfold row_step.
  rewrite (Nat.mul_add_distr_l 6 (pow2 (alpha r + 6*p) * m) (krow r)).
  rewrite (Nat.mul_add_distr_l 3
             (6 * (pow2 (alpha r + 6*p) * m) + 6 * krow r)
             (delta r)).
  rewrite (Nat.mul_add_distr_l 3
             (6 * (pow2 (alpha r + 6*p) * m))
             (6 * krow r)).
  (* assoc/commute to line up with straight_subst, then use it *)
  rewrite !Nat.mul_assoc.
  replace (3*6) with 18 by lia.
  replace (3*6) with 18 by lia.
  rewrite (Nat.mul_comm 18 (pow2 (alpha r + 6*p))).
  replace (3*6) with 18 by lia. replace (3*6) with 18 by lia.
  (* expose the constant block *)
  replace (pow2 (alpha r + 6*p) * (18*m) + 18*krow r + 3*delta r + 1)
    with (pow2 (alpha r + 6*p) * (18*m) + (18*krow r + 3*delta r + 1)) by lia.
  (* use the lift-aware identity *)
  replace (pow2 (alpha r + 6 * p) * 18 * m + 18 * krow r + 3 * delta r + 1)
    with (pow2 (alpha r + 6 * p) * 18 * m + (18 * krow r + 3 * delta r + 1)) by lia.
  rewrite (straight_subst r p j pfam Hfam).
  rewrite Hx. ring_simplify. reflexivity.
Qed.

(* We’ll reuse the exact-division lemma from the previous section. *)
Lemma affine_step_nat_pair_nosub :
  forall (r:Row) p m j pf x,
    x = 18*m + 6*j + pf ->
    (pf = 1 \/ pf = 5) ->
    let e := alpha r + 6*p in
    let A := pow2 e in
    let C := 3 * (6 * krow r + delta r) in
    (* No '-' anywhere: *)
    A * x + C = 3 * row_step r p m + A * (6*j + pf).
Proof.
  intros r p m j pf x Hx _ e A C.
  subst A C x. unfold row_step.
  (* Expand both sides with left/right distributivity, then linear arithmetic *)
  rewrite !Nat.mul_add_distr_l.        (* A*(18*m + 6*j + pf)  and A*(6*j + pf) *)
  (* Make the RHS exponent literally the same “e” *)
  change (pow2 (alpha r + 6 * p)) with (pow2 e).

  (* Normalize products so both sides look the same to lia *)
  rewrite !Nat.mul_assoc.

  (* Put constants on the left of products *)
  replace (pow2 e * 18 * m) with (18 * pow2 e * m) by lia.
  replace (pow2 e * 6  * j) with (6  * pow2 e * j) by lia.

  (* Flatten the RHS 3*6 blocks *)
  replace (3 * (6 * (pow2 e * m))) with (18 * pow2 e * m) by lia.
  replace (3 * (6 * krow r))       with (18 * krow r)       by lia.
  lia.    
Qed.

 Lemma affine_step_scaled :
    forall (r:Row) p m j pf x,
      x = 18*m + 6*j + pf ->
      (pf = 1 \/ pf = 5) ->
      let e := alpha r + 6*p in
      3 * row_step r p m + 1 = pow2 e * x.
  Proof.
    intros r p m j pf x Hx Hpf e.
    (* This is your proven row_soundness specialized to e := alpha r + 6*p *)
    unfold e. eapply row_soundness; eauto.
  Qed.


(* Recall: pow2, Row, row_step, and row_soundness are already in your file. *)

(* 2) Exact division in Nat: row_step = (2^e * x - 1) / 3, and the remainder is 0 *)
Lemma affine_step_divNat :
  forall (r:Row) p m j pf x,
    x = 18*m + 6*j + pf ->
    (pf = 1 \/ pf = 5) ->
    let e := alpha r + 6*p in
    row_step r p m = (pow2 e * x - 1) / 3
/\ (pow2 e * x - 1) mod 3 = 0.
Proof.
  intros r p m j pf x Hx Hpf.
  pose proof (affine_step_scaled r p m j pf x Hx Hpf) as Hsc. (* already e := alpha+6p *)
  cbv zeta in Hsc.
  assert (Hmul' : 3 * row_step r p m = pow2 (alpha r + 6*p) * x - 1) by lia.
  split.
  - rewrite <- Hmul'. replace (3 * row_step r p m) with ((row_step r p m) * 3) by lia.
    now rewrite Nat.div_mul by lia.
  - rewrite <- Hmul'.   
    replace ((3 * row_step r p m)) with ((row_step r p m * 3)) by lia.                    (* (3 * row_step …) mod 3 *)
    now rewrite Nat.Div0.mod_mul by lia.         (* = 0 *)
Qed.


(*************************************************************)
(* Lemma 11.1 (Paper): Uniqueness of y given (x,e).          *)
(* If 3*y+1 = 2^e x, then necessarily y = (2^e x - 1)/3.     *)
(* This is the core row-level invariance in value: the next  *)
(* odd iterate depends only on (x,e), not on the row/lift.    *)
(*************************************************************)
Lemma next_odd_is_unique_from_x_e :
  forall x e y,
    3*y + 1 = pow2 e * x ->
    y = (pow2 e * x - 1) / 3
 /\ (pow2 e * x - 1) mod 3 = 0.
Proof.
  intros x e y Heq.
  assert (Hmul : pow2 e * x - 1 = 3*y) by lia.
  split.
  - rewrite Hmul. rewrite Nat.mul_comm. now rewrite Nat.div_mul by lia.
  - rewrite Hmul. 
    replace (3 * y) with (y * 3) by lia.
    now rewrite Nat.Div0.mod_mul by lia.
Qed.

(********************************************************************)
(* Lemma 11.2 (Paper): Row-step depends only on (x,e).              *)
(* Any realization (r,p,m,j,pf) consistent with x and e yields the  *)
(* same row_step value, namely (2^e x - 1)/3.                       *)
(********************************************************************)
Lemma row_step_depends_only_on_x_e :
  forall r p m j pf x,
    x = 18*m + 6*j + pf -> (pf=1 \/ pf=5) ->
    row_step r p m = (pow2 (alpha r + 6*p) * x - 1) / 3.
Proof.
  intros r p m j pf x Hx Hpf.
  destruct (affine_step_divNat r p m j pf x Hx Hpf) as [H _].
  exact H.
Qed.

(******************************************************************************************)
(* Lemma 11.3 (Paper): Cross-row invariance at fixed exponent.                            *)
(* Suppose two rows r1, r2 share the same exponent with lifts p1,p2:                      *)
(*   alpha r1 + 6*p1 = alpha r2 + 6*p2 = e,                                               *)
(* and both realize the SAME x via decompositions (m1,j1,pf) and (m2,j2,pf), then         *)
(*   row_step r1 p1 m1 = row_step r2 p2 m2.                                               *)
(* Intuition: both sides must equal (2^e * x - 1)/3 by Lemma 11.2.                        *)
(******************************************************************************************)
Lemma row_step_invariant_across_rows :
  forall r1 r2 p1 p2 m1 j1 m2 j2 pf x,
    x = 18*m1 + 6*j1 + pf -> x = 18*m2 + 6*j2 + pf -> (pf=1 \/ pf=5) ->
    alpha r1 + 6*p1 = alpha r2 + 6*p2 ->
    row_step r1 p1 m1 = row_step r2 p2 m2.
Proof.
  intros r1 r2 p1 p2 m1 j1 m2 j2 pf x Hx1 Hx2 Hpf He.
  rewrite (row_step_depends_only_on_x_e r1 p1 m1 j1 pf x Hx1 Hpf).
  rewrite (row_step_depends_only_on_x_e r2 p2 m2 j2 pf x Hx2 Hpf).
  now rewrite He.
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

(************************************************************************************************)
(* Lemma 11.4 (Paper): Many realizations exist for fixed (x,e).                                 *)
(* Given x odd with x mod 3 <> 0 and a certified exponent e, for ANY family pf∈{1,5} and        *)
(* residue a := e mod 6, the table provides a row r with delta r = pf and alpha r = a; using    *)
(* the canonical (m,j) decomposition of x, the pair (r,p:=e/6) realizes the step and yields     *)
(* the unique row_step value (2^e x - 1)/3.                                                     *)
(************************************************************************************************)
Lemma many_realizations_same_value :
  forall x e,
    x mod 2 = 1 -> x mod 3 <> 0 ->
    let a := e mod 6 in let p := e / 6 in
    exists pf r m j,
      pf = x mod 6 /\ (pf = 1 \/ pf = 5) /\
      In r table /\ delta r = pf /\ alpha r = a /\
      x = 18*m + 6*j + pf /\ j < 3 /\
      3 * row_step r p m + 1 = pow2 e * x /\
      row_step r p m = (pow2 e * x - 1) / 3.
Proof.
  intros x e Hodd Hne3 a p.
  (* canonical odd decomposition gives the right pf *)
  destruct (odd_input_decomposition_no3 x Hodd Hne3)
    as (m & j & pf & Hpf15 & Hx & Hjlt).
  (* pick the row matching (pf,a) *)
  assert (Ha : a < 6) by (subst a; apply Nat.mod_upper_bound; lia).
  destruct (table_covers_family_alpha pf a Hpf15 Ha)
    as (r & Hin & Hdelta & Halpha).
  exists pf, r, m, j; repeat split; try assumption.
  - (* pf = x mod 6 *)
    rewrite Hx. rewrite Nat.add_comm.
    (* Goal: pf = (pf + (18*m + 6*j)) mod 6 *)
    (* Turn (18*m + 6*j) into 6*(3*m + j) *)
    replace (18*m + 6*j) with (6 * (3*m + j)) by lia.
    (* Put it in the b*n order that mod_add expects: (a + b*n) mod n *)
    rewrite Nat.mul_comm.                     (* 6 * (3*m + j) -> (3*m + j) * 6 *)
    (* Now apply mod_add: (a + b*n) mod n = a mod n, needs n>0 *)
    rewrite Nat.Div0.mod_add by lia.               (* RHS becomes pf mod 6 *)
    (* Finally, pf ∈ {1,5} ⇒ pf < 6, so pf mod 6 = pf *)
    rewrite Nat.mod_small by lia.
    reflexivity.             (* done *)    
  - (* 3*row_step + 1 = 2^e x *)
    (* we are inside: many_realizations_same_value (Fix 2 variant) *)
    (* a := e mod 6, p := e / 6, Halpha : alpha r = a *)
    (* Step 1: decompose e with div_mod and align the order *)
    assert (HeDM : e = 6 * (e / 6) + e mod 6) by (apply Nat.div_mod; lia).    
    (* Turn it into exactly e = alpha r + 6*p *)
    assert (Heq_e : e = alpha r + 6*p).
    { subst a p. rewrite Halpha.
      (* (e/6)*6 + e mod 6  ->  6*(e/6) + e mod 6  ->  e mod 6 + 6*(e/6) *)
      rewrite HeDM.
      rewrite Nat.mul_comm.
      rewrite Nat.add_comm.
      rewrite Nat.add_comm.
      set (n := e / 6 * 6 + e mod 6).      
      (* goal: n = n mod 6 + 6 * (n / 6) *) 
      replace (n mod 6 + 6 * (n / 6)) with (6 * (n / 6) + n mod 6) by lia.
      now apply Nat.div_mod; lia.      
      }
    (* Now use it: *)
    rewrite Heq_e.
    eapply row_soundness; eauto.
  - (* exact division: row_step = (2^e x - 1)/3 *)
    (* Phase 1: work with a local e' and get the division form now *)
    set (e' := alpha r + 6*p).
    pose proof (affine_step_divNat r p m j pf x Hx Hpf15) as [Hdiv _].
    cbv zeta in Hdiv.  (* unfolds the let inside affine_step_divNat *)
    (* Target: row_step r p m = (pow2 e * x - 1) / 3 *)
    (* 1) Get the division form with the row’s own exponent e' := alpha r + 6*p *)    
    pose proof (proj1 (affine_step_divNat r p m j pf x Hx Hpf15)) as Hdiv'.
    cbv zeta in Hdiv'.
    (* Hdiv : row_step r p m = (pow2 e' * x - 1) / 3 *)

    (* 2) Prove e = e' once, from div/mod and alpha=a *)
    assert (HeDM : e = 6 * (e / 6) + e mod 6) by (apply Nat.div_mod; lia).
    assert (Heq_e : e = e').
    { subst e' a p. rewrite Halpha.
      replace (e mod 6 + 6 * (e / 6)) with (6 * (e / 6) + e mod 6) by lia.
      now apply Nat.div_mod; lia.      
    }
    (* Phase 2: use Heq_e to align e with e', then close your original goal *)
    rewrite Heq_e.            (* turns pow2 e into pow2 (alpha r + 6*p) = pow2 e' *)
    exact Hdiv.
Qed.

(********************************************************************)
(* Lemma 11.5 (Paper): Uniqueness across all realizations.          *)
(* Any two realizations of (x,e) – possibly with different rows,    *)
(* lifts p, and decompositions – produce the same y.                 *)
(********************************************************************)
Lemma uniqueness_across_all_realizations :
  forall r1 r2 p1 p2 m1 j1 pf1 m2 j2 pf2 x,
    x = 18*m1 + 6*j1 + pf1 -> (pf1=1 \/ pf1=5) ->
    x = 18*m2 + 6*j2 + pf2 -> (pf2=1 \/ pf2=5) ->
    alpha r1 + 6*p1 = alpha r2 + 6*p2 ->
    row_step r1 p1 m1 = row_step r2 p2 m2.
Proof.
  intros r1 r2 p1 p2 m1 j1 pf1 m2 j2 pf2 x Hx1 Hpf1 Hx2 Hpf2 He.
  (* Both sides equal (2^e x - 1)/3 with the same e *)
  rewrite (row_step_depends_only_on_x_e r1 p1 m1 j1 pf1 x Hx1 Hpf1).
  rewrite (row_step_depends_only_on_x_e r2 p2 m2 j2 pf2 x Hx2 Hpf2).
  now rewrite He.
Qed.

End RowLevelInvariance.
