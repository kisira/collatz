From Coq Require Import Arith.Arith Arith.PeanoNat Lia.
From Coq Require Import Lists.List.
Import ListNotations.

(*********************************************************************)
(* Section 12 — Row design and the forward identity                  *)
(* Goal: isolate the forward map y = (2^e * x - 1)/3 as a canonical  *)
(* “design target”, and relate it to any row/lift that matches       *)
(* (pf, alpha mod 6).                                                 *)
(*********************************************************************)


(* Assumed from earlier sections / the paper: *)
(*   pow2 : nat -> nat                               (2^n)                  *)
(*   Record Row := { alpha : nat; krow : nat; delta : nat;                  *)
(*                   straight_subst : forall j p,                           *)
(*                     (p=1 \/ p=5) ->                                      *)
(*                     18*krow + 3*delta + 1 = pow2 alpha * (6*j + p);      *)
(*                   delta_ok : delta = 1 \/ delta = 5 }.                   *)
(*   row_step (r:Row) (p m:nat) : nat         (* = 6*(pow2 e * m + krow)+δ *)*)
(*   row_soundness : forall r p m j pf x,                                    *)
(*      x = 18*m + 6*j + pf -> (pf=1 \/ pf=5) ->                             *)
(*      3*row_step r p m + 1 = pow2 (alpha r + 6*p) * x.                     *)
(*   odd_input_decomposition_no3 : forall x,                                  *)
(*      x mod 2 = 1 -> x mod 3 <> 0 ->                                       *)
(*      exists m j pf, (pf=1\/pf=5) /\ x = 18*m + 6*j + pf /\ j < 3.         *)
(*   table : list Row, plus coverage:                                        *)
(*   table_covers_family_alpha : forall pf a, (pf=1\/pf=5) -> a<6 ->         *)
(*       exists r, In r table /\ delta r = pf /\ alpha r = a.                *)

Section RowDesignForwardIdentity.

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

(* ---------- 12.1 The forward image as a canonical design target ---------- *)
Definition forward_image (x e : nat) : nat :=
  (pow2 e * x - 1) / 3.

Lemma pow2_0_ge_1 : 1 <= pow2 0.
Proof.
  unfold pow2. rewrite Nat.pow_0_r. lia.   (* Nat.pow 2 0 = 1 *)
Qed.

Lemma pow2_pos : forall e, 1 <= pow2 e.
Proof.
  unfold pow2.
  induction e as [| e' IH]; simpl.
  - (* e = 0 *) pose proof pow2_0_ge_1. lia.      (* 2^0 = 1 *)
  - (* e = S e' *) rewrite Nat.add_0_r.
    eapply Nat.le_trans; [ exact IH | lia ].     (* 2^(S e') = 2 * 2^e' *)    
Qed.

Lemma forward_image_spec :
   forall x e,
    1 <= x ->                      (* positivity precondition *)
    (pow2 e * x - 1) mod 3 = 0 ->
    3 * forward_image x e + 1 = pow2 e * x.
Proof.
  intros x e Hxpos Hmod. unfold forward_image.
  (* from mod=0, write as 3*k *)
  apply Nat.Div0.mod_divides in Hmod.   
  destruct Hmod as [k Hk]. rewrite Hk.  
  rewrite Nat.mul_comm. 
  replace (3 * k ) with (k*3) by lia.                     (* (3*k)/3 → k via div_mul *)   
  rewrite (Nat.div_mul) by lia.
  rewrite Nat.mul_comm. 
  replace (pow2 e * x) with ((pow2 e * x - 1) + 1) .
  rewrite Hk.                 (* RHS becomes 3*k + 1 *)
  rewrite Nat.mul_comm.       (* LHS k*3 → 3*k *)
  reflexivity.  
  assert (Htmp : pow2 e * x - 1 = 3 * k) by exact Hk.  
  assert (Hpow : 1 <= pow2 e).
    { induction e; simpl.
      - pose proof pow2_0_ge_1. exact pow2_0_ge_1. 
      - pose proof pow2_pos. apply pow2_pos. }  
  assert (Heq : pow2 e * x = 3 * k + 1).
  { (* add 1 to both sides using a concrete equality, no side-conditions *)
    replace (pow2 e * x) with ((pow2 e * x - 1) + 1) by lia.
    replace (pow2 e * x) with ((pow2 e * x - 1) + 1) by lia.
    - apply (f_equal (fun t => t + 1)) in Hk. 
      rewrite Hk.              (* LHS becomes: 3*k + 1 - 1 + 1 *)
      lia.                     (* 3*k + 1 - 1 + 1 = 3*k + 1 *)            
  }
  assert (Hpos : 1 <= pow2 e * x) by (rewrite Heq; lia).
  rewrite Heq.
  lia.  
Qed.

(* A tidier version we often use: *)
Lemma forward_identity_from_equation :
  forall x e y, 3*y + 1 = pow2 e * x ->
  y = forward_image x e /\ (pow2 e * x - 1) mod 3 = 0.
Proof.
  intros x e y Heq. unfold forward_image.
  assert (Hmul : pow2 e * x - 1 = 3*y) by lia.
  split.
  - rewrite Hmul. rewrite Nat.mul_comm. now rewrite Nat.div_mul by lia.
  - rewrite Hmul. 
    replace (3 * y) with (y * 3) by lia.
    now rewrite Nat.Div0.mod_mul by lia.
Qed.

(* ---------- 12.2 Forward identity realized by any matching row/lift ----- *)

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


(* The exact division form for rows (Nat-only), restated for convenience. *)
Lemma row_exact_division :
  forall (r:Row) p m j pf x,
    x = 18*m + 6*j + pf -> (pf=1 \/ pf=5) ->
    row_step r p m = (pow2 (alpha r + 6*p) * x - 1) / 3
 /\ (pow2 (alpha r + 6*p) * x - 1) mod 3 = 0.
Proof.
  intros r p m j pf x Hx Hpf.
  (* From row_soundness: 3*row_step+1 = 2^e x with e := alpha r + 6p *)
  pose proof (row_soundness r p m j pf x Hx Hpf) as Hsc.
  set (e := alpha r + 6*p) in *.
  cbv zeta in Hsc.
  assert (Hmul' : 3 * row_step r p m = pow2 e * x - 1) by lia.
  split.
  - replace ((pow2 e * x - 1) / 3)
      with ((3 * row_step r p m) / 3) by (rewrite Hmul'; reflexivity).
    rewrite Nat.mul_comm.                 (* (3 * n)/3 -> (n * 3)/3 *)
    rewrite Nat.div_mul by lia.           (* 3 <> 0 *)
    reflexivity.
  - rewrite <- Hmul'.                  (* (pow2 e * x - 1) mod 3  →  (3 * row_step …) mod 3 *)
    replace (3 * row_step r p m) with (row_step r p m * 3) by lia.
    now rewrite Nat.Div0.mod_mul by lia.    (* since 3 <> 0 *)
Qed.

Lemma two_pow_pos : forall n, 1 <= 2 ^ n.
Proof.
  intro n.
  induction n as [| n IH].
  - (* n = 0 *) rewrite Nat.pow_0_r; lia.      (* 2^0 = 1 *)
  - (* n = S n *) rewrite Nat.pow_succ_r'.      (* 2^(S n) = 2 * 2^n *)
    (* 0 < 2 and 1 <= 2^n (IH) ⇒ 1 <= 2 * 2^n *)
    simpl. lia. 
Qed.

(* The “forward identity via rows”: any row/lift that matches (pf, alpha mod 6)
   and exponent e realizes the canonical forward_image. *)
Lemma forward_identity_via_rows :
  forall r p m j pf x e,
    x = 18*m + 6*j + pf -> (pf=1 \/ pf=5) ->
    e = alpha r + 6*p ->
    row_step r p m = forward_image x e
 /\ 3 * row_step r p m + 1 = pow2 e * x.
Proof.
  intros r p m j pf x e Hx Hpf He.
  subst e. unfold forward_image.
  destruct (row_exact_division r p m j pf x Hx Hpf) as [Hdiv Hmod].
  split.
  - exact Hdiv.
  - (* scaled identity follows immediately *)    
    set (A := pow2 (alpha r + 6 * p) * x).
    symmetry.
    rewrite Hdiv.
    change ((pow2 (alpha r + 6 * p) * x - 1) / 3) with ((A - 1) / 3).
    pose proof (Nat.div_mod (A - 1) 3 (Nat.neq_succ_0 2)) as Hdm.
    change (pow2 (alpha r + 6 * p) * x - 1) with (A - 1) in Hmod.
    rewrite Hmod in Hdm.  
    set (Hexact := Hdm).                (* A - 1 = 3 * ((A - 1) / 3) + 0 *)
    (* 1) Simplify Hdm to the exact-division form *)
    pose proof Hdm as Hexact'.
    rewrite Nat.add_0_r in Hexact'.  (* Hexact : A - 1 = 3 * ((A - 1) / 3) *)

    (* 2) Rewrite the RHS of the goal using Hexact *)
    rewrite <- Hexact'.               (* goal becomes: A = (A - 1) + 1 *)

    (* 3) Justify (A - 1) + 1 = A with Nat.sub_add; we need 1 <= A *)
    assert (Hxpos : 1 <= x).
    { rewrite Hx. destruct Hpf as [Hpf1|Hpf1]; subst pf; lia. }
    assert (Hpow : 1 <= pow2 (alpha r + 6 * p)).
    { (* pow2_pos if you have it; otherwise inline: *)
      unfold pow2. (* if pow2 := Nat.pow 2 *)
      apply two_pow_pos. }
    lia.
Qed.

(* ---------- 12.3 Design-by-coverage: many realizations, one forward image *)

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

(* Given x odd with x mod 3 ≠ 0 and a target exponent e,
   for ANY table row whose (delta, alpha) matches (pf := x mod 6, a := e mod 6),
   the realized row_step equals forward_image x e. *)

Lemma many_rows_realize_the_same_forward_image :
  forall x e,
    x mod 2 = 1 -> x mod 3 <> 0 ->
    let a := e mod 6 in
    let p := e / 6 in
  forall m j pf,
    (pf = 1 \/ pf = 5) ->
    x = 18*m + 6*j + pf -> j < 3 ->
  forall r,
    In r table -> delta r = pf -> alpha r = a ->
    row_step r p m = forward_image x e.
Proof.
  intros x e Hodd Hne3 a p m j pf Hpf Hx Hj r Hin Hdelta Halpha.
  (* Align e with alpha r + 6*p *)
  assert (He : e = alpha r + 6*p).
  { subst a p.                  (* a = e mod 6, p = e / 6 *)
    (* e = (e/6)*6 + e mod 6 *)
    pose proof (Nat.div_mod e 6 (Nat.neq_succ_0 5)) as HeDM.
    (* Replace e mod 6 by alpha r using Halpha *)
    pose proof HeDM as He.
    rewrite <- Halpha in He.         (* e = 6*(e/6) + alpha r *)
    rewrite Nat.add_comm in He.      (* e = alpha r + 6*(e/6) *)
    exact He.
  }
  destruct (affine_step_divNat r p m j pf x Hx Hpf) as [Hdiv _].
  unfold forward_image.                 (* = (pow2 e * x - 1) / 3 *)
  rewrite He.                           (* make it pow2 (alpha r + 6*p) *)
  exact Hdiv.
Qed.

End RowDesignForwardIdentity.
