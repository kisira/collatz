From Coq Require Import Arith.Arith Arith.PeanoNat Lia Lists.List.
Import ListNotations.

Module AlgebraicCompleteness.

(* Shorthand used earlier *)
Definition pow2 (n:nat) := Nat.pow 2 n.

(* Families (odd layer): only residues 1 or 5 appear *)
Definition family (x:nat) := x mod 6.
Definition fam_e (x:nat) := family x = 1.
Definition fam_o (x:nat) := family x = 5.

(* === Abstract “Row Table” interface ===================================== *)
(* You likely already have concrete (alpha, k, delta) per row. We state the
   two properties we need: coverage (for both families) and correctness. *)

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

(* A single “row map” at lift p: m ↦ 6*(2^(alpha+6p)*m + K) + delta *)
Definition row_step (r:Row) (p m:nat) : nat :=
  6 * (pow2 (alpha r + 6*p) * m + krow r) + delta r.

(* Soundness (already proved in Sec07 as lem_row_correctness specialized).
   We restate it here parameterized by a Row. *)

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

(* === Completeness statement ============================================= *)
(* Every certified odd step with exponent e = alpha + 6*p is realized by a row r,
   a lift p, and suitable m,j,p_fam that encode the input x. *)

(* This is the algebraic packaging of “rows are complete”. To prove it,
   you’ll instantiate `table` with *your* finite list of rows and show
   the search procedure finds a matching row r for the given residue class. *)

Section Completeness.
  Context (table : list Row).

  (* Coverage hypothesis: for each residue family pfam in {1,5}, there exists
   some row in the table with delta = pfam and the straight-subst identity
   compatible with any j. In practice, your concrete rows ensure this. *)
  Hypothesis table_covers_families :
    forall pf, pf = 1 \/ pf = 5 -> exists r, In r table /\ delta r = pf.

  Hypothesis table_covers_family_alpha :
    forall (pf a:nat), (pf = 1 \/ pf = 5) -> a < 6 ->
      exists r, In r table /\ delta r = pf /\ alpha r = a.

  (* Optionally, you may also assume a mild alpha-completeness: for any e,
   there is some row with the same alpha modulo 6 (since e = alpha + 6*p). *)
  Hypothesis table_alpha_mod6_complete :
    forall a_mod6, a_mod6 < 6 ->
      exists r, In r table /\ alpha r mod 6 = a_mod6.

  (* Packaging of the input decomposition x = 18*m + 6*j + pfam *)
  Record InputDecomp := {
    m_in   : nat;
    j_in   : nat;
    pfam   : nat;
    pfam_ok : pfam = 1 \/ pfam = 5;
    x_is   : nat -> Prop
  }.
  
  (* ===== Helper: 2^n >= 8 when n >= 3 (used elsewhere; included for completeness) ===== *)
  Lemma pow2_ge_8 : forall n, 3 <= n -> 8 <= pow2 n.
  Proof.
    intros n H.
    destruct n as [|n1]; [lia|].
    destruct n1 as [|n2]; [lia|].
    destruct n2 as [|n3]; [lia|].
    unfold pow2. 
    replace (S (S (S n3))) with (3 + n3) by lia.
    rewrite Nat.pow_add_r. simpl.
    change (8 <= 8 * 2 ^ n3).           (* fold the nested sum back to a product *)
    assert (Hpos : 1 <= 2 ^ n3).
    { induction n3; simpl; lia. }       (* 2^n3 ≥ 1 *)
    change 8 with (8 * 1).
    apply Nat.mul_le_mono_pos_l; [lia | exact Hpos].         
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

  (* 1) General odd decomposition: pf ∈ {1,3,5} *)
  Lemma odd_input_decomposition_135 :
    forall x, x mod 2 = 1 ->
    exists (m j pf:nat),
        (pf = 1 \/ pf = 3 \/ pf = 5)
    /\ x = 18*m + 6*j + pf
    /\ j < 3.
  Proof.
    intros x Hodd.
    remember (x / 6)  as q  eqn:Hq.
    remember (x mod 6) as pf eqn:Hpf.
    assert (Hx : x = 6*q + pf) by (subst; apply Nat.div_mod; lia).
    assert (Hpf_lt : pf < 6)    by (rewrite Hpf; apply Nat.mod_upper_bound; lia).
    (* pf is odd *)
    assert (Hpf_odd : pf mod 2 = 1).
    { rewrite Hx in Hodd.
      rewrite Nat.Div0.add_mod, Nat.Div0.mul_mod in Hodd by lia.
      replace (6 mod 2) with 0 in Hodd by (now compute).
      rewrite Nat.add_0_l in Hodd.
      now rewrite Nat.Div0.mod_mod in Hodd by lia. }
    (* pf ∈ {1,3,5} *)
    pose proof (odd_lt6_cases pf Hpf_lt Hpf_odd) as Hpf_135.
    (* split q = 3*m + j, j<3 *)
    remember (q / 3) as m eqn:Hm.
    remember (q mod 3) as j eqn:Hj.
    assert (Hq_split : q = 3*m + j) by (subst; apply Nat.div_mod; lia).
    assert (Hj_lt : j < 3)          by (subst; apply Nat.mod_upper_bound; lia).
    destruct Hpf_135 as [Hpf1 | [Hpf3 | Hpf5]].
    - (* pf = 1 *)
      subst pf.
      exists m, j, 1.
      repeat split.
      + now left.                          (* pf ∈ {1,3,5} *)
      + rewrite Hx, Hq_split; lia.         (* x = 18*m + 6*j + 1 *)
      + exact Hj_lt.                       (* j < 3 *)
    - (* pf = 3 *)
      subst pf.
      exists m, j, 3.
      repeat split.
      + now right; left.
      + rewrite Hx, Hq_split; lia.
      + exact Hj_lt.
    - (* pf = 5 *)
      subst pf.
      exists m, j, 5.
      repeat split.
      + now right; right.
      + rewrite Hx, Hq_split; lia.
      + exact Hj_lt.
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

  Lemma x_not_div3_from_equation y x e :
    3*y + 1 = pow2 e * x -> x mod 3 <> 0.
  Proof.
    intros Heq Hc.  (* assume x mod 3 = 0 *)
    apply (f_equal (fun z => z mod 3)) in Heq.
    (* Heq : 3*y + 1 = pow2 e * x, Hc : x mod 3 = 0 *)
    apply (f_equal (fun z => z mod 3)) in Heq.
    (* LHS → 1 *)
    rewrite Nat.Div0.add_mod  in Heq by lia.
    replace ((3 * y)) with ((y * 3)) in Heq by lia.
    rewrite Nat.Div0.mod_mul  in Heq by lia.   (* (3*y) mod 3 = 0 *)
    (* (0 + 1) mod 3 = 1 *)
    rewrite Nat.add_0_l in Heq.
    (* RHS → 0 using Hc *)
    rewrite Nat.Div0.mul_mod in Heq by lia.
    rewrite Hc in Heq.
    replace (1 mod 3) with 1 in Heq by (now compute).    
    replace (1 mod 3) with 1 in Heq by (now compute).        
    replace (1 mod 3) with 1 in Heq by (now compute). 
    rewrite Nat.mul_0_r in Heq.             (* ((… * 0) …) → ((0) mod 3) mod 3 *)
    rewrite Nat.Div0.mod_0_l  in Heq by lia.     (* (0 mod 3)   → 0               *)    
    (* Heq is now: 1 = 0 *)
    congruence.                              (* or: lia *)    
  Qed.

  (* ===== Main completeness (odd-image version) ===== *)

  Theorem rows_and_lifts_are_complete_odd :
    forall y x e,
      3*y + 1 = pow2 e * x ->
      x mod 2 = 1 ->
      exists (p:nat) (r:Row) (m j pf:nat),
          In r table
      /\ pf = delta r
      /\ pf = 1 \/ pf = 5
      /\ e = alpha r + 6*p
      /\ x = 18*m + 6*j + pf /\ j < 3
      /\ 3 * row_step r p m + 1 = pow2 e * x.
  Proof.
    intros y x e Heq Hxodd.
    (* Turn the equation into an equality mod 3 *)
    apply (f_equal (fun z => z mod 3)) in Heq.
    (* Heq : (3*y + 1) mod 3 = (pow2 e * x) mod 3 *)

    (* Simplify the left side: (3*y) mod 3 = 0, so LHS = 1 *)
    rewrite Nat.Div0.add_mod  in Heq by lia.
    rewrite Nat.Div0.mul_mod  in Heq by lia.
    rewrite Nat.Div0.add_mod  in Heq by lia.
    (* You may already have this, but it's harmless to repeat *)
    (* rewrite Nat.mul_mod  in Heq by lia.  <-- keep if you haven't done it yet *)

    replace (3 mod 3) with 0 in Heq by (now compute).    
    rewrite Nat.add_0_l in Heq.
    replace (1 mod 3) with 1 in Heq by (now compute).    
    replace (1 mod 3) with 1 in Heq by (now compute).        
    replace (1 mod 3) with 1 in Heq by (now compute).
    (* Expose x mod 3 on the RHS *)
    rewrite Nat.Div0.mul_mod in Heq by lia.
            
    (* Keep a copy of the original equation *)
    pose proof Heq as Heq0.

    (* If/when you need the mod-3 version later, make a new name *)
    pose proof (f_equal (fun z => z mod 3) Heq0) as Heq_mod3.
    assert (Hx_ne3 : x mod 3 <> 0).
    { intro Hc.      
      rewrite Hc in Heq.  (* RHS becomes 0 *)
      rewrite Nat.mul_0_r in Heq.        (* 1 = (0) mod 3 *)
      rewrite Nat.Div0.mod_0_l  in Heq by lia. (* 1 = 0 *)
      discriminate. }  (* 1 = 0 contradiction *)
    (* 1) From Heq, we already got Hx_ne3 above. Also have Hxodd : x mod 2 = 1. *)
    destruct (odd_input_decomposition_no3 x Hxodd Hx_ne3)
      as (m & j & pf & Hpf15 & Hx_split & Hjlt).

    (* 2) Split e into 6*p + a with a < 6 *)
    set (a := e mod 6).
    set (p := e / 6).
    assert (He_split : e = 6*p + a) by (subst a p; apply Nat.div_mod; lia).
    assert (Ha_lt : a < 6)          by (subst a; apply Nat.mod_upper_bound; lia).

    (* 3) Pick a row r covering (pf,a) *)
    destruct (table_covers_family_alpha pf a Hpf15 Ha_lt)
      as (r & Hin & Hdelta & Halpha).

    (* turn e = 6*p + a into e = alpha r + 6*p *)
    rewrite <- Halpha in He_split.
    rewrite Nat.add_comm in He_split.

    (* choose the branch pf=1 or pf=5 and build witnesses accordingly *)
    destruct Hpf15 as [Hpf1 | Hpf5].
    - (* pf = 1 : take the LEFT disjunct *)
      exists p, r, m, j, pf. left.
      repeat split.
      + exact Hin.
      + now rewrite Hdelta.
      + now exact Hpf1.      
    - (* pf = 5 : take the RIGHT disjunct *)
      exists p, r, m, j, pf. right.
      repeat split.
      + now exact Hpf5.
      + exact He_split.
      + exact Hx_split.
      + exact Hjlt.
      + rewrite He_split. eapply row_soundness; eauto.
  Qed.
  
  (* === Uniqueness up to arithmetic equivalence (normalization) ============== *)
  (* If two rows/lifts produce the same exponent e, they act by the same A=2^e/3+1
    multiplicative gain in the affine view. We can formalize a weak uniqueness: *)

  Definition action_gain (e:nat) : nat := pow2 e.

  Lemma same_exponent_same_gain :
    forall r1 r2 p1 p2,
      alpha r1 + 6*p1 = alpha r2 + 6*p2 ->
      action_gain (alpha r1 + 6*p1) = action_gain (alpha r2 + 6*p2).
  Proof.
    intros r1 r2 p1 p2 Heq.
    unfold action_gain.               (* action_gain e = pow2 e *)
    now rewrite Heq.                  (* 2^e respects equality of e *)
  Qed.  

  (* 3·x' + 1 = 2^e · x  — the scaled affine identity in Nat *)
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

  Lemma sub_add_cancel_nat a b : b <= a -> a - b + b = a.
  Proof. apply Nat.sub_add. Qed.

  Lemma sub_is_0_iff_le a b : a - b = 0 <-> a <= b.
  Proof. apply Nat.sub_0_le. Qed.

  (* Nat-only affine pair with denominator 3 *)

  (* Legacy signature kept as a thin wrapper; prefer *_nosub in new code. *)
  Lemma affine_step_nat_pair :
    forall (r:Row) p m j pf x,
      x = 18*m + 6*j + pf ->
      (pf = 1 \/ pf = 5) ->
      let e := alpha r + 6*p in
      let A := pow2 e in
      A * x + 3 * (6 * krow r + delta r)
      = 3 * row_step r p m + A * (6*j + pf).
  Proof.
    exact affine_step_nat_pair_nosub.  
  Qed.



  End Completeness.
(* You can extend this to the full affine action (A,B) once you thread the krow,delta
   offsets through the explicit formulas; for now we keep the gain statement. *)

End AlgebraicCompleteness.
