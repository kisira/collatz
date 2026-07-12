(* ========================================================================== *)
(* ROQ/COQ FORMALIZATION: SECTION 17 - PARAMETER GEOMETRY & OPERATOR LAYERS   *)
(* ========================================================================== *)

(* 1. IMPORTS *)
From Stdlib Require Import ZArith.
From Stdlib Require Import QArith. (* Essential for A, B, v (Rationals) *)
From Stdlib Require Import QArith.Qminmax.
From Stdlib Require Import Psatz.   (* 'lra' solves Rational arithmetic *)
From Stdlib Require Import Qabs.

(* We work with Rationals for geometry, but keep Integers for raw params *)
Open Scope Q_scope. 

(* ========================================================================== *)
(* 2. PREREQUISITES (TOKENS & RAW Z PARAMS)                                   *)
(* Same as previous sections, needed to ground the geometry.                   *)
(* ========================================================================== *)

Inductive Token :=
  | Psi_0 | Psi_1 | Psi_2 | psi_0 | psi_1 | psi_2
  | omega_0 | omega_1 | omega_2 | Omega_0 | Omega_1 | Omega_2.

Record RowParams := mkParams { alpha : Z; beta : Z; c : Z; delta : Z }.

Definition get_params (t : Token) : RowParams :=
  match t with
  | Psi_0 => mkParams 2 2 (-2) 1   | Psi_1 => mkParams 4 56 (-2) 1
  | Psi_2 => mkParams 6 416 (-2) 1 | omega_0 => mkParams 3 20 (-2) 1
  | omega_1 => mkParams 1 11 (-2) 1| omega_2 => mkParams 5 272 (-2) 1
  | psi_0 => mkParams 4 8 (-8) 5   | psi_1 => mkParams 6 224 (-8) 5
  | psi_2 => mkParams 2 26 (-8) 5  | Omega_0 => mkParams 5 80 (-8) 5
  | Omega_1 => mkParams 3 44 (-8) 5| Omega_2 => mkParams 1 17 (-8) 5
  end.

(* Helper Z functions needed to calculate K *)
Definition pow2 (n : Z) : Z := 2 ^ n.
Definition pow4 (n : Z) : Z := 4 ^ n.
Definition pow64 (n : Z) : Z := 64 ^ n.

(* The Integer Slope Factor K from the paper *)
(* K = (2^(alpha+6p) - 3) * 4^p *)
Definition calc_K_Z (t : Token) (p : Z) : Z :=
  let params := get_params t in
  (pow2 (params.(alpha) + 6 * p) - 3) * pow4 p.

(* The Geometric Accumulator q_p = (4^p - 1) / 3 *)
Definition calc_q_p_Z (p : Z) : Z := (pow4 p - 1) / 3.

(* ========================================================================== *)
(* 3. SECTION 17: OPERATOR PROJECTION (Phi)                                   *)
(* Mapping discrete params -> Rational Affine Operators (A, B)                 *)
(* ========================================================================== *)

(* 3.1 The Gain A = 1 + K/3 *)
(* We use 'inject_Z' to turn integers into rationals for division *)
Definition calc_A (t : Token) (p : Z) : Q :=
  1 + (inject_Z (calc_K_Z t p) / 3).

(* 3.2 The Offsets B_epsilon *)
(* The paper defines two possible B values per row depending on input family *)
(* B_1 = 4*q_p - K/3 *)
Definition calc_B_e (t : Token) (p : Z) : Q :=
  let K := inject_Z (calc_K_Z t p) in
  let q := inject_Z (calc_q_p_Z p) in
  (4 * q) - (K / 3).

(* B_5 = 10*q_p - 2 - 5K/3 *)
Definition calc_B_o (t : Token) (p : Z) : Q :=
  let K := inject_Z (calc_K_Z t p) in
  let q := inject_Z (calc_q_p_Z p) in
  (10 * q) - 2 - (5 * K / 3).

(* 3.3 The Operator Projection Phi(Theta) *)
(* Returns the pair (A, B) based on the token's input family *)
Definition Phi (t : Token) (p : Z) : (Q * Q) :=
  let A := calc_A t p in
  let B := 
    match t with
    (* If input required is family e (1 mod 6) *)
    | Psi_0 | Psi_1 | Psi_2 | psi_0 | psi_1 | psi_2 => calc_B_e t p
    (* If input required is family o (5 mod 6) *)
    | _ => calc_B_o t p
    end in
  (A, B).

(* 3.4 The Geometric Fixed Point v *)
(* v = B / (A - 1) *)
(* This represents the center of expansion for the affine map *)
Definition calc_v (t : Token) (p : Z) : Q :=
  let (A, B) := Phi t p in
  B / (A - 1).

(* ========================================================================== *)
(* 4. GEOMETRIC THEOREMS                                                      *)
(* Verifying the topological properties asserted in Section 17                *)
(* ========================================================================== *)

Lemma pow2_ge_2_nat (k : nat) :
  (k >= 1)%nat -> (2 ^ k >= 2)%nat.
Proof.
  destruct k as [|k].
  - (* k = 0 *)
    lia.
  - (* k = S k *)
    simpl.  intro Hk.                       (* goal: 2 * 2 ^ k >= 2 *)
    assert (Hpow_ge1 : (2 ^ k >= 1)%nat).
    { (* local lemma: 2^k >= 1 for all k *)
      induction k as [|k IH]; simpl; lia.
    }
    lia.
Qed.

Lemma pow2_ge_1 (n : Z) :
  (n >= 0)%Z -> (Z.pow 2 n >= 1)%Z.
Proof.
  intros Hn.
  (* Use monotonicity of Z.pow in the exponent *)
  assert (H := Z.pow_le_mono_r 2 0 n).  (* 1 < 2, 0 <= n -> 2^0 <= 2^n *)
  assert (Hle : (2 ^ 0 <= 2 ^ n)%Z).
  { apply H; lia. }
  simpl in Hle.  (* 2 ^ 0 = 1 *)
  lia.
Qed.

Lemma pow4_ge_1 (p : Z) :
  (p >= 0)%Z -> (4 ^ p >= 1)%Z.
Proof.
  intros Hp.
  (* Step 1: rewrite 4^p as 2^(2*p) *)
  assert (Hpow : (4 ^ p)%Z = (2 ^ (2 * p))%Z).
  {
    change 4%Z with (2 ^ 2)%Z.
    (* now RHS is (2^2)^p, so pow_mul_r applies *)
    rewrite Z.pow_mul_r by lia.
    reflexivity.
  }
  rewrite Hpow.
  (* Step 2: use your existing lemma pow2_ge_1 *)
  apply pow2_ge_1.
  (* need 2 * p >= 0 *)
  lia.
Qed.

(* If z ≥ 1 in Z, then 1 ≤ z in Q *)
Lemma Z_ge_1_to_Q_le (z : Z) :
  (z >= 1)%Z -> (1 <= inject_Z z)%Q.
Proof.
  intros Hz.
  unfold Qle; simpl.
  (* Clean up the useless *1 factors *)
  replace (1 * 1)%Z with 1%Z by lia.
  replace (z * 1)%Z with z%Z by lia.
  lia.  
Qed.

Lemma gain_from_Z_pos (K : Z) :
  (K > 0)%Z ->
  (1 < 1 + inject_Z K / 3)%Q.
Proof.
  intro HK.
  (* Let q := K/3 as a rational *)
  set (q := inject_Z K / 3).

  (* It is enough to show 0 < q, then we can add 1 to both sides. *)
  assert (Hq : (0 < q)%Q).
  {
    subst q.
    unfold Qdiv.
    (* q = inject_Z K * (1#3) *)
    apply Qmult_lt_0_compat.
    - (* inject_Z K > 0 because K > 0 *)
      unfold inject_Z.
      unfold Qlt; simpl.
      (* 0 < K#1  <-> 0 * 1 < K * 1  <-> 0 < K *)
      rewrite Z.mul_1_r.
      assert (HK' : (0 < K)%Z) by lia.
      exact HK'.
    - (* 1#3 > 0 *)
      unfold Qlt; simpl; lia.
  }

  (* From 0 < q we get 1 < 1 + q by adding 1 to both sides. *)
  (* Use the library lemma [Qplus_lt_le_compat]. *)
  pose proof (Qplus_lt_le_compat 0 q 1 1 Hq (Qle_refl 1)) as H.
  (* H : 0 + 1 < q + 1  i.e. 1 < 1 + q *)
  simpl in H.
  change (0 + 1)%Q with 1%Q in H.
  rewrite Qplus_comm in H.
  exact H.
Qed.

(* All always-expanding tokens: K_Z > 0 for all p >= 0 *)

Lemma calc_K_Z_Psi_0_pos :
  forall p, (p >= 0)%Z -> (calc_K_Z Psi_0 p > 0)%Z.
Proof.
  intros p Hp.
  unfold calc_K_Z, calc_K_Z, get_params, alpha in *.
  (* Now goal is: (2 ^ (2 + 6 * p) - 3) * 4 ^ p > 0 *)

  assert (Hbracket : (2 ^ (2 + 6 * p) - 3 > 0)%Z).
  {
    (* 2^(2+6p) >= 2^2 = 4, so 2^(2+6p)-3 >= 1 *)
    assert (Hexp_ge : (2 ^ (2 + 6 * p) >= 4)%Z).
    {
      (* rewrite as 2^(2+6p) = 4 * 2^(6p) and use pow2_ge_1 *)
      rewrite Z.pow_add_r by lia.
      change (2 ^ 2)%Z with 4%Z.
      assert (Hpow_ge1 : (2 ^ (6 * p) >= 1)%Z).
      { apply pow2_ge_1; lia. }
      lia.
    }
    assert (Hge1 : (2 ^ (2 + 6 * p) - 3 >= 1)%Z) by lia.
    assert (Hpos : (2 ^ (2 + 6 * p) - 3 > 0)%Z) by lia.    
    exact Hpos.    
  }

  (* 4^p > 0 for all p >= 0 *)
  assert (H4_pos : (4 ^ p > 0)%Z).
  {
    (* 4^p >= 1, thus > 0 *)
    assert (H4_ge1 : (4 ^ p >= 1)%Z).
    { 
      apply pow4_ge_1; lia.           
    }
    lia.
  }
  apply Z.compare_gt_iff.
  apply Z.compare_gt_iff in Hbracket.
  apply Z.compare_gt_iff in H4_pos.
  (* now Hbracket : 0 < ... , H4_pos : 0 < ... *)
  apply Z.mul_pos_pos; assumption.  
Qed.


Lemma calc_K_Z_Psi_1_pos (p : Z) :
  forall p : Z, (p >= 0)%Z -> (calc_K_Z Psi_1 p > 0)%Z.
Proof. 
  intros p' Hp.
  unfold calc_K_Z, get_params, alpha in *.  
  (* 1. show 2^(4 + 6p) - 3 > 0 *)
  assert (Hbracket : (2 ^ (4 + 6 * p') - 3 > 0)%Z).
  {
    assert (Hge : (2 ^ (4 + 6 * p') >= 16)%Z).
    {
      assert (Hexp_ge1 : (2 ^ (6 * p') >= 1)%Z).
      { apply pow2_ge_1. lia. }       
      rewrite Z.pow_add_r by lia.
      change (2 ^ 4)%Z with 16%Z.
      lia.      
    }
    assert (Hpos : (2 ^ (4 + 6 * p') - 3 >= 1)%Z) by lia.
    lia.
  }
  (* 2. show 4^p > 0 *)
  assert (H4_pos : (4 ^ p' > 0)%Z).
  {
    assert (H4_ge1 : (4 ^ p' >= 1)%Z).
    {
      apply pow4_ge_1; lia.      
    }
    lia.
  }
  (* 3. product positive *)
  apply Z.compare_gt_iff.
  apply Z.compare_gt_iff in Hbracket.
  apply Z.compare_gt_iff in H4_pos.
  apply Z.mul_pos_pos; assumption.
Qed.

Lemma calc_K_Z_Psi_2_pos (p : Z) :
  forall p : Z, (p >= 0)%Z -> (calc_K_Z Psi_2 p > 0)%Z.
Proof. 
  intros p' Hp.
  unfold calc_K_Z, get_params, alpha in *.    
  assert (Hbracket : (2 ^ (6 + 6 * p') - 3 > 0)%Z).
  {
    assert (Hge : (2 ^ (6 + 6 * p') >= 64)%Z).
    {
      assert (Hexp_ge1 : (2 ^ (6 * p') >= 1)%Z).
      { apply pow2_ge_1. lia. }       
      rewrite Z.pow_add_r by lia.
      change (2 ^ 6)%Z with 64%Z.
      lia.      
    }
    assert (Hpos : (2 ^ (6 + 6 * p') - 3 >= 1)%Z) by lia.
    lia.
  }
  (* 2. show 4^p > 0 *)
  assert (H4_pos : (4 ^ p' > 0)%Z).
  {
    assert (H4_ge1 : (4 ^ p' >= 1)%Z).
    {
      apply pow4_ge_1; lia.      
    }
    lia.
  }
  (* 3. product positive *)
  apply Z.compare_gt_iff.
  apply Z.compare_gt_iff in Hbracket.
  apply Z.compare_gt_iff in H4_pos.
  apply Z.mul_pos_pos; assumption.
Qed.

Lemma calc_K_Z_psi_0_pos (p : Z) :
  forall p : Z, (p >= 0)%Z -> (calc_K_Z psi_0 p > 0)%Z.
Proof. 
  intros p' Hp.
  unfold calc_K_Z, get_params, alpha in *.    
  assert (Hbracket : (2 ^ (4 + 6 * p') - 3 > 0)%Z).
  {
    assert (Hge : (2 ^ (4 + 6 * p') >= 16)%Z).
    {
      assert (Hexp_ge1 : (2 ^ (6 * p') >= 1)%Z).
      { apply pow2_ge_1. lia. }       
      rewrite Z.pow_add_r by lia.
      change (2 ^ 4)%Z with 16%Z.
      lia.      
    }
    assert (Hpos : (2 ^ (4 + 6 * p') - 3 >= 1)%Z) by lia.
    lia.
  }
  (* 2. show 4^p > 0 *)
  assert (H4_pos : (4 ^ p' > 0)%Z).
  {
    assert (H4_ge1 : (4 ^ p' >= 1)%Z).
    {
      apply pow4_ge_1; lia.      
    }
    lia.
  }
  (* 3. product positive *)
  apply Z.compare_gt_iff.
  apply Z.compare_gt_iff in Hbracket.
  apply Z.compare_gt_iff in H4_pos.
  apply Z.mul_pos_pos; assumption.
Qed.

Lemma calc_K_Z_psi_1_pos (p : Z) :
  forall p : Z, (p >= 0)%Z -> (calc_K_Z psi_1 p > 0)%Z.
Proof. 
  intros p' Hp.
  unfold calc_K_Z, get_params, alpha in *.    
  assert (Hbracket : (2 ^ (6 + 6 * p') - 3 > 0)%Z).
  {
    assert (Hge : (2 ^ (6 + 6 * p') >= 64)%Z).
    {
      assert (Hexp_ge1 : (2 ^ (6 * p') >= 1)%Z).
      { apply pow2_ge_1. lia. }       
      rewrite Z.pow_add_r by lia.
      change (2 ^ 6)%Z with 64%Z.
      lia.      
    }
    assert (Hpos : (2 ^ (6 + 6 * p') - 3 >= 1)%Z) by lia.
    lia.
  }
  (* 2. show 4^p > 0 *)
  assert (H4_pos : (4 ^ p' > 0)%Z).
  {
    assert (H4_ge1 : (4 ^ p' >= 1)%Z).
    {
      apply pow4_ge_1; lia.      
    }
    lia.
  }
  (* 3. product positive *)
  apply Z.compare_gt_iff.
  apply Z.compare_gt_iff in Hbracket.
  apply Z.compare_gt_iff in H4_pos.
  apply Z.mul_pos_pos; assumption.
Qed.

Lemma calc_K_Z_psi_2_pos (p : Z) :
  forall p : Z, (p >= 0)%Z -> (calc_K_Z psi_2 p > 0)%Z.
Proof. 
  intros p' Hp.
  unfold calc_K_Z, get_params, alpha in *.    
  assert (Hbracket : (2 ^ (2 + 6 * p') - 3 > 0)%Z).
  {
    assert (Hge : (2 ^ (2 + 6 * p') >= 4)%Z).
    {
      assert (Hexp_ge1 : (2 ^ (6 * p') >= 1)%Z).
      { apply pow2_ge_1. lia. }       
      rewrite Z.pow_add_r by lia.
      change (2 ^ 2)%Z with 4%Z.
      lia.      
    }
    assert (Hpos : (2 ^ (2 + 6 * p') - 3 >= 1)%Z) by lia.
    lia.
  }
  (* 2. show 4^p > 0 *)
  assert (H4_pos : (4 ^ p' > 0)%Z).
  {
    assert (H4_ge1 : (4 ^ p' >= 1)%Z).
    {
      apply pow4_ge_1; lia.      
    }
    lia.
  }
  (* 3. product positive *)
  apply Z.compare_gt_iff.
  apply Z.compare_gt_iff in Hbracket.
  apply Z.compare_gt_iff in H4_pos.
  apply Z.mul_pos_pos; assumption.
Qed.

Lemma calc_K_Z_omega_0_pos (p : Z) :
  forall p : Z, (p >= 0)%Z -> (calc_K_Z omega_0 p > 0)%Z.
Proof. 
  intros p' Hp.
  unfold calc_K_Z, get_params, alpha in *.    
  assert (Hbracket : (2 ^ (3 + 6 * p') - 3 > 0)%Z).
  {
    assert (Hge : (2 ^ (3 + 6 * p') >= 8)%Z).
    {
      assert (Hexp_ge1 : (2 ^ (6 * p') >= 1)%Z).
      { apply pow2_ge_1. lia. }       
      rewrite Z.pow_add_r by lia.
      change (2 ^ 3)%Z with 8%Z.
      lia.      
    }
    assert (Hpos : (2 ^ (3 + 6 * p') - 3 >= 1)%Z) by lia.
    lia.
  }
  (* 2. show 4^p > 0 *)
  assert (H4_pos : (4 ^ p' > 0)%Z).
  {
    assert (H4_ge1 : (4 ^ p' >= 1)%Z).
    {
      apply pow4_ge_1; lia.      
    }
    lia.
  }
  (* 3. product positive *)
  apply Z.compare_gt_iff.
  apply Z.compare_gt_iff in Hbracket.
  apply Z.compare_gt_iff in H4_pos.
  apply Z.mul_pos_pos; assumption.
Qed.

Lemma calc_K_Z_omega_2_pos (p : Z) :
  forall p : Z, (p >= 0)%Z -> (calc_K_Z omega_2 p > 0)%Z.
Proof. 
  intros p' Hp.
  unfold calc_K_Z, get_params, alpha in *.    
  assert (Hbracket : (2 ^ (5 + 6 * p') - 3 > 0)%Z).
  {
    assert (Hge : (2 ^ (5 + 6 * p') >= 32)%Z).
    {
      assert (Hexp_ge1 : (2 ^ (6 * p') >= 1)%Z).
      { apply pow2_ge_1. lia. }       
      rewrite Z.pow_add_r by lia.
      change (2 ^ 5)%Z with 32%Z.
      lia.      
    }
    assert (Hpos : (2 ^ (5 + 6 * p') - 3 >= 1)%Z) by lia.
    lia.
  }
  (* 2. show 4^p > 0 *)
  assert (H4_pos : (4 ^ p' > 0)%Z).
  {
    assert (H4_ge1 : (4 ^ p' >= 1)%Z).
    {
      apply pow4_ge_1; lia.      
    }
    lia.
  }
  (* 3. product positive *)
  apply Z.compare_gt_iff.
  apply Z.compare_gt_iff in Hbracket.
  apply Z.compare_gt_iff in H4_pos.
  apply Z.mul_pos_pos; assumption.
Qed.

Lemma calc_K_Z_Omega_0_pos (p : Z) :
  forall p : Z, (p >= 0)%Z -> (calc_K_Z Omega_0 p > 0)%Z.
Proof. 
  intros p' Hp.
  unfold calc_K_Z, get_params, alpha in *.    
  assert (Hbracket : (2 ^ (5 + 6 * p') - 3 > 0)%Z).
  {
    assert (Hge : (2 ^ (5 + 6 * p') >= 32)%Z).
    {
      assert (Hexp_ge1 : (2 ^ (6 * p') >= 1)%Z).
      { apply pow2_ge_1. lia. }       
      rewrite Z.pow_add_r by lia.
      change (2 ^ 5)%Z with 32%Z.
      lia.      
    }
    assert (Hpos : (2 ^ (5 + 6 * p') - 3 >= 1)%Z) by lia.
    lia.
  }
  (* 2. show 4^p > 0 *)
  assert (H4_pos : (4 ^ p' > 0)%Z).
  {
    assert (H4_ge1 : (4 ^ p' >= 1)%Z).
    {
      apply pow4_ge_1; lia.      
    }
    lia.
  }
  (* 3. product positive *)
  apply Z.compare_gt_iff.
  apply Z.compare_gt_iff in Hbracket.
  apply Z.compare_gt_iff in H4_pos.
  apply Z.mul_pos_pos; assumption.
Qed.

Lemma calc_K_Z_Omega_1_pos (p : Z) :
  forall p : Z, (p >= 0)%Z -> (calc_K_Z Omega_1 p > 0)%Z.
Proof. 
  intros p' Hp.
  unfold calc_K_Z, get_params, alpha in *.    
  assert (Hbracket : (2 ^ (3 + 6 * p') - 3 > 0)%Z).
  {
    assert (Hge : (2 ^ (3 + 6 * p') >= 8)%Z).
    {
      assert (Hexp_ge1 : (2 ^ (6 * p') >= 1)%Z).
      { apply pow2_ge_1. lia. }       
      rewrite Z.pow_add_r by lia.
      change (2 ^ 3)%Z with 8%Z.
      lia.      
    }
    assert (Hpos : (2 ^ (3 + 6 * p') - 3 >= 1)%Z) by lia.
    lia.
  }
  (* 2. show 4^p > 0 *)
  assert (H4_pos : (4 ^ p' > 0)%Z).
  {
    assert (H4_ge1 : (4 ^ p' >= 1)%Z).
    {
      apply pow4_ge_1; lia.      
    }
    lia.
  }
  (* 3. product positive *)
  apply Z.compare_gt_iff.
  apply Z.compare_gt_iff in Hbracket.
  apply Z.compare_gt_iff in H4_pos.
  apply Z.mul_pos_pos; assumption.
Qed.

(* omega_1: maybe contracting at p = 0, expanding for p >= 1 *)

Lemma calc_K_Z_omega_1_p0_neg :
  (calc_K_Z omega_1 0 < 0)%Z.
Proof.
  unfold calc_K_Z.
  cbn [get_params alpha pow2 pow4]. (* or whatever your pow2/pow4 names are *)
  (* At this point your goal should basically be: (2 ^ 1 - 3) * 1 < 0 *)
  (* If Coq doesn’t fully reduce, you can help it a bit: *)
  change (alpha (get_params omega_1)) with 1.
  change (4 ^ 0) with 1%Z.
  change (2 ^ 1) with 2%Z.
  simpl.
  (* Now goal should literally be: (2 - 3) * 1 < 0  i.e. (-1) < 0 *)
  lia.
Qed.


Lemma calc_K_Z_omega_1_pos_ge1 (p : Z) :
  (p >= 1)%Z -> (calc_K_Z omega_1 p > 0)%Z.
Proof. 
  intros Hp.
  unfold calc_K_Z, get_params, alpha in *.
  (* omega_1 has alpha = 1. Goal: (2^(1 + 6*p) - 3) * 4^p > 0 *)

  (* 1. Show the first term (2^(...) - 3) is positive *)
  assert (Hbracket : (2 ^ (1 + 6 * p) - 3 > 0)%Z).
  {
    (* Since p >= 1, the exponent is at least 7 *)
    assert (H_exp_val : (1 + 6 * p >= 7)%Z) by lia.

    (* We use monotonicity: if a <= b, then 2^a <= 2^b *)
    assert (H_pow_val : (2 ^ 7 <= 2 ^ (1 + 6 * p))%Z).
    { 
      apply Z.pow_le_mono_r; lia. 
    }

    (* Evaluate 2^7 -> 128 *)
    change (2 ^ 7)%Z with 128%Z in H_pow_val.
    
    (* 128 <= 2^(...) implies 2^(...) - 3 >= 125 > 0 *)
    lia.
  }

  (* 2. Show the second term (4^p) is positive *)
  assert (H4_pos : (4 ^ p > 0)%Z).
  {
    (* Since p >= 1, 4^p >= 4 *)
    assert (4 ^ 1 <= 4 ^ p)%Z.
    { apply Z.pow_le_mono_r; lia. }
    lia.
  }
  unfold pow2, pow4. (* Expose 2^ and 4^ to match Hbracket/H4_pos *)
  nia.
Qed.

(* Omega_2: maybe contracting at p = 0, expanding for p >= 1 *)

Lemma calc_K_Z_Omega_2_p0_neg :
  (calc_K_Z Omega_2 0 < 0)%Z.
Proof.
  unfold calc_K_Z.
  cbn [get_params alpha pow2 pow4].
  change (alpha (get_params Omega_2)) with 1.
  change (4 ^ 0) with 1%Z.
  change (2 ^ 1) with 2%Z.
  simpl.
  lia.
Qed.


Lemma calc_K_Z_Omega_2_pos_ge1 (p : Z) :
  (p >= 1)%Z -> (calc_K_Z Omega_2 p > 0)%Z.
Proof.
  intro Hp.
  (* 1. Expose the math definitions *)
  unfold calc_K_Z, get_params, alpha.
  unfold pow2, pow4.
  
  (* Omega_2 has alpha=1, so we prove: (2^(1+6p) - 3) * 4^p > 0 *)

  (* 2. Prove the first term is positive *)
  assert (Hbracket : (2 ^ (1 + 6 * p) - 3 > 0)%Z).
  {
    (* Since p >= 1, the exponent is at least 7 *)
    assert (H_exp_val : (1 + 6 * p >= 7)%Z) by lia.

    (* 2^7 = 128, so 2^(1+6p) >= 128 *)
    assert (H_pow_val : (2 ^ 7 <= 2 ^ (1 + 6 * p))%Z).
    { apply Z.pow_le_mono_r; lia. }
    
    change (2 ^ 7)%Z with 128%Z in H_pow_val.
    lia. (* 128 - 3 > 0 *)
  }

  (* 3. Prove the second term is positive *)
  assert (H4_pos : (4 ^ p > 0)%Z).
  {
    (* p >= 1 implies 4^p >= 4 *)
    assert (4 ^ 1 <= 4 ^ p)%Z.
    { apply Z.pow_le_mono_r; lia. }
    lia.
  }

  (* 4. Solve the final inequality *)
  nia.
Qed.

Lemma gain_Psi_0 (p : Z) :
  (p >= 0)%Z ->
  (calc_A Psi_0 p > 1)%Q.
Proof.
  intro Hp.
  unfold calc_A.
  set (K := calc_K_Z Psi_0 p).
  change (1 < 1 + inject_Z K / 3)%Q.
  apply gain_from_Z_pos.
  apply calc_K_Z_Psi_0_pos; exact Hp.
Qed.

Lemma gain_Psi_1 (p : Z) :
  (p >= 0)%Z ->
  (calc_A Psi_1 p > 1)%Q.
Proof.
  intro Hp.
  unfold calc_A.
  set (K := calc_K_Z Psi_1 p).
  change (1 < 1 + inject_Z K / 3)%Q.
  apply gain_from_Z_pos.
  apply calc_K_Z_Psi_1_pos; assumption.  
Qed.

Lemma gain_Psi_2 (p : Z) :
  (p >= 0)%Z ->
  (calc_A Psi_2 p > 1)%Q.
Proof.
  intro Hp.
  unfold calc_A.
  set (K := calc_K_Z Psi_2 p).
  change (1 < 1 + inject_Z K / 3)%Q.
  apply gain_from_Z_pos.
  apply calc_K_Z_Psi_2_pos; assumption.
Qed.

Lemma gain_psi_0 (p : Z) :
  (p >= 0)%Z ->
  (calc_A psi_0 p > 1)%Q.
Proof.
  intro Hp.
  unfold calc_A.
  set (K := calc_K_Z psi_0 p).
  change (1 < 1 + inject_Z K / 3)%Q.
  apply gain_from_Z_pos.
  apply calc_K_Z_psi_0_pos; assumption.
Qed.

Lemma gain_psi_1 (p : Z) :
  (p >= 0)%Z ->
  (calc_A psi_1 p > 1)%Q.
Proof.
  intro Hp.
  unfold calc_A.
  set (K := calc_K_Z psi_1 p).
  change (1 < 1 + inject_Z K / 3)%Q.
  apply gain_from_Z_pos.
  apply calc_K_Z_psi_1_pos; assumption.
Qed.

Lemma gain_psi_2 (p : Z) :
  (p >= 0)%Z ->
  (calc_A psi_2 p > 1)%Q.
Proof.
  intro Hp.
  unfold calc_A.
  set (K := calc_K_Z psi_2 p).
  change (1 < 1 + inject_Z K / 3)%Q.
  apply gain_from_Z_pos.
  apply calc_K_Z_psi_2_pos; assumption.
Qed.

Lemma gain_omega_0 (p : Z) :
  (p >= 0)%Z ->
  (calc_A omega_0 p > 1)%Q.
Proof.
  intro Hp.
  unfold calc_A.
  set (K := calc_K_Z omega_0 p).
  change (1 < 1 + inject_Z K / 3)%Q.
  apply gain_from_Z_pos.
  apply calc_K_Z_omega_0_pos; assumption.
Qed.

Lemma gain_omega_2 (p : Z) :
  (p >= 0)%Z ->
  (calc_A omega_2 p > 1)%Q.
Proof.
  intro Hp.
  unfold calc_A.
  set (K := calc_K_Z omega_2 p).
  change (1 < 1 + inject_Z K / 3)%Q.
  apply gain_from_Z_pos.
  apply calc_K_Z_omega_2_pos; assumption.
Qed.

Lemma gain_Omega_0 (p : Z) :
  (p >= 0)%Z ->
  (calc_A Omega_0 p > 1)%Q.
Proof.
  intro Hp.
  unfold calc_A.
  set (K := calc_K_Z Omega_0 p).
  change (1 < 1 + inject_Z K / 3)%Q.
  apply gain_from_Z_pos.
  apply calc_K_Z_Omega_0_pos; assumption.
Qed.

Lemma gain_Omega_1 (p : Z) :
    (p >= 0)%Z ->
  (calc_A Omega_1 p > 1)%Q.
Proof.
  intro Hp.
  unfold calc_A.
  set (K := calc_K_Z Omega_1 p).
  change (1 < 1 + inject_Z K / 3)%Q.
  apply gain_from_Z_pos.
  apply calc_K_Z_Omega_1_pos; assumption.
Qed.

(* omega_1: contracting at p = 0 *)

Lemma loss_omega_1_p0 :
  (calc_A omega_1 0 < 1)%Q.
Proof.
  (* 1. Unfold all definitions down to raw numbers *)
  unfold calc_A, calc_K_Z, get_params, alpha, pow2, pow4.
  
  (* 2. Simplify the integer arithmetic *)
  (* This reduces (2^(1+0)-3)*1 to -1 *)
  vm_compute. 
  
  (* 3. Goal is now roughly: 2/3 < 1 *)
  reflexivity.
Qed.

Lemma gain_omega_1_ge1 (p : Z) :
  (p >= 1)%Z ->
  (calc_A omega_1 p > 1)%Q.
Proof.
  intro Hp.
  unfold calc_A.
  set (K := calc_K_Z omega_1 p).
  change (1 < 1 + inject_Z K / 3)%Q.
  apply gain_from_Z_pos.
  apply calc_K_Z_omega_1_pos_ge1; exact Hp.
Qed.

(* Omega_2: contracting at p = 0 *)

Lemma loss_Omega_2_p0 :
  (calc_A Omega_2 0 < 1)%Q.
Proof.
  unfold calc_A.
  set (K := calc_K_Z Omega_2 0).
  change (1 + inject_Z K / 3 < 1)%Q.  
  apply calc_K_Z_Omega_2_p0_neg.
Qed.

Lemma gain_Omega_2_ge1 (p : Z) :
  (p >= 1)%Z ->
  (calc_A Omega_2 p > 1)%Q.
Proof.
  intro Hp.
  unfold calc_A.
  set (K := calc_K_Z Omega_2 p).
  change (1 < 1 + inject_Z K / 3)%Q.
  apply gain_from_Z_pos.
  apply calc_K_Z_Omega_2_pos_ge1; exact Hp.
Qed.


Theorem gain_expansive_except_singularities : forall (t : Token) (p : Z),
  (p >= 0)%Z ->
  (* The set of contractive tokens at p=0 *)
  ~ ((p = 0)%Z /\ (t = omega_1 \/ t = Omega_2)) ->
  calc_A t p > 1.
Proof.
  intros t p Hp Hnot_singular.

  (* Split into p=0 and p>=1 *)
  destruct (Z.eq_dec p 0) as [Heq | Hneq].

  (* ======================================================== *)
  (* CASE 1: p = 0                                            *)
  (* ======================================================== *)
  - subst p.
    destruct t.
    
    (* 1. Psi_0 *)
    + unfold calc_A, calc_K_Z, get_params, alpha, pow2, pow4.
      vm_compute. unfold Qlt. simpl. reflexivity.
    (* 2. Psi_1 *)
    + unfold calc_A, calc_K_Z, get_params, alpha, pow2, pow4.
      vm_compute. unfold Qlt. simpl. reflexivity.
    (* 3. Psi_2 *)
    + unfold calc_A, calc_K_Z, get_params, alpha, pow2, pow4.
      vm_compute. unfold Qlt. simpl. reflexivity.
      
    (* 4. psi_0 *)
    + unfold calc_A, calc_K_Z, get_params, alpha, pow2, pow4.
      vm_compute. unfold Qlt. simpl. reflexivity.
    (* 5. psi_1 *)
    + unfold calc_A, calc_K_Z, get_params, alpha, pow2, pow4.
      vm_compute. unfold Qlt. simpl. reflexivity.
    (* 6. psi_2 *)
    + unfold calc_A, calc_K_Z, get_params, alpha, pow2, pow4.
      vm_compute. unfold Qlt. simpl. reflexivity.
      
    (* 7. omega_0 *)
    + unfold calc_A, calc_K_Z, get_params, alpha, pow2, pow4.
      vm_compute. unfold Qlt. simpl. reflexivity.
    (* 8. omega_1 (SINGULARITY) *)
    + exfalso. apply Hnot_singular. split; [reflexivity | left; reflexivity].
    (* 9. omega_2 *)
    + unfold calc_A, calc_K_Z, get_params, alpha, pow2, pow4.
      vm_compute. unfold Qlt. simpl. reflexivity.
      
    (* 10. Omega_0 *)
    + unfold calc_A, calc_K_Z, get_params, alpha, pow2, pow4.
      vm_compute. unfold Qlt. simpl. reflexivity.
    (* 11. Omega_1 *)
    + unfold calc_A, calc_K_Z, get_params, alpha, pow2, pow4.
      vm_compute. unfold Qlt. simpl. reflexivity.
    (* 12. Omega_2 (SINGULARITY) *)
    + exfalso. apply Hnot_singular. split; [reflexivity | right; reflexivity].

  (* ======================================================== *)
  (* CASE 2: p >= 1                                           *)
  (* ======================================================== *)
  - assert (Hp_ge1 : (p >= 1)%Z) by lia.
    unfold calc_A; apply gain_from_Z_pos.
    
    destruct t.
    
    (* 1. Psi_0 *)
    + apply calc_K_Z_Psi_0_pos; lia.
    (* 2. Psi_1 *)
    + apply calc_K_Z_Psi_1_pos. assumption. lia.
    (* 3. Psi_2 *)
    + apply calc_K_Z_Psi_2_pos. assumption. lia.
    
    (* 4. psi_0 *)
    + apply calc_K_Z_psi_0_pos. assumption. lia.
    (* 5. psi_1 *)
    + apply calc_K_Z_psi_1_pos. assumption. lia.
    (* 6. psi_2 *)
    + apply calc_K_Z_psi_2_pos. assumption. lia.
    
    (* 7. omega_0 *)
    + apply calc_K_Z_omega_0_pos. assumption. lia.
    (* 8. omega_1 (Using _ge1 lemma) *)
    + apply calc_K_Z_omega_1_pos_ge1; assumption.
    (* 9. omega_2 *)
    + apply calc_K_Z_omega_2_pos. assumption. lia.
    
    (* 10. Omega_0 *)
    + apply calc_K_Z_Omega_0_pos. assumption. lia.
    (* 11. Omega_1 *)
    + apply calc_K_Z_Omega_1_pos. assumption. lia.
    (* 12. Omega_2 (Using _ge1 lemma) *)
    + apply calc_K_Z_Omega_2_pos_ge1; assumption.
Qed.

(* 4.2 Well-Definedness of Fixed Points *)
(* The fixed point v = B/(A-1) exists if A != 1. *)
(* Since A = 1 + K/3, we need K != 0. *)
(* From the previous proof, K > 0 usually, or K = -1. K is never 0. *)

Theorem fixed_point_valid : forall (t : Token) (p : Z),
  (p >= 0)%Z ->
  ~ (calc_A t p == 1).
Proof.
  intros t p Hp H_eq.
  unfold calc_A in H_eq.

  (* 1. Prove K = 0 by unfolding Rational arithmetic to Integer arithmetic *)
  (* Goal: 1 + K/3 == 1  ->  K = 0 *)
  assert (H_K: (calc_K_Z t p = 0)%Z).
  {
    (* 1. Simplify the equation using Q arithmetic lemmas first *)
    (* Goal: 1 + K/3 == 1 *)
    rewrite <- (Qplus_0_r 1) in H_eq at 2. (* Rewrite RHS '1' as '1+0' *)
    apply Qplus_inj_l in H_eq.             (* Subtract '1' from both sides *)
    
    (* 2. Now Goal is: K/3 == 0 *)
    (* Now we can safely unfold without generating messy additions *)
    unfold Qdiv, Qmult, inject_Z, Qeq in H_eq.
    simpl in H_eq.
    
    (* 3. Result is simple multiplication: K * 1 * 1 = 0 *)
    lia.
  }

  (* 2. Derive contradiction from K = 0 *)
  unfold calc_K_Z in H_K.
  (* K = (2^E - 3) * 4^p. Product is 0 implies one factor is 0 *)
  apply Z.mul_eq_0 in H_K.
  destruct H_K as [H_term | H_pow].

  - (* Case A: 2^(alpha + 6p) - 3 = 0  =>  2^E = 3 *)
    unfold pow2 in H_term.
    assert (H_imp: (2 ^ (alpha (get_params t) + 6 * p) = 3)%Z).
    {
      unfold pow2 in H_term.
      apply Z.sub_move_0_r in H_term.
      set (A := (2 ^ (alpha (get_params t) + 6 * p))%Z) in *.
      (* Now H_term is: (A - 3 - 0 = 0)%Z *)

      assert (HA : A = 3%Z).
      {
        (* Simplify the minus expression so lia can handle it *)
        assert (H_term_simp: (A - 3 - 0)%Z = (A - 3)%Z) by lia.
        rewrite H_term_simp in H_term.        
        lia.
      }

      subst A.      
      (* Goal is now exactly 2 ^ (alpha (get_params t) + 6 * p) = 3, done by HA *)
      rewrite HA.
      reflexivity.
    }    
    
    (* Prove 2^n <> 3 for any n >= 0 using modulo 4 *)
    assert (H_pow2_neq_3: forall n, (n >= 0)%Z -> (2^n <> 3)%Z).
    {
      intros n Hn.
      (* Check small cases n=0, n=1 manually *)
      destruct (Z.eq_dec n 0); [subst; simpl; lia |].
      destruct (Z.eq_dec n 1); [subst; simpl; lia |].
      
      (* For n >= 2, 2^n is divisible by 4 (0 mod 4), but 3 is 3 mod 4 *)
      assert (H_mod: (2^n mod 4 = 0)%Z).
      {
        replace n with ((2 + (n - 2))%Z) by lia.
         
         (* 2. Split the power: 2^(2 + k) = 2^2 * 2^k *)
         rewrite Z.pow_add_r; try lia.
         
         (* 3. Simplify 2^2 to 4 *)
         change (2^2) with 4.
         
         (* 4. Prove that (4 * X) mod 4 is 0 *)
         rewrite Z.mul_comm. 
         apply Z.mod_mul. 
         lia. (* Proves 4 <> 0 *)        
      }
      intro H_abs.
      rewrite H_abs in H_mod.
      (* 3 mod 4 is 3, not 0 *)
      vm_compute in H_mod. discriminate.
    }
    
    apply H_pow2_neq_3 in H_imp.
    * contradiction.
    * (* Prove exponent n >= 0 to satisfy the helper lemma *)
      (* Convert >= to <=, then split the sum *)
      apply Z.le_ge; apply Z.add_nonneg_nonneg.
      { destruct t; simpl; lia. } (* alpha >= 0 *)
      { lia. }                    (* 6*p >= 0 *)

  - (* Case B: 4^p = 0 *)
    (* Impossible because 4^p >= 1 *)
    assert (H_ge1: (4^p >= 1)%Z).
    { 
      unfold pow4.       
      apply pow4_ge_1; lia.    
    }
    unfold pow4 in H_pow.
    lia.
Qed.

(* 4.3 The Drift Metric Bound (Lemma 19) *)
(* drift <= |A-1|*X + |B| *)
(* 1. Define the drift function first *)
(* This calculates how much x changes in one step: (Ax + B) - x *)
Definition drift_at_x (t : Token) (p : Z) (x : Q) : Q :=
  let (A, B) := Phi t p in
  (A * x + B) - x.

Theorem drift_bound_linear : forall (t : Token) (p : Z) (x : Q),
  (x >= 1)%Q ->
  let (A, B) := Phi t p in
  Qabs (drift_at_x t p x) <= Qabs (A - 1) * x + Qabs B.
Proof.
  intros t p x Hx.
  unfold drift_at_x.
  destruct (Phi t p) as [A0 B0].

  (* 1. Algebraic simplification: (Ax + B) - x = (A-1)x + B *)
  (* 'field' solves rational field equations robustly *)
  assert (Heq : (A0 * x + B0) - x == (A0 - 1) * x + B0) by field.
  rewrite Heq.
  
  (* 2. Apply Triangle Inequality: |X + Y| <= |X| + |Y| *)
  pose proof (Qabs_triangle ((A0 - 1) * x) B0) as Htri.
  
  (* 3. Distribute Absolute Value over Product: |C * x| = |C| * |x| *)  
  rewrite Qabs_Qmult in Htri.
  
  (* 4. Simplify |x| to x manually *)
  (* We know x >= 1, so x >= 0. Qabs_pos removes the abs bars. *)
  assert (H_abs_x: Qabs x == x).
  {
    apply Qabs_pos.
    (* We must prove 0 <= x. We know 1 <= x, and 0 <= 1. *)
    apply Qle_trans with (y:=1).
    - unfold Qle; simpl; lia. (* Prove 0 <= 1 *)
    - exact Hx.               (* We know 1 <= x *)
  }  
  
  (* Now we use our specific assertion to rewrite only |x| *)
  rewrite H_abs_x in Htri.
  
  (* 5. Conclusion *)
  exact Htri.
Qed.

Theorem fixed_slope_distance : forall (t1 t2 : Token) (p : Z) (x : Q),
  (* If two tokens share the same p (and thus same A)... *)
  (fst (Phi t1 p) == fst (Phi t2 p)) ->
  (* ...the difference in their drift is exactly the difference in B *)
  let B1 := snd (Phi t1 p) in
  let B2 := snd (Phi t2 p) in
  Qabs (drift_at_x t1 p x - drift_at_x t2 p x) == Qabs (B1 - B2).
Proof.
  intros t1 t2 p x HA.
  unfold drift_at_x.
  
  (* Destruct the pairs to expose A1, B1, A2, B2 *)
  destruct (Phi t1 p) as [A1 B1].
  destruct (Phi t2 p) as [A2 B2].
  
  (* Crucial Step: Simplify to remove 'fst' and 'snd' *)
  (* This turns 'fst (A1, B1)' into 'A1', etc. *)
  simpl in HA.
  
  (* 2. Prove the algebraic equality of the contents first *)
  assert (H_diff: ((A1 * x + B1) - x) - ((A2 * x + B2) - x) == B1 - B2).
  {
    rewrite HA. (* Turns A1 into A2 *)
    field.      (* Solves the equation *)
  }
  
  (* 3. Rewrite the contents of the absolute value *)
  (* Since we didn't explode the goal, this sees 'Qabs (...)' and replaces the inside *)
  rewrite H_diff.
  
  (* 4. The goal is now Qabs (B1 - B2) == Qabs (B1 - B2) *)
  reflexivity.
Qed.
