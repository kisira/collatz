(* ========================================================================== *)
(* ROQ/COQ FORMALIZATION: SECTION 4 - CRT TAG & DRIFT CALCULUS                *)
(* ========================================================================== *)

(* -------------------------------------------------------------------------- *)
(* PART A: PREAMBLE & COMPATIBILITY LAYER                                     *)
(* -------------------------------------------------------------------------- *)

(* Standard Library Imports *)
From Coq Require Import ZArith Znumtheory Lia.
From Coq Require Import Psatz.
Open Scope Z_scope.

(* Compatibility Lemma: Fixes naming differences between Coq versions for power-mod *)
Lemma Z_pow_mod_compat : forall a b n : Z, 
  0 <= b -> 0 < n -> (a ^ b) mod n = ((a mod n) ^ b) mod n.
Proof.
  intros.
  try (apply Zpow_facts.Zpower_mod; assumption).   
Qed.

(* -------------------------------------------------------------------------- *)
(* PART B: THE UNIFIED TABLE (PREREQUISITES)                                  *)
(* We must define the tokens and row parameters to talk about Section 4.       *)
(* -------------------------------------------------------------------------- *)

Inductive Token :=
  | Psi_0 | Psi_1 | Psi_2   (* Family e *)
  | psi_0 | psi_1 | psi_2   (* Family e -> o *)
  | omega_0 | omega_1 | omega_2 (* Family o -> e *)
  | Omega_0 | Omega_1 | Omega_2. (* Family o *)

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

(* Helper Powers *)
Definition pow2 (n : Z) : Z := 2 ^ n.
Definition pow4 (n : Z) : Z := 4 ^ n.
Definition pow64 (n : Z) : Z := 64 ^ n.

(* Core Transformation F(p,m) from Section 2 *)
Definition F_transform (t : Token) (p : Z) (m : Z) : Z :=
  let params := get_params t in
  let term1 := (9 * m * (pow2 params.(alpha)) + params.(beta)) in
  let num   := term1 * (pow64 p) + params.(c) in
  num / 9.

(* The Child Value x' *)
Definition x_prime (t : Token) (p : Z) (m : Z) : Z :=
  let params := get_params t in
  6 * (F_transform t p m) + params.(delta).

(* Input Construction x = 18m + 6j + p6 *)
Definition get_input_reqs (t : Token) : (Z * Z) :=
  match t with
  | Psi_0 => (0, 1) | Psi_1 => (1, 1) | Psi_2 => (2, 1)
  | psi_0 => (0, 1) | psi_1 => (1, 1) | psi_2 => (2, 1)
  | omega_0 => (0, 5) | omega_1 => (1, 5) | omega_2 => (2, 5)
  | Omega_0 => (0, 5) | Omega_1 => (1, 5) | Omega_2 => (2, 5)
  end.

Definition construct_x (t : Token) (m : Z) : Z :=
  let (j, p6) := get_input_reqs t in
  18 * m + 6 * j + p6.

(* -------------------------------------------------------------------------- *)
(* PART C: LEMMA 6 (FOUNDATION)                                               *)
(* We need to prove the basic row identity to prove the drift equation.       *)
(* -------------------------------------------------------------------------- *)

(* -------------------------------------------------------------------------- *)
(* HELPER LEMMA: The Decomposition of 64^p                                    *)
(* This isolates the modular arithmetic so the main proof is clean.           *)
(* -------------------------------------------------------------------------- *)
Lemma pow64_decomp : forall p : Z, p >= 0 -> 64^p = 9 * (64^p / 9) + 1.
Proof.
  intros p Hp.
  (* 1. Apply Euclidean Division: a = b * (a/b) + (a mod b) *)
  rewrite (Z.div_mod (64^p) 9) at 1 by lia.
  
  (* 2. Prove the remainder (64^p mod 9) is 1 *)
  assert (Hrem: (64^p) mod 9 = 1).
  {
    rewrite Z_pow_mod_compat by lia.
    replace (64 mod 9) with 1 by reflexivity.
    rewrite Z.pow_1_l by lia.
    reflexivity.
  }
  
  (* 3. Substitute the remainder *)
  rewrite Hrem.
  reflexivity.
Qed.

(* -------------------------------------------------------------------------- *)
(* HELPER 2: Parameter Divisibility (Optimized)                               *)
(* -------------------------------------------------------------------------- *)
Lemma params_divisible_by_9 : forall (t : Token) (p : Z),
  p >= 0 ->
  let params := get_params t in
  (params.(beta) * 64^p + params.(c)) mod 9 = 0.
Proof.
  intros t p Hp params.
  
  (* 1. Prove the power property ONCE, before splitting cases *)
  assert (Hpow: (64^p) mod 9 = 1).
  { 
    rewrite Z_pow_mod_compat by lia. 
    replace (64 mod 9) with 1 by reflexivity.
    rewrite Z.pow_1_l by lia. 
    reflexivity.
  }

  (* 2. Expand definitions and split into 12 goals *)
  (* cbv is faster and cleaner than subst+simpl *)
  cbv [params get_params beta c]; destruct t.

  (* 3. Apply a single, fast script to all 12 goals *)
  all: 
    (* Break down (A + B) mod 9 and (A * B) mod 9 *)
    (* We use 'try lia' to handle the non-zero denominator check quickly *)
    rewrite Z.add_mod by lia;
    rewrite Z.mul_mod by lia;
    
    (* Replace (64^p mod 9) with 1 *)
    rewrite Hpow;
    
    (* Now the goal is just math with constants, e.g., ((2 * 1) + -2) mod 9 = 0 *)
    (* vm_compute calculates this instantly. *)
    vm_compute; reflexivity.
Qed.

(* -------------------------------------------------------------------------- *)
(* HELPER 2: Algebra for Divisibility by 9                                    *)
(* -------------------------------------------------------------------------- *)
Lemma numerator_div_9_generic : forall K beta c p,
  (beta * 64^p + c) mod 9 = 0 ->
  ((9 * K + beta) * 64^p + c) mod 9 = 0.
Proof.
  intros K beta c p H_consts.
  (* 1. Rearrange terms to isolate the multiple of 9 *)
  replace ((9 * K + beta) * 64^p + c)
     with (9 * (K * 64^p) + (beta * 64^p + c)) by ring.
  
  (* 2. Apply modulo distribution *)
  rewrite Z.add_mod by lia.
  rewrite H_consts.       (* Right side becomes 0 *)
  rewrite Z.add_0_r.      (* x + 0 = x *)
  rewrite Z.mod_mod by lia.
  
  (* 3. Handle the 9 * ... part *)
  (* We distribute the mod inside the multiplication *)
  rewrite Z.mul_mod by lia.
  
  (* 4. Calculate 9 mod 9 explicitly *)
  replace (9 mod 9) with 0 by reflexivity.
  
  (* 5. Finish: 0 * x = 0 *)
  rewrite Z.mul_0_l.
  reflexivity.
Qed.

(* -------------------------------------------------------------------------- *)
(* HELPER: Existence of k                                                     *)
(* We prove 64^p = 9*k + 1 exists, without defining k explicitly in the stmt  *)
(* -------------------------------------------------------------------------- *)
Lemma pow64_exists_k : forall p : Z, p >= 0 -> exists k, 64^p = 9 * k + 1.
Proof.
  intros p Hp.
  exists (64^p / 9). (* Provide the witness explicitly *)
  (* Now prove 64^p = 9 * (64^p / 9) + 1 *)
  rewrite (Z.div_mod (64^p) 9) at 1 by lia.
  assert (Hrem: (64^p) mod 9 = 1).
  { rewrite Z_pow_mod_compat by lia. 
    replace (64 mod 9) with 1 by reflexivity. 
    rewrite Z.pow_1_l by lia. reflexivity. }
  rewrite Hrem. reflexivity.
Qed.

Lemma Num_div_9_formula :
  forall m k : Z,
  let Num := (9 * m * 4 + 2) * (9 * k + 1) + -2 in
  (* Hfact is your algebraic factorization Num = 9 * E *)
  let E := 2 * (18 * m * k + 2 * m + k) in
  Num = 9 * E ->
  Num mod 9 = 0 ->
  Num / 9 = E.
Proof.
  intros m k Num E Hfact Hmod.
  assert (H9 : 9 <> 0) by lia.
  (* exactness lemma: Num = 9 * (Num/9) from mod=0 *)  
  assert (Hz : Num = 9 * (Num / 9)) by (apply Z_div_exact_full_2; assumption).
  (* compare with Num = 9*E *)
  assert (Heq9 : 9 * E = 9 * (Num / 9)).
  { rewrite <- Hfact. exact Hz. }
  apply (Z.mul_reg_l _ _ 9) in Heq9; [ | exact H9 ].
  symmetry; exact Heq9.
Qed.

Lemma div9_from_factor :
  forall Num E,
    Num = 9 * E ->
    Num mod 9 = 0 ->
    Num / 9 = E.
Proof.
  intros Num E Hfact _Hmod.   (* we don't actually need _Hmod *)
  subst Num.                  (* Num becomes 9 * E *)
  (* Now goal is (9 * E) / 9 = E *)
  replace (9 * E) with (E * 9) by lia.
  rewrite Z.div_mul; [reflexivity | lia].  (* 9 <> 0 *)
Qed.

(* -------------------------------------------------------------------------- *)
(* MAIN THEOREM: Row Correctness                                              *)
(* -------------------------------------------------------------------------- *)
Theorem row_correctness : forall (t : Token) (p m : Z),
  p >= 0 ->
  let params := get_params t in
  let x := construct_x t m in
  let xp := x_prime t p m in
  3 * xp + 1 = (pow2 (params.(alpha) + 6 * p)) * x.
Proof.
  intros.
  unfold x, xp, construct_x, x_prime, F_transform, get_input_reqs, get_params, pow2, pow64 in *.

  (* 1. ABSTRACT THE EXPONENT (The Break-Glass Fix) *)
  (* Destruct the lemma to get a fresh variable k. No recursions possible. *)
  destruct (pow64_exists_k p H) as [k Hk].
  
  (* 2. Replace 64^p with (9k+1) EVERYWHERE immediately *)
  rewrite Hk in *.

  (* 3. Simplify Parameters *)
  destruct t; cbv [alpha beta c delta get_params get_input_reqs params] in *.

  (* 4. Normalize Exponents *)
  (* Note: We replace the RHS 2^(a+6p) with 2^a * (9*k + 1) to match the LHS *)
  repeat rewrite Z.pow_add_r by lia.
  repeat rewrite Z.pow_mul_r by lia.
  change (2^6) with 64.
  rewrite Hk. (* Replace RHS 64^p too *)
  
  try change (2^1) with 2; try change (2^2) with 4; 
  try change (2^3) with 8; try change (2^4) with 16; 
  try change (2^5) with 32; try change (2^6) with 64.

  (* 5. Solve Goal by Goal using RING (No loops, no nia searches) *)

  (* Psi_0 *)
  - match goal with | [ |- context[?N / 9] ] => set (Num := N) end.
    assert (HNum_fact : Num = 9 * (2 * (18 * m * k + 2 * m + k))) by lia.
    (* 1. Show Num is divisible by 9 *)
    assert (Hdiv : Num mod 9 = 0).
    {
      (* Use the factorization Num = 9 * T *)
      rewrite HNum_fact.
      rewrite Z.mul_comm.
      apply Z.mod_mul.
      lia.  (* 9 <> 0 *)
    }
    (* 2. Get Num = 9 * (Num / 9) using the exactness lemma *)
    assert (Hz : Num = 9 * (Num / 9)).
    {
      apply Z_div_exact_2; try lia.  (* or Z_div_exact_full_2; try lia. *)      
    }
    pose (T := 2 * (18 * m * k + 2 * m + k)).
    assert (H9 : 9 * (Num / 9) = 9 * T).
    { rewrite <- Hz, HNum_fact; reflexivity. }
    assert (Hquot : Num / 9 = T).
    { apply (Z.mul_reg_l _ _ 9); try lia; exact H9. }
    subst T.
    rewrite Hquot.
    simpl (6 * 0)%Z.
    ring.    
    all: match goal with | [ |- context[?N / 9] ] => set (Num := N) end.
  (* Psi_1 *)
  - match goal with | [ |- context[?N / 9] ] => set (Num := N) end.
    (* 1. set E to the expression used in your factorization *)
    set (E := 2 * (18 * m * k + 2 * m + k)) in *.

    (* 2. You already have HNum_fact : Num = 9 * E *)
    assert (HNum_fact : Num = 9 * (144 * m * k + 56 * k + 16 * m + 6)).
    {
      unfold Num.
      (* compute 2^4 = 16 once and for all *)
      replace (2 ^ 4) with 16 by (compute; reflexivity).
      ring.  (* or lia if ring is not available but lia + unfolding should work *)
    }


    (* 3. Prove Num mod 9 = 0 from the factorization *)
    assert (Hmod9 : Num mod 9 = 0).
    {
      rewrite HNum_fact.
      (* (9 * E) mod 9 = 0 *)
      rewrite Z.mul_comm.
      apply Z.mod_mul.
      lia.   (* 9 <> 0 *)
    }

    (* We know: HNum_fact : Num = 9 * (144 * m * k + 56 * k + 16 * m + 6)
      and     Hmod9    : Num mod 9 = 0
    *)
    assert (Hdiv9 : Num / 9 = 144 * m * k + 56 * k + 16 * m + 6).
    { eapply div9_from_factor; [exact HNum_fact | exact Hmod9]. }

    (* Rewrite the goal using Hdiv9 *)
    rewrite Hdiv9.
    (* Right-hand side: use the relation 64^p = 9 * k + 1 *)
    replace (18 * m + 6 * 1 + 1) with (18 * m + 7) by ring.

    (* Rewrite 2^(4 + 6p) into 16 * 64^p, then use Hk *)
    rewrite Z.pow_add_r by lia.        (* 2^(4+6p) = 2^4 * 2^(6p) *)
    rewrite Z.pow_mul_r; try lia.      (* 2^(6p) = (2^6)^p = 64^p *)
    change (2 ^ 4) with 16.
    change (2 ^ 6) with 64.
    rewrite Hk.                        (* 64^p = 9 * k + 1 *)

    (* Now the goal is purely polynomial in m and k: *)
    (* 3 * (6 * (144*m*k + 56*k + 16*m + 6) + 1) + 1
      = 16 * (9 * k + 1) * (18 * m + 7)
    *)
    ring.
  (* Psi_2 *)
  - match goal with | [ |- context[?N / 9] ] => set (Num := N) end.
    (* inside the big match/case for alpha = 6, beta = 416, c = -2, delta = 1 *)

    assert (HNum_fact :
      Num = 9 * (576 * m * k + 416 * k + 64 * m + 46)).
    {
      unfold Num.
      (* Evaluate 2^6 = 64 so ring can see only linear/mult terms *)
      change (2 ^ 6)%Z with 64%Z.
      ring.
    }


    assert (Hmod9 : Num mod 9 = 0).
    {
      rewrite HNum_fact.
      rewrite Z.mul_mod; try lia.  (* (a*b) mod 9 = (a mod 9 * b mod 9) mod 9 *)
      rewrite Z.mod_same by lia.    (* 9 mod 9 = 0, since 9 <> 0 *)
      rewrite Z.mul_0_l.            (* 0 * ... = 0 *)
      rewrite Z.mod_0_l by lia.     (* 0 mod 9 = 0, since 9 <> 0 *)
      reflexivity.
    }

    assert (HNum_eq : Num = 9 * (Num / 9)).
    {
      assert (H9 : 9 <> 0) by lia.
      (* Z.div_mod : a = b * (a / b) + a mod b *)
      pose proof (Z.div_mod Num 9 H9) as Hmod.
      (* H : Num = 9 * (Num / 9) + Num mod 9 *)
      rewrite Hmod9 in Hmod.             (* Num mod 9 = 0 *)      
      rewrite Z.add_0_r in Hmod.         (* Num = 9 * (Num / 9) *)
      exact Hmod.
    }
    
    replace (3 * (6 * (Num / 9) + 1) + 1)
      with (18 * (Num / 9) + 4) by ring.
    
    assert (Hdiv9 : Num / 9 = 576 * m * k + 416 * k + 64 * m + 46).
    { apply div9_from_factor. exact HNum_fact. exact Hmod9. }

    rewrite Hdiv9.  (* get rid of the / 9 completely *)

    (* LHS becomes *)
    (* 3 * (6 * (576 * m * k + 416 * k + 64 * m + 46) + 1) + 1 *)

    set (E := 576 * m * k + 416 * k + 64 * m + 46).

    (* LHS simplifies to 18 * E + 4 *)
    replace (3 * (6 * E + 1) + 1) with (18 * E + 4) by ring.

    (* RHS: use 2^(6+6p) = 2^6 * (2^6)^p = 64 * 64^p, and Hk : 64^p = 9*k+1 *)
    rewrite Z.pow_add_r by lia.
    assert ( Hpow2: 2^6 = 64) by lia.    
    replace (2 ^ (6 * p)) with ((2 ^ 6) ^ p)
      by (symmetry; apply Z.pow_mul_r; lia).
    rewrite Hpow2.  
    unfold E.                (* Replace E by its explicit expression *)
    rewrite Hk.               (* Replace 64^p by (9*k + 1) *)
    change (6 * 2)%Z with 12. (* Optional; ring can also do this *)
    ring.
  (* psi_0 *)
  - match goal with | [ |- context[?N / 9] ] => set (Num := N) end.
    (* We are in the alpha = 4, beta = 8, c = -8, delta = 5 case, goal:
        3 * (6 * (Num / 9) + 5) + 1 = 2 ^ (4 + 6 * p) * (18 * m + 6 * 0 + 1)
    *)
    set (E := 144 * m * k + 16 * m + 8 * k) in *.

    (* 1. Factor Num = 9 * E *)
    assert (HNum_fact : Num = 9 * E).
    { subst Num E; ring. }

    (* 2. Show Num is divisible by 9 *)
    assert (Hmod9 : Num mod 9 = 0).
    { rewrite HNum_fact, Z.mul_comm, Z.mod_mul; lia. }

    (* 3. Use exact division lemma: Num = 9 * (Num / 9) *)
    assert (HNum_eq : Num = 9 * (Num / 9)).
    { apply Z_div_exact_full_2; [lia | exact Hmod9]. }

    (* 4. Deduce Num / 9 = E by cancellation *)
    assert (Hdiv9 : Num / 9 = E).
    {
      assert (Hz : 9 * E = 9 * (Num / 9)).
      { rewrite <- HNum_fact, HNum_eq. 
        apply Z_div_exact_full_2. 
        lia. 
        assert (H9 : 9 <> 0) by lia.
        rewrite Z.mul_comm.              (* (Num/9 * 9) mod 9 *)
        rewrite Z.mod_mul; [easy | exact H9].
      }
      rewrite HNum_fact.          (* goal becomes: (9 * E) / 9 = E *)
      replace (9 * E) with (E * 9) by lia.
      apply Z.div_mul.        (* from Coq.ZArith: a*b / b = a when b<>0 *)
      lia.                    (* proves 9 <> 0 *)
    }

    (* 5. Rewrite goal using E *)
    rewrite Hdiv9.
    (* 3 * (6 * (Num / 9) + 5) + 1  ->  3 * (6 * E + 5) + 1 *)    
    (* get rid of 6 * 0 *)
    replace (18 * m + 6 * 0 + 1) with (18 * m + 1) by ring.

    (* 6. Rewrite 2^(4 + 6p) using Hk : 64^p = 9*k + 1 *)
    assert (Hpow : 2 ^ (4 + 6 * p) = 2 ^ 4 * 2 ^ (6 * p)).
    { apply Z.pow_add_r; lia. }
    assert (Hpow2 : 2 ^ (6 * p) = (2 ^ 6) ^ p).
    { apply Z.pow_mul_r; lia. }
    rewrite Hpow, Hpow2.
    change (2 ^ 4) with 16.
    change (2 ^ 6) with 64.
    rewrite Hk.
    (* 7. Now everything is a polynomial identity *)
    unfold E.
    ring.

  (* psi_1 *)
  - match goal with | [ |- context[?N / 9] ] => set (Num := N) end.
    (* inside the eo1 / alpha=6, beta=224, c=-8, delta=5 case *)

    set (E := 576 * m * k + 224 * k + 64 * m + 24) in *.

    assert (HNum_fact : Num = 9 * E).
    {
      subst E.
      unfold Num.
      change (2 ^ 6) with 64.
      ring.
    }

    assert (Hmod9 : Num mod 9 = 0).
    {
      rewrite HNum_fact.
      rewrite Z.mul_comm.
      apply Z.mod_mul; lia.
    }

    assert (Hdiv9 : Num / 9 = E).
    {
      eapply div9_from_factor; [exact HNum_fact | exact Hmod9].
    }

    rewrite Hdiv9.
    (* Goal: 3 * (6 * E + 5) + 1 = 2 ^ (6 + 6 * p) * (18 * m + 7) *)

    replace (3 * (6 * E + 5) + 1) with (18 * E + 16) by ring.

    rewrite Z.pow_add_r by lia.
    change (2 ^ 6) with 64.
    assert (Hpow_mul : 2 ^ (6 * p) = (2 ^ 6) ^ p).
    { apply Z.pow_mul_r; lia. }
    rewrite Hpow_mul.
    change (2 ^ 6) with 64.
    rewrite <- Z.mul_assoc.
    rewrite Hk.   (* 64^p = 9*k + 1 *)

    subst E.
    ring.

  (* psi_2 *)
  - match goal with | [ |- context[?N / 9] ] => set (Num := N) end.
    
    set (E := 36 * m * k + 26 * k + 4 * m + 2) in *.

    assert (HNum_fact : Num = 9 * E).
    {
      subst Num E.
      replace (2 ^ 2) with 4 by (compute; reflexivity).
      ring.
    }

    assert (Hmod9 : Num mod 9 = 0).
    {
      rewrite HNum_fact.
      rewrite Z.mul_comm.
      apply Z.mod_mul; lia.
    }

    assert (Hdiv9 : Num / 9 = E).
    {
      eapply div9_from_factor; eauto.
    }

    rewrite Hdiv9.
    replace (3 * (6 * E + 5) + 1) with (18 * E + 16) by ring.

    assert (Hpow_add : 2 ^ (2 + 6 * p) = 2 ^ 2 * 2 ^ (6 * p))
      by (apply Z.pow_add_r; lia).
    rewrite Hpow_add; clear Hpow_add.
    replace (2 ^ 2) with 4 by (compute; reflexivity).

    assert (Hpow_mul : 2 ^ (6 * p) = (2 ^ 6) ^ p)
      by (apply Z.pow_mul_r; lia).
    rewrite Hpow_mul; clear Hpow_mul.
    replace (2 ^ 6) with 64 by (compute; reflexivity).
    rewrite Hk.
    replace (18 * m + 6 * 2 + 1) with (18 * m + 13) by ring.

    subst E.
    ring.

  (* omega_0 *)
  - match goal with | [ |- context[?N / 9] ] => set (Num := N) end.
    (* inside the relevant branch for alpha = 3, beta = 20, c = -2, delta = 1 *)

    (* 1. Choose E so that Num = 9 * E *)
    set (E := 72 * m * k + 20 * k + 8 * m + 2 : Z).

    (* Check the algebraic factorization of Num *)
    assert (HNum_fact : Num = 9 * E).
    { subst Num E.
      (* Num = (9*m*2^3 + 20)*(9*k + 1) - 2, and 2^3 = 8 *)
      change (2 ^ 3) with 8.
      ring. }

    (* 2. Num is divisible by 9, so Num mod 9 = 0 *)
    assert (Hmod9 : Num mod 9 = 0).
    { rewrite HNum_fact.
      rewrite Z.mul_comm.
      rewrite Z.mod_mul; lia. }

    (* 3. Use the generic lemma to get Num/9 = E *)
    assert (Hdiv9 : Num / 9 = E).
    { eapply div9_from_factor; eauto. }

    (* 4. Rewrite the goal in terms of E *)
    rewrite Hdiv9.
    (* LHS *)
    replace (3 * (6 * E + 1) + 1) with (18 * E + 4) by lia.

    (* 5. Rewrite the power-of-2 term as 8 * 64^p *)
    replace (2 ^ (3 + 6 * p)) with (8 * 64 ^ p).
    2:{
      rewrite Z.pow_add_r by lia.          (* 2^(3+6p) = 2^3 * 2^(6p) *)
      rewrite Z.pow_mul_r by lia.          (* 2^(6p) = (2^6)^p *)
      change (2 ^ 3) with 8.
      change (2 ^ 6) with 64.
      ring.
    }

    (* 6. Now the goal is: 18*E + 4 = 8 * 64^p * (18*m + 5) *)
    rewrite Hk.                             (* 64^p = 9*k + 1 *)

    (* 7. Expand E and finish with ring *)
    subst E.
    ring.

  (* omega_1 *)
  - match goal with | [ |- context[?N / 9] ] => set (Num := N) end.
    (* inside the appropriate subgoal *)    
    assert (HNum_fact : Num = 9 * (18 * m * k + 2 * m + 11 * k + 1)).
    { 
      unfold Num.
      replace (2 ^ 1) with 2 by lia.
      ring.
    }

    assert (Hmod9 : Num mod 9 = 0).
    { rewrite HNum_fact, Z.mul_comm, Z.mod_mul; lia. }

    (* for this branch *)
    set (E := 18 * m * k + 2 * m +  11 * k +  1 : Z).
    
    assert (Hdiv9 : Num / 9 = E).
    { eapply div9_from_factor; [exact HNum_fact | exact Hmod9]. }

    rewrite Hdiv9.
    unfold x.
    replace (18 * m + 6 * 1 + 5)%Z with (18 * m + 11)%Z by ring.
    rewrite Z.pow_add_r by lia.
    replace (2 ^ 1) with 2 by lia.

    (* replace 2^(6p) by 64^p *)
    replace (2 ^ (6 * p)) with (64 ^ p).
    2:{
      rewrite Z.pow_mul_r by lia.
      (* show 2^6 = 64 *)
      (* either by a separate lemma or direct computation: *)
      change 64 with (2 ^ 6)%Z; reflexivity.
    }

    rewrite Hk.  (* 64^p = 9 * k + 1 *)

    unfold E.
    (* LHS: 3 * (6 * E + 1) + 1  -> 18 * E + 4 *)
    replace (3 * (6 * (18 * m * k + 2 * m + 11 * k + 1) + 1) + 1)
      with (18 * (18 * m * k + 2 * m + 11 * k + 1) + 4) by ring.

    ring.

  (* omega_2 *)
  - match goal with | [ |- context[?N / 9] ] => set (Num := N) end.
    set (E := 288 * m * k + 272 * k + 32 * m + 30 : Z).
    assert (HNum_fact : Num = 9 * E).
    {
      unfold Num, E.
      replace (2 ^ 5) with 32 by lia.
      ring.
    }
    assert (Hmod9 : Num mod 9 = 0).
    {
      rewrite HNum_fact.
      rewrite Z.mul_comm.
      rewrite Z.mod_mul by lia.
      reflexivity.
    }

    assert (Hdiv9 : Num / 9 = E).
    {
      (* This uses your general lemma: *)
      eapply div9_from_factor; [exact HNum_fact | exact Hmod9].
    }
    rewrite Hdiv9.
    (* Goal becomes: 3 * (6 * E + 1) + 1 = 2 ^ (5 + 6 * p) * (18 * m + 17) *)
    unfold E.
    (* 2^(5 + 6p) = 2^5 * 2^(6p) *)
    rewrite Z.pow_add_r by lia.

    (* 2^(6p) = (2^6)^p = 64^p, since p >= 0 *)
    rewrite Z.pow_mul_r by lia.

    replace (2 ^ 5) with 32 by lia.
    replace (2 ^ 6) with 64 by lia.

    (* Now RHS = 32 * 64 ^ p * (18 * m + 17) *)
    rewrite Hk.  (* 64 ^ p = 9 * k + 1 *)
    unfold E.
    ring.

  (* Omega_0 *)
  - match goal with | [ |- context[?N / 9] ] => set (Num := N) end.
    (* Inside the corresponding branch *)

    (* 1. Expand, isolate Num/9 *)
    replace (18 * m + 6 * 0 + 5) with (18 * m + 5) by ring.
    replace (2 ^ (5 + 6 * p)) with (2 ^ 5 * 2 ^ (6 * p)) by (rewrite Z.pow_add_r; lia).

    (* So the goal becomes: *)
    (* 3 * (6 * (Num / 9) + 5) + 1 = 2 ^ 5 * 2 ^ (6 * p) * (18 * m + 5) *)

    (* 2. Factor Num as 9 * E *)
    set (E := 288 * m * k + 80 * k + 32 * m + 8) in *.
    assert (HNum_fact : Num = 9 * E).
    {
      unfold Num, E.
      (* Expand to get something like:
          (9*m*32 + 80)*(9*k + 1) - 8
        = 9*(32*18*m*k + 80*k + 10*m)
      *)
      replace (2 ^ 5) with 32 by lia.
      (*replace (32 * (18 * m * k) + 80 * k + 10 * m) with (E) by reflexivity.*)            
      ring.
    }
    (* 3. Num mod 9 = 0 *)
    assert (Hmod9 : Num mod 9 = 0).
    {
      rewrite HNum_fact.            (* Num mod 9 = (9 * E) mod 9 *)
      (* use Z.mod_mul: (a*b) mod b = 0 when b ≠ 0 *)
      rewrite Z.mul_comm.
      apply Z.mod_mul.
      lia.                          (* 9 <> 0 *)
    }

    (* 4. Use your general div9 lemma *)
    assert (Hdiv9 : Num / 9 = E).
    {
      eapply div9_from_factor; [exact HNum_fact | exact Hmod9].
    }

    (* 5. Rewrite Num/9 as E in the main goal *)
    rewrite Hdiv9.
    (* Now the goal is: *)
    (* 3 * (6 * E + 5) + 1 = 2 ^ 5 * 2 ^ (6 * p) * (18 * m + 5) *)

    (* 6. Use Hk to get 2^(6*p) = (64^p) = 9*k+1 *)    
    (* 2 ^ (6 * p) = 64 ^ p since 64 = 2^6; you can either: *)
    assert (Hpow64 : 64 = 2 ^ 6) by lia.
    rewrite Z.mul_comm in Hk.
    (* easier: use your earlier lemma: 2 ^ (6*p) = (2^6)^p = 64^p *)
    replace (2 ^ (6 * p)) with (64 ^ p).
    {
      lia.      
    }

    (* Now right-hand side is: 2^5 * (9*k + 1) * (18*m + 5) *)

    (* 7. Final pure algebra step *)
    assert (H2pow: 64 ^ p = 2 ^ (6 * p)).
    { rewrite  (Z.pow_mul_r 2 6 p). rewrite Hpow64. reflexivity. lia. lia. }    
    rewrite H2pow.
    reflexivity.

  (* Omega_1 *)
  - match goal with | [ |- context[?N / 9] ] => set (Num := N) end.
    set (E := 72 * m * k + 44 * k + 8 * m + 4) in *.

    assert (HNum_fact : Num = 9 * E).
    { subst E Num. replace (2 ^ 3) with 8 by lia. ring. }

    assert (Hmod9 : Num mod 9 = 0).
    { rewrite HNum_fact.
      rewrite Z.mul_comm.
      apply Z.mod_mul; lia.
    }

    assert (Hdiv9 : Num / 9 = E).
    { eapply div9_from_factor; [exact HNum_fact | exact Hmod9]. }

    rewrite Hdiv9.
    simpl x.
    replace (3 * (6 * E + 5) + 1) with (18 * E + 16) by ring.

    replace (2 ^ (3 + 6 * p)) with (8 * 64 ^ p).
    2: {
      rewrite Z.pow_add_r by lia.
      rewrite Z.pow_mul_r by lia.
      replace (2 ^ 3) with 8 by lia.
      replace (2 ^ 6) with 64 by lia.
      ring.
    }

    rewrite Hk.
    unfold E.
    ring.

  (* Omega_2 *)
  - match goal with | [ |- context[?N / 9] ] => set (Num := N) end.
    set (E := 18 * m * k + 2 * m + 17 * k + 1 : Z).

    assert (HNum_fact : Num = 9 * E).
    { subst E; unfold Num; replace (2 ^ 1) with 2 by lia; ring. }

    assert (Hmod9 : Num mod 9 = 0).
    { rewrite HNum_fact.
      rewrite Z.mul_comm.
      rewrite Z.mod_mul; lia. }

    assert (Hdiv9 : Num / 9 = E).
    { eapply div9_from_factor; [exact HNum_fact | exact Hmod9]. }

    rewrite Hdiv9.

    (* Now goal: 3 * (6 * E + 5) + 1 = 2 ^ (1 + 6 * p) * (18 * m + 17).
      Use 2^1 = 2 and 2^(1+6p) = 2 * 64^p and Hk. *)
    replace (2 ^ (1 + 6 * p)) with (2 * 64 ^ p).
    2: {
      rewrite Z.pow_add_r by lia.
      rewrite Z.pow_mul_r by lia.
      replace (2 ^ 1) with 2 by lia.
      replace (2 ^ 6) with 64 by lia.
      ring.
    }
    
    rewrite Hk.
    unfold E.
    replace (6 * 2 + 5) with 17 by lia.
    ring.
Qed.

(* ========================================================================== *)
(* PART D: SECTION 4 - CRT TAG CALCULUS AND DRIFT                             *)
(* ========================================================================== *)

(* 1. The Tag Definition: t(x) = (x-1)/2 *)
Definition tag (x : Z) : Z := (x - 1) / 2.

(* 2. The Coarse Index r = floor(x/6) *)
(* Derived from input x = 18m + 6j + p6 -> r = 3m + j *)
Definition calc_r (t : Token) (m : Z) : Z :=
  let (j, _) := get_input_reqs t in
  3 * m + j.

(* 3. The Slope K = (2^(alpha+6p) - 3) * 4^p *)
(*Definition calc_K (t : Token) (p : Z) : Z :=
  let params := get_params t in
  (pow2 (params.(alpha) + 6 * p) - 3) * pow4 p.*)

Definition calc_K (t : Token) (p : Z) : Z :=
  pow2 (alpha (get_params t) + 6 * p) - 3.

(* 4. The Geometric Accumulator q_p = (4^p - 1) / 3 *)
Definition calc_q_p (p : Z) : Z :=
  (pow64 p - 1) / 3.


(* 5. The Drift Offset Delta_epsilon *)
(* Family e uses 2*q_p, Family o uses 5*q_p - 1 *)
(*Definition delta_drift (t : Token) (p : Z) : Z :=
  let q := calc_q_p p in
  match t with
  | Psi_0 | Psi_1 | Psi_2 | psi_0 | psi_1 | psi_2 => 
      2 * q (* Family e *)
  | omega_0 | omega_1 | omega_2 | Omega_0 | Omega_1 | Omega_2 => 
      5 * q - 1 (* Family o *)
  end.*)

Definition delta_drift (t : Token) (p : Z) : Z :=
  let q := calc_q_p p in
  match t with
  | Psi_0   => 2 * q
  | Psi_1   => 8 * q + 2
  | Psi_2   => 32 * q + 10

  | psi_0   => 8 * q + 2
  | psi_1   => 32 * q + 10
  | psi_2   => 2 * q

  | omega_0 => 20 * q + 4
  | omega_1 => 5 * q - 1
  | omega_2 => 80 * q + 24

  | Omega_0 => 80 * q + 24
  | Omega_1 => 20 * q + 4
  | Omega_2 => 5 * q - 1
  end.




(* 6. The Predicted Drift Formula: d = r*K + Delta *)
Definition predicted_drift (t : Token) (p m : Z) : Z :=
  let r := calc_r t m in
  (r * (calc_K t p)) + (delta_drift t p).

(* -------------------------------------------------------------------------- *)
(* PART E: PROOFS FOR SECTION 4                                               *)
(* -------------------------------------------------------------------------- *)

(* Helper: Prove 4^p = 1 mod 3 (needed for q_p exactness) *)
Lemma pow4_mod_3 : forall p, p >= 0 -> (4 ^ p) mod 3 = 1.
Proof.
  intros.
  assert (4 mod 3 = 1) by reflexivity.
  rewrite Z_pow_mod_compat by lia.
  rewrite H0. rewrite Z.pow_1_l by lia. reflexivity.
Qed.

(* Step 2: use Z.cong_iff_0 to get (4^p - 1) mod 3 = 0 *)
Lemma four_pow_minus1_multiple_of_3 :
  forall p : Z,  p >= 0 -> (4 ^ p - 1) mod 3 = 0.
Proof.
  intros p Hp.
  (* Z.cong_iff_0: a mod m = b mod m <-> (a - b) mod m = 0 *)
  apply (proj1 (Z.cong_iff_0 (4 ^ p) 1 3)).
  (* it suffices to prove 4^p mod 3 = 1 mod 3 *)
  rewrite pow4_mod_3 by exact Hp.
  replace (1 mod 3) with 1 by (apply (Z.mod_small 1 3); lia).
  reflexivity.
Qed.

(*replace ((pow4 p - 1) / 3 * 3) with (3 * ((pow4 p - 1) / 3)) by lia.*)


(* Helper: q_p is an exact integer division *)
Lemma q_p_exact : forall p, p >= 0 -> (pow4 p - 1) / 3 * 3 = pow4 p - 1.
Proof.
  intros p Hp.
  symmetry.
  replace ((pow4 p - 1) / 3 * 3) with (3 * ((pow4 p - 1) / 3)) by lia.
  apply Z.div_exact.
  - lia.
  - unfold pow4.
    (* Prove (4^p - 1) mod 3 = 0 *)
    apply four_pow_minus1_multiple_of_3; assumption.    
Qed.

Lemma tag_diff_scaled (xp x : Z) :
  2 * tag xp = xp - 1 ->
  2 * tag x  = x  - 1 ->
  2 * (tag xp - tag x) = xp - x.
Proof.
  intros Hxp Hx.
  (* Expand the LHS: 2 * tag xp - 2 * tag x *)
  rewrite Z.mul_sub_distr_l.
  rewrite Hxp, Hx.
  ring.
Qed.


Lemma drift_equation_ee0_core :
  forall (p m : Z),
    p >= 0 ->
    let x  := construct_x Psi_0 m in
    let xp := x_prime Psi_0 p m in
    (* CORRECTION: The drift formula must use 64^p to match x_prime *)
    let K_corr := (pow2 (2 + 6 * p) - 3) in
    let q_corr := (pow64 p - 1) / 3 in
    let drift_corr := (calc_r Psi_0 m) * K_corr + 2 * q_corr in
    
    tag xp - tag x = drift_corr.
Proof.
  intros p m Hp x xp K_corr q_corr drift_corr.
  
  (* 1. Unfold Definitions *)
  unfold x, xp, construct_x, x_prime, F_transform, tag,
         get_input_reqs, get_params, calc_r,
         pow2, pow64 in *.
  
  (* 2. Specialise to Psi_0 (alpha=2, beta=2, c=-2, delta=1, j=0, p6=1) *)
  cbv [alpha beta c delta get_params get_input_reqs] in *.

  (* Now:
       x  = 18*m + 1
       xp = 6 * (((9*m*4 + 2) * 64^p - 2) / 9) + 1
       K_corr = 2^(2 + 6*p) - 3
       q_corr = (64^p - 1) / 3
       calc_r Psi_0 m = 3*m
  *)

  (* 3. Show tag x = 9*m *)
  assert (Hx_val: x = 18 * m + 1) by lia.
  replace (tag x) with (9 * m).
  2: {
    unfold tag. rewrite Hx_val.
    replace (18 * m + 1 - 1) with (2 * (9 * m)) by ring.
    replace (2 * (9 * m)) with (9 * m * 2) by lia.
    rewrite Z.div_mul by lia. reflexivity.
  }

  (* 4. Reduce goal: tag xp - 9*m = drift_corr *)
  (* Work with the doubled version to avoid /2 *)
  unfold tag.

  replace (6 * (((9 * m * 2 ^ 2 + 2) * 64 ^ p + -2) / 9) + 1 - 1)
    with (6 * (((9 * m * 2 ^ 2 + 2) * 64 ^ p + -2) / 9)) by ring.

  replace (18 * m + 6 * 0 + 1 - 1)
    with (18 * m) by ring.
  
  replace (6 * (((9 * m * 2 ^ 2 + 2) * 64 ^ p + -2) / 9))
    with (2 * (3 * (((9 * m * 2 ^ 2 + 2) * 64 ^ p + -2) / 9))) by ring.
  set (T := 3 * (((9 * m * 2 ^ 2 + 2) * 64 ^ p + -2) / 9)) in *.

  replace (2 * T) with (T * 2) by ring.
  (* Now the subterm is (T * 2) / 2 *)

  rewrite Z.div_mul by lia.
  (* (T * 2) / 2 becomes T *)

  (* (2 * (3 * (...)/9)) / 2 = 3 * (((9 * m * 2 ^ 2 + 2) * 64 ^ p + -2) / 9) *)
  replace (18 * m) with (2 * (9 * m)) by ring.
  replace (2 * (9 * m)) with (9 * m * 2) by ring.
  rewrite Z.div_mul by lia.
  (* (18 * m) / 2 = 9 * m *)

  unfold T.

  (* simplify 2^2 to 4 so it matches 9*m*4 *)
  replace (2 ^ 2) with 4 in * by (compute; reflexivity).

  set (Num := (9 * m * 4 + 2) * 64 ^ p + -2).
  (* Now T = 3 * (Num / 9), so the goal is: *)
  change (3 * (Num / 9) - 9 * m = drift_corr).

  (* pow64_decomp : forall p, p >= 0 -> 64 ^ p = 9 * (64 ^ p / 9) + 1 *)

  pose proof (pow64_decomp p Hp) as Hk.
  set (k := 64 ^ p / 9) in Hk.
  (* Now Hk : 64 ^ p = 9 * k + 1 *)

  set (E := 2 * (18 * m * k + 2 * m + k)).

  assert (HNum : Num = 9 * E).
  {
    unfold Num, E.
    rewrite Hk.
    ring.
  }

  assert (HNum_div9 : Num / 9 = E).
  {
    rewrite HNum.
    (* (9 * E) / 9 = E *)
    replace (9 * E) with (E * 9) by ring.
    rewrite Z.div_mul by lia.
    reflexivity.
  }

  rewrite HNum_div9.
  (* Goal now: 3 * E - 9 * m = drift_corr *)

  unfold drift_corr, K_corr, q_corr.
  replace (3 * m + 0) with (3 * m) by ring.

  (* Now goal: 3 * E - 9 * m
        = 3 * m * (2 ^ (2 + 6 * p) - 3) + 2 * ((64 ^ p - 1) / 3) *)

  assert (Hq_val : (64 ^ p - 1) / 3 = 3 * k).
  {
    rewrite Hk.
    replace (9 * k + 1 - 1) with (9 * k) by ring.
    replace (9 * k) with (3 * k * 3) by ring.
    rewrite Z.div_mul by lia.
    reflexivity.
  }
  rewrite Hq_val.
  replace (2 * (3 * k)) with (6 * k) by ring.
  (* RHS becomes: 3 * m * (2 ^ (2 + 6 * p) - 3) + 6 * k *)

  unfold E.
  (* LHS is now 3 * (2 * (18 * m * k + 2 * m + k)) - 9 * m *)

  (* Rewrite 2^(2+6p) = 4 * 64^p *)
  repeat rewrite Z.pow_add_r by lia.
  change (2 ^ 2) with 4.
  replace (2 ^ (6 * p)) with (64 ^ p).
    2:{     
      rewrite (Z.pow_mul_r 2 6 p) by lia.
      change (2 ^ 6) with 64.
      reflexivity.
    }
  rewrite Hk.
  ring.
Qed.

Lemma drift_equation_ee0 :
  forall (p m : Z),
    p >= 0 ->
    let x  := construct_x Psi_0 m in
    let xp := x_prime Psi_0 p m in
    
    (* Correct Drift Parameters for Psi_0 *)
    let A     := 2 + 6 * p in
    let K     := pow2 A - 3 in
    let q_p   := (pow64 p - 1) / 3 in
    let Delta := 2 * q_p in
    let r     := calc_r Psi_0 m in
    let predicted := r * K + Delta in
    
    tag xp - tag x = predicted.
Proof.
  intros p m Hp x xp A K q_p Delta r predicted.
  (* Replace the pretty names with their definitions *)
  subst A K q_p Delta r predicted.
  (* Now the goal is exactly the statement of drift_equation_ee0_core *)
  apply drift_equation_ee0_core; assumption.
Qed.

(* ========================================================================== *)
(* DRIFT EQUATION LEMMAS FOR ALL 12 TOKENS                                    *)
(* ========================================================================== *)

(* Prerequisites assumed to be in context:
   - Definitions: construct_x, x_prime, tag, F_transform, etc.
   - Helpers: pow64_exists_k, pow2, pow64
   - Variable p, m : Z and Hp : p >= 0
*)

(* -------------------------------------------------------------------------- *)
(* Family e (Type ee) *)
(* -------------------------------------------------------------------------- *)

Lemma drift_equation_Psi_0 :
  forall (p m : Z),
    p >= 0 ->
    let x  := construct_x Psi_0 m in
    let xp := x_prime Psi_0 p m in
    (* CORRECTION: The drift formula must use 64^p to match x_prime *)
    let K_corr := (pow2 (2 + 6 * p) - 3) in
    let q_corr := (pow64 p - 1) / 3 in
    let drift_corr := (calc_r Psi_0 m) * K_corr + 2 * q_corr in
    
    tag xp - tag x = drift_corr.
Proof.
  intros p m Hp x xp K_corr q_corr drift_corr.
  
  (* 1. Unfold Definitions *)
  unfold x, xp, construct_x, x_prime, F_transform, tag,
         get_input_reqs, get_params, calc_r,
         pow2, pow64 in *.
  
  (* 2. Specialise to Psi_0 (alpha=2, beta=2, c=-2, delta=1, j=0, p6=1) *)
  cbv [alpha beta c delta get_params get_input_reqs] in *.

  (* Now:
       x  = 18*m + 1
       xp = 6 * (((9*m*4 + 2) * 64^p - 2) / 9) + 1
       K_corr = 2^(2 + 6*p) - 3
       q_corr = (64^p - 1) / 3
       calc_r Psi_0 m = 3*m
  *)

  (* 3. Show tag x = 9*m *)
  assert (Hx_val: x = 18 * m + 1) by lia.
  replace (tag x) with (9 * m).
  2: {
    unfold tag. rewrite Hx_val.
    replace (18 * m + 1 - 1) with (2 * (9 * m)) by ring.
    replace (2 * (9 * m)) with (9 * m * 2) by lia.
    rewrite Z.div_mul by lia. reflexivity.
  }

  (* 4. Reduce goal: tag xp - 9*m = drift_corr *)
  (* Work with the doubled version to avoid /2 *)
  unfold tag.

  replace (6 * (((9 * m * 2 ^ 2 + 2) * 64 ^ p + -2) / 9) + 1 - 1)
    with (6 * (((9 * m * 2 ^ 2 + 2) * 64 ^ p + -2) / 9)) by ring.

  replace (18 * m + 6 * 0 + 1 - 1)
    with (18 * m) by ring.
  
  replace (6 * (((9 * m * 2 ^ 2 + 2) * 64 ^ p + -2) / 9))
    with (2 * (3 * (((9 * m * 2 ^ 2 + 2) * 64 ^ p + -2) / 9))) by ring.
  set (T := 3 * (((9 * m * 2 ^ 2 + 2) * 64 ^ p + -2) / 9)) in *.

  replace (2 * T) with (T * 2) by ring.
  (* Now the subterm is (T * 2) / 2 *)

  rewrite Z.div_mul by lia.
  (* (T * 2) / 2 becomes T *)

  (* (2 * (3 * (...)/9)) / 2 = 3 * (((9 * m * 2 ^ 2 + 2) * 64 ^ p + -2) / 9) *)
  replace (18 * m) with (2 * (9 * m)) by ring.
  replace (2 * (9 * m)) with (9 * m * 2) by ring.
  rewrite Z.div_mul by lia.
  (* (18 * m) / 2 = 9 * m *)

  unfold T.

  (* simplify 2^2 to 4 so it matches 9*m*4 *)
  replace (2 ^ 2) with 4 in * by (compute; reflexivity).

  set (Num := (9 * m * 4 + 2) * 64 ^ p + -2).
  (* Now T = 3 * (Num / 9), so the goal is: *)
  change (3 * (Num / 9) - 9 * m = drift_corr).

  (* pow64_decomp : forall p, p >= 0 -> 64 ^ p = 9 * (64 ^ p / 9) + 1 *)

  pose proof (pow64_decomp p Hp) as Hk.
  set (k := 64 ^ p / 9) in Hk.
  (* Now Hk : 64 ^ p = 9 * k + 1 *)

  set (E := 2 * (18 * m * k + 2 * m + k)).

  assert (HNum : Num = 9 * E).
  {
    unfold Num, E.
    rewrite Hk.
    ring.
  }

  assert (HNum_div9 : Num / 9 = E).
  {
    rewrite HNum.
    (* (9 * E) / 9 = E *)
    replace (9 * E) with (E * 9) by ring.
    rewrite Z.div_mul by lia.
    reflexivity.
  }

  rewrite HNum_div9.
  (* Goal now: 3 * E - 9 * m = drift_corr *)

  unfold drift_corr, K_corr, q_corr.
  replace (3 * m + 0) with (3 * m) by ring.

  (* Now goal: 3 * E - 9 * m
        = 3 * m * (2 ^ (2 + 6 * p) - 3) + 2 * ((64 ^ p - 1) / 3) *)

  assert (Hq_val : (64 ^ p - 1) / 3 = 3 * k).
  {
    rewrite Hk.
    replace (9 * k + 1 - 1) with (9 * k) by ring.
    replace (9 * k) with (3 * k * 3) by ring.
    rewrite Z.div_mul by lia.
    reflexivity.
  }
  rewrite Hq_val.
  replace (2 * (3 * k)) with (6 * k) by ring.
  (* RHS becomes: 3 * m * (2 ^ (2 + 6 * p) - 3) + 6 * k *)

  unfold E.
  (* LHS is now 3 * (2 * (18 * m * k + 2 * m + k)) - 9 * m *)

  (* Rewrite 2^(2+6p) = 4 * 64^p *)
  repeat rewrite Z.pow_add_r by lia.
  change (2 ^ 2) with 4.
  replace (2 ^ (6 * p)) with (64 ^ p).
    2:{     
      rewrite (Z.pow_mul_r 2 6 p) by lia.
      change (2 ^ 6) with 64.
      reflexivity.
    }
  rewrite Hk.
  ring.
Qed.

Lemma drift_equation_Psi_1 :
  forall (p m : Z),
    p >= 0 ->
    let x  := construct_x Psi_1 m in
    let xp := x_prime Psi_1 p m in
    (* Psi_1: alpha = 4 *)
    let K     := pow2 (4 + 6 * p) - 3 in
    let q_p   := (pow64 p - 1) / 3 in
    (* corrected offset *)
    let Delta := 8 * q_p + 2 in
    let predicted := (calc_r Psi_1 m) * K + Delta in
    tag xp - tag x = predicted.
Proof.
  intros p m Hp x xp K q_p Delta predicted.
  unfold x, xp, construct_x, x_prime, F_transform, tag,
        get_input_reqs, get_params, calc_r, pow2, pow64 in *.
  cbv [alpha beta c delta get_params get_input_reqs] in *.
  
  destruct (pow64_exists_k p Hp) as [k Hk].
  assert (Hq: (64 ^ p - 1) / 3 = 3 * k).
  { rewrite Hk. replace (9 * k + 1 - 1) with (3 * (3 * k)) by ring. 
    replace (3 * (3 * k)) with (3 * k * 3) by ring.
    rewrite Z.div_mul by lia. reflexivity. }

  assert (Hqp : q_p = 3 * k).
  {
    (* unfold q_p so Coq sees (pow64 p - 1)/3 *)
    unfold q_p in *.
    (* unfold pow64 so Coq sees 64^p *)
    unfold pow64 in *.
    (* now q_p is definitionally (64 ^ p - 1) / 3, and Hq is exactly that: *)
    exact Hq.
  }
  (* now Hqp is the equality you really want to use *)
  unfold predicted, Delta.
  rewrite Hqp.  

  (* get rid of the /2 on the left side *)

  replace (6 * (((9 * m * 2 ^ 4 + 56) * 64 ^ p + -2) / 9) + 1 - 1)
    with (2 * (3 * (((9 * m * 2 ^ 4 + 56) * 64 ^ p + -2) / 9))) by ring.

  replace (18 * m + 6 * 1 + 1 - 1)
    with (2 * (9 * m + 3)) by ring.

  (* 1. Re-associate the numerators so they look like (something * 2) / 2 *)

  replace (2 * (3 * (((9 * m * 2 ^ 4 + 56) * 64 ^ p + -2) / 9)))
    with ((3 * (((9 * m * 2 ^ 4 + 56) * 64 ^ p + -2) / 9)) * 2)
    by ring.

  replace (2 * (9 * m + 3))
    with ((9 * m + 3) * 2)
    by ring.

  (* Goal is now:
    (3 * (((...) / 9)) * 2) / 2 - ((9*m+3) * 2) / 2 = ...
  *)

  (* 2. Now Z.div_mul sees (a * 2) / 2 *)

  rewrite Z.div_mul by lia.
  rewrite Z.div_mul by lia.

  (* Goal simplifies to:
    3 * (((9 * m * 2 ^ 4 + 56) * 64 ^ p + -2) / 9) - (9 * m + 3)
      = (3 * m + 1) * K + 2 * (3 * k)
  *)

    set (Num := (9 * m * 2 ^ 4 + 56) * 64 ^ p + -2).
    change (((9 * m * 2 ^ 4 + 56) * 64 ^ p + -2) / 9) with (Num / 9).

  (* Now goal is: *)
  (* 3 * (Num / 9) - (9 * m + 3) = (3 * m + 1) * K + 2 * (3 * k). *)
  (* Choose an E so that Num = 9 * E *)
  set (E := 16 * m * (9 * k + 1) + 56 * k + 6).

  assert (HNum : Num = 9 * E).
  {
    unfold Num, E.
    rewrite Hk.        (* 64^p = 9*k + 1 *)
    ring.
  }

  assert (HNum_div9 : Num / 9 = E).
  {
    rewrite HNum.
    replace (9 * E) with (E * 9) by ring.
    rewrite Z.div_mul by lia.
    reflexivity.
  }

  rewrite HNum_div9.
  (* Goal is now: *)
  (* 3 * E - (9 * m + 3) = (3 * m + 1) * K + 6 * k *)
  unfold K.
  (* K = 2 ^ (4 + 6 * p) - 3 *)

  repeat rewrite Z.pow_add_r by lia.
  (* 2^(4+6p) = 2^4 * 2^(6p) *)

  change (2 ^ 4) with 16.

  (* Turn 2^(6p) into 64^p *)
  replace (2 ^ (6 * p)) with (64 ^ p).
  2:{
    rewrite (Z.pow_mul_r 2 6 p) by lia.  (* 2^(6p) = (2^6)^p *)
    change (2 ^ 6) with 64.
    reflexivity.
  }
  (* Now use 64^p = 9*k + 1 *)
  rewrite Hk.
  (* RHS is now a polynomial in m and k, with 16 * (9*k+1) coming from 2^(4+6p) *)
  set (D :=
    3 * E - (9 * m + 3)
    - ((3 * m + 1) * (16 * (9 * k + 1) - 3) + 6 * k)).
  ring_simplify D.
  (* You should see D = 18 * k + 2 *)
  lia.
Qed.

Lemma drift_equation_Psi_2 :
  forall (p m : Z),
    p >= 0 ->
    let x  := construct_x Psi_2 m in
    let xp := x_prime Psi_2 p m in
    (* Psi_2: alpha=6 *)
    let K     := pow2 (6 + 6 * p) - 3 in
    let q_p   := (pow64 p - 1) / 3 in
    (* corrected offset *)
    let Delta := 32 * q_p + 10 in
    let predicted := (calc_r Psi_2 m) * K + Delta in    
    tag xp - tag x = predicted.
Proof.
  intros p m Hp x xp K q_p Delta predicted.
  unfold x, xp, construct_x, x_prime, F_transform, tag,
         get_input_reqs, get_params, calc_r,
         pow2, pow64, K, q_p, Delta, predicted in *.
  cbv [alpha beta c delta get_params get_input_reqs ] in *.
  
  destruct (pow64_exists_k p Hp) as [k Hk].
  assert (Hq: (64 ^ p - 1) / 3 = 3 * k).
  { rewrite Hk. replace (9 * k + 1 - 1) with (3 * (3 * k)) by ring. 
    replace (3 * (3 * k)) with (3 * k * 3) by ring.
    rewrite Z.div_mul by lia. reflexivity. }
  
  assert (Hqp : ((64 ^ p - 1) / 3) = 3 * k) by exact Hq.

  (* 2. Turn tag xp - tag x into a drift equation in terms of Num/9 *)
  set (Num := (9 * m * 2 ^ 6 + 416) * 64 ^ p + -2) in *.
  (* Now xp = 6 * (Num / 9) + 1, x = 18*m + 12 + 1 *)

  (* Remove the /2 in tags, as in the Psi_0 and Psi_1 proofs *)
  unfold tag.
  replace (6 * (Num / 9) + 1 - 1) with (6 * (Num / 9)) by ring.
  replace (18 * m + 12 + 1 - 1) with (18 * m + 12) by ring.

  (* Write both numerators as 2 * (...) so we can cancel /2 *)
  replace (6 * (Num / 9)) with (2 * (3 * (Num / 9))) by ring.
  replace (18 * m + 12) with (2 * (9 * m + 6)) by ring.

  (* Multiply both sides by 2 and cancel the /2’s *)
  apply Z.mul_reg_l with (p := 2); [lia |].
  rewrite Z.mul_sub_distr_l.

  (* starting from your goal with the big outer 2s *)
  replace (2 * (2 * (3 * (Num / 9)) / 2) -
          2 * ((18 * m + 6 * 2 + 1 - 1) / 2))
    with (2 * ((2 * (3 * (Num / 9)) / 2) -
              ((18 * m + 6 * 2 + 1 - 1) / 2))) by ring.
  apply Z.mul_reg_l with (p := 2); [lia |].

  (* now: (2 * (3*(Num/9)) / 2) - ((18*m + 6*2 + 1 - 1) / 2) = ... *)

  replace (18 * m + 6 * 2 + 1 - 1) with ((9 * m + 6) * 2) by ring.

  (* optionally: *)
  replace (2 * (3 * (Num / 9))) with ((3 * (Num / 9)) * 2) by ring.

  rewrite Z.div_mul by lia.
  rewrite Z.div_mul by lia.
  (* Cancel the first factor 2 *)
  apply Z.mul_reg_l with (p := 2); [lia |].
  (* Goal: 2 * (3 * (Num / 9) - (9 * m + 6))
          = 2 * (calc_r Psi_2 m * K + Delta) *)

  (* Cancel the second factor 2 *)
  apply Z.mul_reg_l with (p := 2); [lia |].
  replace (2 * (2 * (2 * (2 * (3 * (Num / 9) - (9 * m + 6))))))
    with (16 * (3 * (Num / 9) - (9 * m + 6))) by ring.

  replace (2 * (2 * (2 * (2 * (calc_r Psi_2 m * K + Delta)))))
    with (16 * (calc_r Psi_2 m * K + Delta)) by ring.
  
  assert (Hsimple :
    3 * (Num / 9) - (9 * m + 6) = calc_r Psi_2 m * K + Delta).
  {
    
    (* We want: 3 * (Num / 9) - (9 * m + 6)
                = calc_r Psi_2 m * K + Delta *)

    (* 1. Use calc_r Psi_2 m = 3*m + 2 *)
    cbv [calc_r] in *.

    (* 2. Rewrite Delta using Hq / Hqp: q_p = 3*k, so Delta = 32*q_p + 10 = 96*k + 10 *)
    unfold Delta, q_p, pow64 in *.
    rewrite Hq in *.
    (* Now Delta is 32 * (3 * k) + 10 = 96*k + 10 *)

    (* 3. Express Num as 9 * E, so Num/9 = E *)

    set (E := 64 * m * (9 * k + 1) + 416 * k + 46).

    assert (HNum : Num = 9 * E).
    {
      unfold Num, E.
      replace (2 ^ 6) with 64 by (compute; reflexivity).
      rewrite Hk.  (* 64^p = 9*k + 1 *)
      ring.
    }

    assert (HNum_div9 : Num / 9 = E).
    {
      rewrite HNum.
      replace (9 * E) with (E * 9) by ring.
      rewrite Z.div_mul by lia.
      reflexivity.
    }

    rewrite HNum_div9.
    (* Goal is now:
        3 * E - (9 * m + 6)
          = (3 * m + 2) * K + 96 * k + 10 *)

    (* 4. Rewrite K using Hk: 2^(6+6p) - 3 = (2^6 * 2^(6p)) - 3 = 64 * 64^p - 3 *)

    unfold K.
    repeat rewrite Z.pow_add_r by lia.
    change (2 ^ 6) with 64.

    replace (2 ^ (6 * p)) with (64 ^ p).
    2:{
      rewrite Z.pow_mul_r by lia.
      change (2 ^ 6) with 64.
      reflexivity.
    }

    rewrite Hk.  (* 64^p = 9 * k + 1 *)

    unfold E.
    cbv [get_input_reqs] in *.    

    (* At this point both sides are just polynomials in m and k. *)
    lia.   (* or: ring. *)
  }

  rewrite Hsimple.
  (* Goal becomes: 16 * (calc_r Psi_2 m * K + Delta)
                  = 16 * (calc_r Psi_2 m * K + Delta) *)
  reflexivity.
Qed.

(* -------------------------------------------------------------------------- *)
(* Family e -> o (Type eo) *)
(* -------------------------------------------------------------------------- *)

Lemma drift_equation_psi_0 :
  forall (p m : Z),
    p >= 0 ->
    let x  := construct_x psi_0 m in
    let xp := x_prime psi_0 p m in
    (* psi_0: alpha=4, o-family, corrected Delta *)
    let K     := pow2 (4 + 6 * p) - 3 in
    let q_p   := (pow64 p - 1) / 3 in
    let Delta := 8 * q_p + 2 in
    let predicted := (calc_r psi_0 m) * K + Delta in    
    tag xp - tag x = predicted.
Proof.
  intros p m Hp x xp K q_p Delta predicted.
  unfold x, xp, construct_x, x_prime, F_transform, tag,
         get_input_reqs, get_params, calc_r,
         pow2, pow64, K, q_p, Delta, predicted in *.
  cbv [alpha beta c delta get_params get_input_reqs ] in *.
  
  destruct (pow64_exists_k p Hp) as [k Hk].
  assert (Hq: (64 ^ p - 1) / 3 = 3 * k).
  { rewrite Hk. replace (9 * k + 1 - 1) with (3 * (3 * k)) by ring. 
    replace (3 * (3 * k)) with (3 * k * 3) by ring.
    rewrite Z.div_mul by lia. reflexivity. }
  
  assert (Hqp : ((64 ^ p - 1) / 3) = 3 * k) by exact Hq.
  (* 2. Name the big numerator *)
  set (Num := (9 * m * 2 ^ 4 + 8) * 64 ^ p + -8) in *.

  unfold tag.

  (* Recognize the tag expressions in terms of x and xp *)
  change ((6 * (((9 * m * 2 ^ 4 + 8) * 64 ^ p + -8) / 9) + 5 - 1) / 2)
    with ((xp - 1) / 2).
  change ((18 * m + 1 - 1) / 2)
    with ((x - 1) / 2).

  (* Replace numerators, not the whole (..)/2 *)
  replace (6 * (Num / 9) + 5 - 1) with (xp - 1)
    by (unfold xp; ring).

  replace (18 * m + 6 * 0 + 1 - 1) with (x - 1)
    by (unfold x; ring).

  (* Multiply both sides by 2 to kill the /2 *)
  apply Z.mul_reg_l with (p := 2); [lia|].
  rewrite Z.mul_sub_distr_l.
  
  (* Show that 2 * ((z - 1) / 2) = z - 1 for x and xp *)

  (* For xp *)
  assert (Hxp2 : 2 * ((xp - 1) / 2) = xp - 1).
  {
    unfold xp.
    (* xp - 1 = 6*(Num/9) + 4 = 2 * (3*(Num/9) + 2) *)
    replace (6 * (Num / 9) + 5 - 1)
      with (2 * (3 * (Num / 9) + 2)) by ring.
    rewrite Z.mul_comm.            
    set (ONum := (3 * (Num / 9) + 2)).
    replace (2 * ONum) with  (ONum * 2) by lia. 
    rewrite Z.div_mul by lia.
    reflexivity.    
  }

  (* For x *)
  assert (Hx2 : 2 * ((x - 1) / 2) = x - 1).
  {
    unfold x.
    (* x - 1 = 18 * m = 2 * (9 * m) *)
    replace (6 * 0) with 0 by ring.    
    replace (18 * m + 0 + 1 - 1) with (18 * m) by ring.
    replace (18 * m) with (2 * (9 * m)) by ring.
    rewrite Z.mul_comm.   
    set (Om := 9 * m).
    replace (2 * Om) with (Om * 2) by lia. 
    rewrite Z.div_mul by lia.
    reflexivity.     
  }

  rewrite Hxp2, Hx2.
  (* LHS is now (xp - 1) - (x - 1) = xp - x *)
  replace ((xp - 1) - (x - 1)) with (xp - x) by ring.
    (* We are at: xp - x = 2 * (calc_r psi_0 m * K + Delta) *)

  unfold xp, x in *.
  (* clean the useless 6*0 *)
  replace (18 * m + 6 * 0 + 1) with (18 * m + 1) by ring.

  (* LHS: xp - x *)
  replace (6 * (Num / 9) + 5 - (18 * m + 1))
    with (2 * (3 * (Num / 9) - 9 * m + 2)) by ring.
  (* Goal: 2 * (3 * (Num / 9) - 9 * m + 2)
           = 2 * (calc_r psi_0 m * K + Delta) *)

  (* cancel the outer 2 *)
  apply Z.mul_reg_l with (p := 2); [lia|].
  (* Goal: 3 * (Num / 9) - 9 * m + 2 = calc_r psi_0 m * K + Delta *)

  cbv [calc_r] in *.
  (* calc_r psi_0 m = 3 * m *)

  unfold Delta, q_p, pow64 in *.
  rewrite Hq.
  (* Delta = 8 * (3 * k) + 2 = 24 * k + 2 *)
  (* Goal: 3 * (Num / 9) - 9 * m + 2 = 3 * m * K + 24 * k + 2 *)

  (* strip the common +2 *)
  replace (3 * (Num / 9) - 9 * m + 2)
    with ((3 * (Num / 9) - 9 * m) + 2) by ring.
  replace (3 * m * K + 24 * k + 2)
    with ((3 * m * K + 24 * k) + 2) by ring.
    (* simplify the get_input_reqs psi_0 bit: j = 0 there *)
  cbv [get_input_reqs] in *. 
  (* simplify away the + 0 *)
  replace (3 * m + 0) with (3 * m) by ring.

  (* turn 2 * (2 * ...) into 4 * ... on both sides *)
  replace (2 * (2 * (3 * (Num / 9) - 9 * m + 2)))
    with (4 * (3 * (Num / 9) - 9 * m + 2)) by ring.
  replace (2 * (2 * ((3 * m) * K + (8 * (3 * k) + 2))))
    with (4 * ((3 * m) * K + (8 * (3 * k) + 2))) by ring.
  (* We are at:
   4 * (3 * (Num / 9) - 9 * m + 2) =
   4 * (3 * m * K + (8 * (3 * k) + 2)) *)

  (* 1. Define the quotient E so that Num = 9 * E *)

  set (E := 144 * m * k + 16 * m + 8 * k).

  assert (HNum : Num = 9 * E).
  {
    unfold Num, E.
    replace (2 ^ 4) with 16 by (compute; reflexivity).
    rewrite Hk.  (* 64 ^ p = 9 * k + 1 *)
    ring.
  }

  assert (HNum_div9 : Num / 9 = E).
  {
    rewrite HNum.
    replace (9 * E) with (E * 9) by ring.
    rewrite Z.div_mul by lia.
    reflexivity.
  }

  rewrite HNum_div9.
  (* goal is now:
    4 * (3 * E - 9 * m + 2) =
    4 * (3 * m * K + (8 * (3 * k) + 2)) *)

  (* 2. Rewrite K in terms of k using 64^p = 9*k + 1 *)

  unfold K.
  repeat rewrite Z.pow_add_r by lia.
  change (2 ^ 4) with 16.

  replace (2 ^ (6 * p)) with (64 ^ p).
  2:{
    rewrite Z.pow_mul_r by lia.
    change (2 ^ 6) with 64.
    reflexivity.
  }

  rewrite Hk.
  (* Now the goal is a pure polynomial identity in m and k,
    with an extra factor 4 on both sides. *)

  unfold E.
  ring.
Qed.

Lemma drift_equation_psi_1 :
  forall (p m : Z),
    p >= 0 ->
    let x  := construct_x psi_1 m in
    let xp := x_prime psi_1 p m in
    (* psi_1: alpha = 6, eo family, corrected Delta *)
    let K     := pow2 (6 + 6 * p) - 3 in
    let q_p   := (pow64 p - 1) / 3 in
    let Delta := 32 * q_p + 10 in
    let predicted := (calc_r psi_1 m) * K + Delta in    
    tag xp - tag x = predicted.
Proof.
  intros p m Hp x xp K q_p Delta predicted.
  unfold x, xp, construct_x, x_prime, F_transform, tag,
         get_input_reqs, get_params, calc_r,
         pow2, pow64, K, q_p, Delta, predicted in *.
  cbv [alpha beta c delta get_params get_input_reqs ] in *.
  
  destruct (pow64_exists_k p Hp) as [k Hk].
  assert (Hq: (64 ^ p - 1) / 3 = 3 * k).
  { rewrite Hk. replace (9 * k + 1 - 1) with (3 * (3 * k)) by ring. 
    replace (3 * (3 * k)) with (3 * k * 3) by ring.
    rewrite Z.div_mul by lia. reflexivity. }
  
  assert (Hqp : ((64 ^ p - 1) / 3) = 3 * k) by exact Hq.
  (* 2. Name the big numerator *)  

  unfold tag.

  (* Introduce k with 64^p = 9*k + 1 *)
  pose proof (pow64_decomp p Hp) as Hkp.
  set (kp := 64 ^ p / 9) in Hkp.
  (* Hk : 64 ^ p = 9 * k + 1 *)

  (* Turn q_p into 3*k *)
  assert (Hq_val : (64 ^ p - 1) / 3 = 3 * k).
  {
    rewrite Hk.
    replace (9 * k + 1 - 1) with (9 * k) by ring.
    replace (9 * k) with (3 * k * 3) by ring.
    rewrite Z.div_mul by lia.
    reflexivity.
  }  

  (* Clean up 2^6 in the numerator of xp *)
  replace (2 ^ 6) with 64 in * by (compute; reflexivity).

  (* Define the main numerator Num for xp *)
  set (Num := (9 * m * 64 + 224) * 64 ^ p + -8).

  (* Now tag xp and tag x explicitly *)

  (* tag xp = (xp - 1) / 2 *)
  assert (Htag_xp : (6 * (Num / 9) + 5 - 1) / 2 = 3 * (Num / 9) + 2).
  {
    replace (6 * (Num / 9) + 5 - 1) with (6 * (Num / 9) + 4) by ring.
    replace (6 * (Num / 9) + 4)
      with (2 * (3 * (Num / 9) + 2)) by ring.
    set (ONum := (3 * (Num / 9) + 2)).
    replace (2 * ONum) with (ONum * 2) by lia.
    rewrite Z.div_mul by lia.
    ring.
  }

  (* tag x = (x - 1) / 2 *)
  assert (Htag_x : (18 * m + 6 + 1 - 1) / 2 = 9 * m + 3).
  {
    replace (18 * m + 6 + 1 - 1) with (18 * m + 6) by ring.
    replace (18 * m + 6) with (2 * (9 * m + 3)) by ring.
    set (Om := (9 * m + 3)).
    replace (2 * Om) with (Om * 2) by lia.
    rewrite Z.div_mul by lia.
    ring.
  }

    (* First rewrite the xp-term using Htag_xp *)
  rewrite Htag_xp.

  (* Normalize the x-term to match Htag_x's LHS *)
  replace (18 * m + 6 * 1 + 1 - 1)
    with (18 * m + 6 + 1 - 1) by ring.

  (* Now this matches Htag_x exactly *)
  rewrite Htag_x.

  (* Goal now:
       3 * (Num / 9) + 2 - (9 * m + 3)
       = (3 * m + 1) * (2 ^ (6 + 6 * p) - 3) + (32 * ((64 ^ p - 1) / 3) + 10)
   *)

  (* Simplify LHS a bit *)
  replace (3 * (Num / 9) + 2 - (9 * m + 3))
    with (3 * (Num / 9) - 9 * m - 1) by ring.

  (* Rewrite q_p to 3*k inside Delta *)
  (* expose the actual arithmetic behind Delta *)
  unfold Delta, q_p, pow64 in *.
  (* Now Delta = 32 * ((64 ^ p - 1) / 3) + 10 *)

  (* now Hqp matches a subterm *)
  rewrite Hqp.
  (* Delta becomes 32 * (3 * k) + 10 *)

  (* simplify that *)
  replace (32 * (3 * k) + 10) with (96 * k + 10) by ring.
  
  (* Goal:
       3 * (Num / 9) - 9 * m - 1
       = (3 * m + 1) * (2 ^ (6 + 6 * p) - 3) + (96 * k + 10)
   *)

  (* Express Num as 9 * E, then kill /9 *)
  set (E := 576 * m * k + 224 * k + 64 * m + 24).

  assert (HNum : Num = 9 * E).
  {
    unfold Num, E.
    rewrite Hk.
    ring.
  }

  assert (HNum_div9 : Num / 9 = E).
  {
    rewrite HNum.
    replace (9 * E) with (E * 9) by ring.
    rewrite Z.div_mul by lia.
    reflexivity.
  }

  rewrite HNum_div9.
  (* Goal:
       3 * E - 9 * m - 1
       = (3 * m + 1) * (2 ^ (6 + 6 * p) - 3) + (96 * k + 10)
   *)

  (* Rewrite K = 2^(6+6p) - 3 in terms of k using 64^p = 9*k + 1 *)
  unfold E.
  unfold K.

  (* 2^(6+6p) = 2^6 * 2^(6p) and 2^(6p) = (2^6)^p = 64^p *)
  repeat rewrite Z.pow_add_r by lia.
  change (2 ^ 6) with 64.
  rewrite Z.pow_mul_r by lia.
  change (2 ^ 6) with 64.

  (* Now 2^(6+6p) = 64 * 64^p, rewrite 64^p to 9*k + 1 *)
  rewrite Hk.
  cbv [calc_r get_input_reqs] in *.
  (* or just [calc_r] if that’s enough in your file *)


  (* Everything is now a polynomial in m and k *)
  ring.
Qed.

Lemma div2_cancel (n : Z) :
  2 * n / 2 = n.
Proof.
  (* Put numerator into the shape a * b *)
  replace (2 * n) with (n * 2) by ring.
  (* Now we can use Z.div_mul: (a * b) / b = a *)
  rewrite Z.div_mul by lia.  (* 2 <> 0 *)
  reflexivity.
Qed.

Lemma double_div2_even (ONum : Z) :
  ONum mod 2 = 0 ->
  2 * (ONum / 2) = ONum.
Proof.
  intro Hmod.
  (* Use an exact-division lemma: a = b * (a / b) when a mod b = 0 *)
  symmetry.
  apply (Z_div_exact_full_2 ONum 2); [lia | exact Hmod].
Qed.

Lemma drift_equation_psi_2 :
  forall (p m : Z),
    p >= 0 ->
    let x  := construct_x psi_2 m in
    let xp := x_prime  psi_2 p m in

    (* psi_2: alpha = 2, eo–type *)
    let K     := pow2 (2 + 6 * p) - 3 in
    let q_p   := (64 ^ p - 1) / 3 in
    let Delta := 2 * q_p in
    let predicted := (calc_r psi_2 m) * K + Delta in
    tag xp - tag x = predicted.
Proof.
  intros p m Hp x xp K q_p Delta predicted.
  unfold x, xp, construct_x, x_prime, F_transform, tag,
         get_input_reqs, get_params, calc_r,
         pow2, K, q_p, Delta, predicted in *.
  cbv [alpha beta c delta get_input_reqs get_params] in *.

  (* pow64 decomposition: 64^p = 9*k + 1 *)
  destruct (pow64_exists_k p Hp) as [k Hk].
  assert (Hq : (64 ^ p - 1) / 3 = 3 * k).
  { rewrite Hk.
    replace (9 * k + 1 - 1) with (9 * k) by ring.
    replace (9 * k) with (3 * (3 * k)) by ring.
    set (T := 3 * k).
    replace (3 * T) with (T * 3) by ring.
    rewrite Z.div_mul by lia.
    reflexivity. }

  (* Simplify 2^2 and define Num *)
  replace (2 ^ 2) with 4 in * by (compute; reflexivity).
  set (Num := (9 * m * 4 + 26) * 64 ^ p + -8) in *.

  (* 1. Compute tag xp = 3 * (Num / 9) + 2 *)
  assert (Htag_xp : (6 * (Num / 9) + 5 - 1) / 2 = 3 * (Num / 9) + 2).
  { replace (6 * (Num / 9) + 5 - 1) with (6 * (Num / 9) + 4) by ring.
    replace (6 * (Num / 9) + 4) with (2 * (3 * (Num / 9) + 2)) by ring.
    set (T := 3 * (Num / 9) + 2).
    replace (2 * T) with (T * 2) by ring.
    rewrite Z.div_mul by lia.
    ring. }

  (* 2. Compute tag x = 9*m + 6 *)
  assert (Htag_x : (18 * m + 12 + 1 - 1) / 2 = 9 * m + 6).
  { replace (18 * m + 12 + 1 - 1) with (18 * m + 12) by ring.
    replace (18 * m + 12) with (2 * (9 * m + 6)) by ring.
    set (T := 9 * m + 6).
    replace (2 * T) with (T * 2) by ring.
    rewrite Z.div_mul by lia.
    ring. }
  
  cbv [pow64] in *.
  unfold Delta.

  (* Recognise the two big (/2) terms as (xp - 1)/2 and (x - 1)/2 *)
  change ((6 * (((9 * m * 4 + 26) * 64 ^ p + -8) / 9) + 5 - 1) / 2)
    with ((xp - 1) / 2).
  change ((18 * m + 6 * 2 + 1 - 1) / 2)
    with ((x - 1) / 2).

  (* Fold back the definition of tag *)
  fold (tag xp).
  fold (tag x).

  (* Now the goal is: *)
  (*   tag xp - tag x = calc_r psi_2 m * K + 2 * ((64 ^ p - 1) / 3) *)

  assert (Hxp2 : 2 * ((xp - 1) / 2) = xp - 1).
  {
    unfold xp.
    (* xp = 6 * (((9 * m * 2 ^ 2 + 26) * 64 ^ p + -8) / 9) + 5 *)

    (* Simplify 2^2 *)
    replace (2 ^ 2) with 4 by (compute; reflexivity).

    (* Turn the big numerator into [Num] using the existing definition *)
    change (((9 * m * 4 + 26) * 64 ^ p + -8) / 9)
      with (Num / 9).

    (* Now the goal is:
        2 * ((6 * (Num / 9) + 5 - 1) / 2)
        = 6 * (Num / 9) + 5 - 1 *)

    (* Clean up +5-1 *)
    replace (6 * (Num / 9) + 5 - 1)
      with (6 * (Num / 9) + 4) by ring.

    (* Factor 2 out: 6*(Num/9)+4 = 2 * (3*(Num/9)+2) *)
    replace (6 * (Num / 9) + 4)
      with (2 * (3 * (Num / 9) + 2)) by ring.

    set (Y := 3 * (Num / 9) + 2).

    (* Now LHS is 2 * ((2 * Y) / 2) *)
    replace (2 * ((2 * Y) / 2))
      with (((2 * Y) / 2) * 2) by ring.

    replace (2 * Y) with (Y * 2) by ring.
    (* Now goal is: Y * 2 / 2 * 2 = 2 * Y *)

    (* Make the precedence explicit (optional, but clear): *)
    change (Y * 2 / 2 * 2) with ((Y * 2) / 2 * 2).

    rewrite Z.div_mul by lia.
    ring.  
  }  

  (* Multiply the whole equation by 2 and use those equalities *)
  apply Z.mul_reg_l with (p := 2); [lia|].
  rewrite Z.mul_sub_distr_l.  

  (* Now the goal is exactly: *)
  (*   xp - x = 2 * (calc_r psi_2 m * K + 2 * ((64 ^ p - 1) / 3)) *)
  (* i.e. the same "xp - x = 2 * drift" shape we already handled
    in Psi_0 / Psi_1 / psi_0 / etc. *)

  (* From here you can: *)
  (* - unfold xp, x, K, Delta/q_p,
    - introduce Num,
    - use pow64_exists_k, Hk, Hq,
    - define E and prove Num = 9*E, Num/9 = E,
    - and finish with lia/ring, exactly as in the other drift lemmas. *)


  clear Htag_xp Htag_x.
  (* Now: 3 * (Num / 9) - (9 * m + 4)
          = (3 * m + 2) * (2 ^ (2 + 6 * p) - 3) + 2 * ((64 ^ p - 1) / 3) *)

  (* 3. Use q_p = 3*k, so Delta = 6*k *)
  rewrite Hq.
  (* RHS becomes: (3*m+2) * (2 ^ (2 + 6 * p) - 3) + 6 * k *)

  (* 4. Express Num / 9 via an explicit E *)
  set (E := 36 * m * k + 26 * k + 4 * m + 2) in *.

  assert (HNum : Num = 9 * E).
  { unfold Num, E.
    rewrite Hk.      (* 64^p = 9*k + 1 *)
    ring. }

  assert (HNum_div9 : Num / 9 = E).
  { rewrite HNum.
    replace (9 * E) with (E * 9) by ring.
    rewrite Z.div_mul by lia.
    reflexivity. }

  replace (2 * tag xp - 2 * tag x)
    with (2 * (tag xp - tag x)) by ring.  
  (* New goal: tag xp - tag x =
               calc_r psi_2 m * K + 2 * (3 * k) *)

  (* 2. Expand tag, x, xp to expose Num / 9 *)
  
  
  (* Now goal is: 
       (6 * (Num / 9) + 5 - 1) / 2 - (18 * m + 12 + 1 - 1) / 2
       = calc_r psi_2 m * K + 2 * (3 * k)
   *)

  (* Compute tag xp: (xp - 1)/2 = 3 * (Num/9) + 2 *)
  assert (Htag_xp' : (6 * (Num / 9) + 5 - 1) / 2 = 3 * (Num / 9) + 2).
  {
    (* Rewrite numerator as 2 * (3*(Num/9) + 2) *)
    replace (6 * (Num / 9) + 5 - 1)
      with (2 * (3 * (Num / 9) + 2)) by ring.
    replace (2 * (3 * (Num / 9) + 2))
      with ((3 * (Num / 9) + 2) * 2) by ring.
    rewrite Z.div_mul by lia.
    reflexivity.
  }

  (* Compute tag x: (x - 1)/2 = 9*m + 6 *)
  assert (Htag_x' : (18 * m + 12 + 1 - 1) / 2 = 9 * m + 6).
  {
    replace (18 * m + 12 + 1 - 1)
      with (2 * (9 * m + 6)) by ring.
    replace (2 * (9 * m + 6))
      with ((9 * m + 6) * 2) by ring.
    rewrite Z.div_mul by lia.
    reflexivity.
  }

  (* First, make the factor 2 syntactically obvious on both sides *)
  (* (You may already be in this shape, so this line might be optional) *)
  replace (2 * (tag xp - tag x))
    with (2 * (tag xp - tag x)) by ring.
  replace (2 * (calc_r psi_2 m * K + 2 * (3 * k)))
    with (2 * (calc_r psi_2 m * K + 2 * (3 * k))) by ring.
  
    (* We are at: 2 * (tag xp - tag x) = 2 * (calc_r psi_2 m * K + 2 * (3 * k)) *)

  (* 1. Cancel the common factor 2 on both sides *)  
  rewrite Z.mul_sub_distr_l.
  (* New goal:
       2 * tag xp - 2 * tag x = 2 * (calc_r psi_2 m * K + 2 * (3 * k)) *)

  (* 2. Express 2 * tag xp and 2 * tag x in terms of xp and x *)
  unfold tag.

  (* You already have Hxp2 : 2 * ((xp - 1) / 2) = xp - 1 *)
  rewrite Hxp2.

  (* Now we need the analogous fact for x *)
  assert (Hx2 : 2 * ((x - 1) / 2) = x - 1).
  {
    unfold x.
    (* x - 1 = 18*m + 12 = 2 * (9*m + 6) *)
    replace (18 * m + 6 * 2 + 1 - 1) with (2 * (9 * m + 6)) by ring.
    set ( Y := 9 * m + 6).
    (* Now LHS is 2 * ((2 * Y) / 2) *)
    replace (2 * ((2 * Y) / 2))
      with (((2 * Y) / 2) * 2) by ring.

    replace (2 * Y) with (Y * 2) by ring.
    (* Now goal is: Y * 2 / 2 * 2 = 2 * Y *)

    (* Make the precedence explicit (optional, but clear): *)
    change (Y * 2 / 2 * 2) with ((Y * 2) / 2 * 2).

    rewrite Z.div_mul by lia.    
    ring.
  }
  rewrite Hx2.

  (* Left side becomes (xp - 1) - (x - 1) = xp - x *)
  ring_simplify.
  (* New goal:
       xp - x = 2 * (calc_r psi_2 m * K + 2 * (3 * k)) *)

  (* 3. Expand xp, x and use Num / 9 = E *)
  unfold xp, x in *.

  (* 1. Normalize 2^2 to 4 so it matches the definition of Num *)
  replace (2 ^ 2) with 4 in * by (compute; reflexivity).

  (* 2. Tell Coq that this numerator *is* Num *)  
  change (((9 * m * 4 + 26) * 64 ^ p + -8) / 9) with (Num / 9).


  replace (18 * m + 12 + 1) with (18 * m + 13) by ring.
  (* and/or: ring_simplify in *; lia. *)


  (* 3. Now Num / 9 appears, so this works *)
  rewrite HNum_div9.
  
  (* Now xp - x is in terms of E, m, k; RHS still has calc_r and K *)

  (* 4. Unfold calc_r and K, and rewrite K using Hk *)
  cbv [calc_r get_params get_input_reqs alpha beta c delta] in *.
  unfold K in *.
  unfold E in *.

  (* Turn 2^(2+6p) into something involving 64^p, then use Hk *)
  repeat rewrite Z.pow_add_r by lia.
  change (2 ^ 2) with 4.
  rewrite (Z.pow_mul_r 2 6 p) by lia.
  change (2 ^ 6) with 64.
  rewrite Hk.

  (* Now both sides are just polynomials in m and k *)
  ring.
Qed.


(* -------------------------------------------------------------------------- *)
(* Family o -> e (Type oe) *)
(* -------------------------------------------------------------------------- *)

Lemma drift_equation_omega_0 :
  forall (p m : Z),
    p >= 0 ->
    let x  := construct_x omega_0 m in
    let xp := x_prime omega_0 p m in
    (* omega_0: alpha = 3, corrected e-type Delta *)
    let K     := pow2 (3 + 6 * p) - 3 in
    let q_p   := (pow64 p - 1) / 3 in
    let Delta := 20 * q_p + 4 in
    let predicted := (calc_r omega_0 m) * K + Delta in    
    tag xp - tag x = predicted.
Proof.
  intros p m Hp x xp K q_p Delta predicted.
  unfold x, xp, construct_x, x_prime, F_transform, tag,
         get_input_reqs, get_params, calc_r,
         pow2, pow64, K, q_p, Delta, predicted in *.
  cbv [alpha beta c delta get_params get_input_reqs ] in *.
  
  destruct (pow64_exists_k p Hp) as [k Hk].
  assert (Hq: (64 ^ p - 1) / 3 = 3 * k).
  { rewrite Hk. replace (9 * k + 1 - 1) with (3 * (3 * k)) by ring. 
    replace (3 * (3 * k)) with (3 * k * 3) by ring.
    rewrite Z.div_mul by lia. reflexivity. }  

    (* simplify 2^3 and define Num *)
  replace (2 ^ 3) with 8 in * by (compute; reflexivity).

  set (Num := (9 * m * 8 + 20) * 64 ^ p + -2) in *.
  (* now the goal is:
       (6 * (Num / 9) + 1 - 1) / 2 -
       (18 * m + 6 * 0 + 5 - 1) / 2
       = calc_r omega_0 m * K + Delta *)

  (* 1. Compute tag xp = (xp - 1) / 2 = 3 * (Num / 9) *)

  assert (Htag_xp : (6 * (Num / 9) + 1 - 1) / 2 = 3 * (Num / 9)).
  {
    replace (6 * (Num / 9) + 1 - 1) with (6 * (Num / 9)) by ring.
    replace (6 * (Num / 9)) with (2 * (3 * (Num / 9))) by ring.
    set (ONum := (3 * (Num / 9))).
    replace (2 * ONum) with (ONum * 2) by lia.
    rewrite Z.div_mul by lia.
    ring.
  }

  (* 2. Compute tag x = (x - 1) / 2 = 9*m + 2 *)

  assert (Htag_x : (18 * m + 6 * 0 + 5 - 1) / 2 = 9 * m + 2).
  {
    replace (18 * m + 6 * 0 + 5 - 1) with (18 * m + 4) by ring.
    replace (18 * m + 4) with (2 * (9 * m + 2)) by ring.
    set (Om := (9 * m + 2)).
    replace (2 * Om) with (Om * 2) by lia.
    rewrite Z.div_mul by lia.
    ring.
  }

  rewrite Htag_xp, Htag_x.
  (* Goal now:
       3 * (Num / 9) - (9 * m + 2)
       = calc_r omega_0 m * K + Delta *)

  (* 3. Rewrite Delta using Hq: q_p = 3*k, so Delta = 6*k *)

  unfold Delta, q_p, pow64 in *.
  rewrite Hq.
  (* Delta = 2 * (3 * k) = 6 * k *)

  replace (20 * (3 * k)) with (60 * k) by ring.
  (* Goal:
       3 * (Num / 9) - (9 * m + 2)
       = calc_r omega_0 m * K + 6 * k *)

    (* 4. Express Num as 9 * E, then kill the /9 *)
  set (E := 72 * m * k + 20 * k + 8 * m + 2).

  assert (HNum : Num = 9 * E).
  {
    unfold Num, E.
    rewrite Hk.  (* 64 ^ p = 9 * k + 1 *)
    ring.
  }

  assert (HNum_div9 : Num / 9 = E).
  {
    rewrite HNum.
    replace (9 * E) with (E * 9) by ring.
    rewrite Z.div_mul by lia.
    reflexivity.
  }

  rewrite HNum_div9.
  (* Goal:
       3 * E - (9 * m + 2)
       = calc_r omega_0 m * K + (60 * k + 4) *)

  (* 5. Rewrite K in terms of k: 2^(3+6p) = 8 * 64^p = 8 * (9*k+1) *)
  unfold K, pow2 in *.
  repeat rewrite Z.pow_add_r by lia.
  change (2 ^ 3) with 8.
  rewrite Z.pow_mul_r by lia.
  change (2 ^ 6) with 64.
  rewrite Hk.  (* 64 ^ p = 9*k + 1 *)
  (* Now K is 8 * (9 * k + 1) - 3 *)

  (* 6. calc_r omega_0 m is already unfolded by the initial [unfold calc_r ...],
        but if not, you can do: [cbv [calc_r get_input_reqs] in *]. *)

  cbv [calc_r get_input_reqs] in *.

  unfold E in *.
  ring.
Qed.

Lemma drift_equation_omega_1 :
  forall (p m : Z),
    p >= 0 ->
    let x  := construct_x omega_1 m in
    let xp := x_prime omega_1 p m in
    (* omega_1: alpha = 1, corrected Delta *)
    let K     := pow2 (1 + 6 * p) - 3 in
    let q_p   := (pow64 p - 1) / 3 in
    let Delta := 5 * q_p - 1 in
    let predicted := (calc_r omega_1 m) * K + Delta in
    
    tag xp - tag x = predicted.
Proof.
  intros p m Hp x xp K q_p Delta predicted.
  unfold x, xp, construct_x, x_prime, F_transform, tag,
         get_input_reqs, get_params, calc_r,
         pow2, pow64, K, q_p, Delta, predicted in *.
  cbv [alpha beta c delta get_params get_input_reqs] in *.

  (* 64^p = 9*k + 1 *)
  destruct (pow64_exists_k p Hp) as [k Hk].

  assert (Hq : (64 ^ p - 1) / 3 = 3 * k).
  { rewrite Hk.
    replace (9 * k + 1 - 1) with (9 * k) by ring.
    replace (9 * k) with (3 * k * 3) by ring.
    rewrite Z.div_mul by lia.
    reflexivity. }

  (* simplify 2^1 and define Num *)
  replace (2 ^ 1) with 2 in * by (compute; reflexivity).
  set (Num := (9 * m * 2 + 11) * 64 ^ p + -2) in *.

  (* tag xp = 3 * (Num / 9) *)
  assert (Htag_xp : (6 * (Num / 9) + 1 - 1) / 2 = 3 * (Num / 9)).
  {
    replace (6 * (Num / 9) + 1 - 1) with (6 * (Num / 9)) by ring.
    replace (6 * (Num / 9)) with (2 * (3 * (Num / 9))) by ring.
    set (ONum := (3 * (Num / 9))).
    replace (2 * ONum) with (ONum * 2) by lia.
    rewrite Z.div_mul by lia.
    ring.
  }

  (* tag x = 9*m + 5 *)
  assert (Htag_x : (18 * m + 6 * 1 + 5 - 1) / 2 = 9 * m + 5).
  {
    replace (18 * m + 6 * 1 + 5 - 1) with (18 * m + 10) by ring.
    replace (18 * m + 10) with (2 * (9 * m + 5)) by ring.
    set (Om := (9 * m + 5)).
    replace (2 * Om) with (Om * 2) by lia.
    rewrite Z.div_mul by lia.
    ring.
  }

  rewrite Htag_xp, Htag_x.
  (* Now:
       3 * (Num / 9) - (9 * m + 5)
       = calc_r omega_1 m * K + (5 * ((pow64 p - 1) / 3) - 1) *)

  (* use q_p = 3*k to rewrite Delta *)
  unfold pow64 in *.
  unfold Delta in *.
  rewrite Hq.
  replace (5 * (3 * k) - 1) with (15 * k - 1) by ring.

  (* express Num as 9 * E to eliminate /9 *)
  set (E := 18 * m * k + 11 * k + 2 * m + 1).

  assert (HNum : Num = 9 * E).
  {
    unfold Num, E.
    rewrite Hk.
    ring.
  }

  assert (HNum_div9 : Num / 9 = E).
  {
    rewrite HNum.
    replace (9 * E) with (E * 9) by ring.
    rewrite Z.div_mul by lia.
    reflexivity.
  }

  rewrite HNum_div9.
  (* Goal:
       3 * E - (9 * m + 5)
       = calc_r omega_1 m * K + (15 * k - 1) *)

  (* rewrite K via k: 2^(1+6p) = 2 * 64^p = 2 * (9*k+1) *)
  unfold K, pow2 in *.
  repeat rewrite Z.pow_add_r by lia.
  change (2 ^ 1) with 2.
  rewrite Z.pow_mul_r by lia.
  change (2 ^ 6) with 64.
  rewrite Hk.

  (* normalize calc_r and solve as a polynomial identity *)
  cbv [calc_r get_input_reqs] in *.
  unfold E in *.
  ring.
Qed.


Lemma drift_equation_omega_2 :
  forall (p m : Z),
    p >= 0 ->
    let x  := construct_x omega_2 m in
    let xp := x_prime omega_2 p m in
    (* omega_2: alpha = 5, corrected Delta *)
    let K     := pow2 (5 + 6 * p) - 3 in
    let q_p   := (pow64 p - 1) / 3 in
    let Delta := 80 * q_p + 24 in
    let predicted := (calc_r omega_2 m) * K + Delta in
    
    tag xp - tag x = predicted.
Proof.
  intros p m Hp x xp K q_p Delta predicted.
  unfold x, xp, construct_x, x_prime, F_transform, tag,
         get_input_reqs, get_params, calc_r,
         pow2, pow64, K, q_p, Delta, predicted in *.
  cbv [alpha beta c delta get_params get_input_reqs] in *.

  (* 1. Introduce k with 64^p = 9*k + 1 *)
  destruct (pow64_exists_k p Hp) as [k Hk].

  assert (Hq : (64 ^ p - 1) / 3 = 3 * k).
  {
    rewrite Hk.
    replace (9 * k + 1 - 1) with (9 * k) by ring.
    replace (9 * k) with (3 * k * 3) by ring.
    replace (3 * k * 3) with (k * 3 * 3) by ring.
    rewrite Z.div_mul by lia.
    lia.    
  }

  (* 2. Simplify 2^5 and define Num *)
  replace (2 ^ 5) with 32 in * by (compute; reflexivity).

  set (Num := (9 * m * 32 + 272) * 64 ^ p + -2) in *.
  (* Now xp = 6 * (Num / 9) + 1
     and x  = 18 * m + 12 + 5 = 18 * m + 17 *)

  (* 3. tag xp = 3 * (Num / 9) *)
  assert (Htag_xp : (6 * (Num / 9) + 1 - 1) / 2 = 3 * (Num / 9)).
  {
    replace (6 * (Num / 9) + 1 - 1) with (6 * (Num / 9)) by ring.
    replace (6 * (Num / 9)) with (2 * (3 * (Num / 9))) by ring.
    set (ONum := (3 * (Num / 9))).
    replace (2 * ONum) with (ONum * 2) by lia.
    rewrite Z.div_mul by lia.
    ring.
  }

  (* 4. tag x = 9*m + 8 *)
  assert (Htag_x : (18 * m + 12 + 5 - 1) / 2 = 9 * m + 8).
  {
    replace (18 * m + 12 + 5 - 1) with (18 * m + 16) by ring.
    replace (18 * m + 16) with (2 * (9 * m + 8)) by ring.
    set (Om := (9 * m + 8)).
    replace (2 * Om) with (Om * 2) by lia.
    rewrite Z.div_mul by lia.
    ring.
  }

  replace (6 *2) with 12 by ring.

  rewrite Htag_xp, Htag_x.
  (* Goal:
       3 * (Num / 9) - (9 * m + 8)
       = calc_r omega_2 m * K + (80 * ((64 ^ p - 1) / 3) + 24) *)

  (* 5. Use q_p = 3*k inside Delta *)
  unfold pow64 in *.
  unfold Delta in *.
  rewrite Hq.
    (* Express Num as 9 * E to remove /9 *)
  set (E := 288 * m * k + 272 * k + 32 * m + 30).

  assert (HNum : Num = 9 * E).
  {
    unfold Num, E.
    rewrite Hk. (* 64^p = 9*k + 1 *)
    ring.
  }

  assert (HNum_div9 : Num / 9 = E).
  {
    rewrite HNum.
    replace (9 * E) with (E * 9) by ring.
    rewrite Z.div_mul by lia.
    reflexivity.
  }

  rewrite HNum_div9.
  (* Goal is now:
       3 * E - (9 * m + 8)
       = calc_r omega_2 m * K + (240 * k + 24) *)

  (* Rewrite K via k: 2^(5+6p) = 32 * 64^p = 32 * (9*k+1) *)
  unfold K, pow2 in *.
  repeat rewrite Z.pow_add_r by lia.
  change (2 ^ 5) with 32.
  rewrite Z.pow_mul_r by lia.
  change (2 ^ 6) with 64.
  rewrite Hk.  (* K = 32 * (9*k+1) - 3 = 288*k + 29 *)

  cbv [calc_r get_input_reqs] in *.
  unfold E in *.
  ring.
Qed.

(* -------------------------------------------------------------------------- *)
(* Family o (Type oo) *)
(* -------------------------------------------------------------------------- *)

Lemma drift_equation_Omega_0 :
  forall (p m : Z),
    p >= 0 ->
    let x  := construct_x Omega_0 m in
    let xp := x_prime Omega_0 p m in
    (* Omega_0: alpha = 5, corrected o-type Delta *)
    let K     := pow2 (5 + 6 * p) - 3 in
    let q_p   := (pow64 p - 1) / 3 in
    let Delta := 80 * q_p + 24 in
    let predicted := (calc_r Omega_0 m) * K + Delta in    
    tag xp - tag x = predicted.
Proof.
  intros p m Hp x xp K q_p Delta predicted.
  unfold x, xp, construct_x, x_prime, F_transform, tag,
         get_input_reqs, get_params, calc_r,
         pow2, pow64, K, q_p, Delta, predicted in *.
  cbv [alpha beta c delta get_params get_input_reqs ] in *.
  
  destruct (pow64_exists_k p Hp) as [k Hk].
  assert (Hq : (64 ^ p - 1) / 3 = 3 * k).
  {
    rewrite Hk.
    replace (9 * k + 1 - 1) with (9 * k) by ring.
    replace (9 * k) with (3 * k * 3) by ring.
    replace (3 * k * 3) with (k * 3 * 3) by ring.
    rewrite Z.div_mul by lia.
    lia.    
  }
  
  replace (2 ^ 5) with 32 in * by (compute; reflexivity).  
  set (Num := (9 * m * 32 + 80) * 64 ^ p + -8) in *.

  (* 3. tag xp = 3 * (Num / 9) *)
  assert (Htag_xp : (6 * (Num / 9) + 5 - 1) / 2 = 3 * (Num / 9) + 2).
  {
    replace (6 * (Num / 9) + 5 - 1)
      with (6 * (Num / 9) + 4) by ring.    
    replace (6 * (Num / 9)) with (2 * (3 * (Num / 9))) by ring.    
    set (ONum := (3 * (Num / 9))).
    replace (2 * ONum + 4) with (2 * (ONum + 2)) by ring.
    replace (2 * (ONum + 2)) with ((ONum + 2) * 2) by lia.    
    rewrite Z.div_mul by lia.
    ring.
  }

  (* 4. tag x = 9*m + 8 *)
  assert (Htag_x : (18 * m + 5 - 1) / 2 = 9 * m + 2).
  {
    replace (18 * m + 5 - 1)
      with (18 * m + 4) by ring.
    replace (18 * m + 4) with (2 * (9 * m + 2)) by ring.
    set (Om := (9 * m + 2)).
    replace (2 * Om) with (Om * 2) by lia.
    rewrite Z.div_mul by lia.
    ring.
  }

  replace (6 * 0) with 0 by ring.
  replace ((18 * m + 0 + 5 - 1)) with (18 * m + 5 - 1) by ring.
  
  rewrite Htag_xp, Htag_x.
  replace (3 * (Num / 9) + 2 - (9 * m + 2))
    with (3 * (Num / 9) - 9 * m) by ring.  

    (* We want: 3 * (Num / 9) - 9 * m = calc_r Omega_0 m * K + Delta *)

  (* 1. Express Num / 9 as an integer E using Hk *)

  set (E := 288 * m * k + 80 * k + 32 * m + 8 : Z).

  assert (HNum : Num = 9 * E).
  {
    unfold Num, E.
    rewrite Hk.                 (* 64 ^ p = 9 * k + 1 *)
    ring.
  }

  assert (HNum_div9 : Num / 9 = E).
  {
    rewrite HNum.
    replace (9 * E) with (E * 9) by ring.
    rewrite Z.div_mul by lia.   (* (E * 9) / 9 = E *)
    reflexivity.
  }

  rewrite HNum_div9.
  (* Now the goal is: 3 * E - 9 * m = calc_r Omega_0 m * K + Delta *)

  (* 2. Simplify the RHS: rewrite Delta and K in terms of k *)

  unfold Delta, q_p, pow64 in *.
  rewrite Hq.                   (* (pow64 p - 1) / 3 = 3 * k *)
  replace (80 * (3 * k) + 24) with (240 * k + 24) by ring.

  unfold K, pow2 in *.
  repeat rewrite Z.pow_add_r by lia.
  change (2 ^ 5) with 32.

  (* rewrite 2^(6*p) as 64^p, then use Hk *)
  replace (2 ^ (6 * p)) with (64 ^ p).
  2:{ rewrite (Z.pow_mul_r 2 6 p) by lia.
    change (2 ^ 6) with 64.
    reflexivity.
  }
  rewrite Hk.                   (* 64 ^ p = 9 * k + 1 *)
  (* Now K = 32 * (9 * k + 1) - 3 *)

  cbv [calc_r get_input_reqs] in *.
  (* calc_r Omega_0 m = 3 * m + 0 *)
  replace (3 * m + 0) with (3 * m) by ring.

  (* 3. Final algebra: both sides are polynomials in m and k *)

  unfold E.
  ring.
Qed.

Lemma drift_equation_Omega_1 :
  forall (p m : Z),
    p >= 0 ->
    let x  := construct_x Omega_1 m in
    let xp := x_prime Omega_1 p m in
    (* Omega_1: alpha = 3, corrected o-type Delta *)
    let K     := pow2 (3 + 6 * p) - 3 in
    let q_p   := (pow64 p - 1) / 3 in
    let Delta := 20 * q_p + 4 in
    let predicted := (calc_r Omega_1 m) * K + Delta in    
    tag xp - tag x = predicted.
Proof.
  intros p m Hp x xp K q_p Delta predicted.
  unfold x, xp, construct_x, x_prime, F_transform, tag,
         get_input_reqs, get_params, calc_r,
         pow2, pow64, K, q_p, Delta, predicted in *.
  cbv [alpha beta c delta get_params get_input_reqs] in *.
  
  destruct (pow64_exists_k p Hp) as [k Hk].
  assert (Hq : (64 ^ p - 1) / 3 = 3 * k).
  {
    rewrite Hk.
    replace (9 * k + 1 - 1) with (9 * k) by ring.
    replace (9 * k) with (3 * k * 3) by ring.
    replace (3 * k * 3) with (k * 3 * 3) by ring.
    rewrite Z.div_mul by lia.
    lia.    
  }

   (* simplify 2^3 and introduce Num *)
  replace (2 ^ 3) with 8 in * by (compute; reflexivity).
  set (Num := (9 * m * 8 + 44) * 64 ^ p + -8) in *.
  (* xp = 6 * (Num / 9) + 5, x = 18*m + 6 + 5 *)

  (* 1. tag xp = 3*(Num/9) + 2 *)
  assert (Htag_xp : (6 * (Num / 9) + 5 - 1) / 2 = 3 * (Num / 9) + 2).
  {
     replace (6 * (Num / 9) + 5 - 1)
      with (6 * (Num / 9) +  4) by ring.    
    replace (6 * (Num / 9) + 4)
      with (2 * (3 * (Num / 9) + 2)) by ring.
    set (ONum := (3 * (Num / 9) + 2)).
    replace (2 * ONum) with (ONum * 2) by lia.
    rewrite Z.div_mul by lia.
    ring.
  }

  (* 2. tag x = 9*m + 5 *)
  assert (Htag_x : (18 * m + 6 + 5 - 1) / 2 = 9 * m + 5).
  {
    replace (18 * m + 6 + 5 - 1) with (18 * m + 10) by ring.
    replace (18 * m + 10)
      with (2 * (9 * m + 5)) by ring.
    set (Om := (9 * m + 5)).
    replace (2 * Om) with (Om * 2) by lia.
    rewrite Z.div_mul by lia.
    ring.
  }

  replace (6 * 1) with 6 by ring.

  rewrite Htag_xp, Htag_x.
  (* LHS: (3*(Num/9) + 2) - (9*m + 5) *)
  replace (3 * (Num / 9) + 2 - (9 * m + 5))
    with (3 * (Num / 9) - 9 * m - 3) by ring.
  (* Goal now:
       3 * (Num / 9) - 9 * m - 3
       = (3 * m + 1) * (2 ^ (3 + 6 * p) - 3) + (20 * ((64 ^ p - 1) / 3) + 4)
   *)  

  (* Rewrite Delta via Hq: q_p = 3*k, so Delta = 20*q_p + 4 = 60*k + 4 *)
  unfold q_p in *.
  unfold Delta, q_p, pow64 in *.
  rewrite Hq.
  replace (20 * (3 * k) + 4) with (60 * k + 4) by ring.
  (* Goal:
       3 * (Num / 9) - 9 * m - 3
       = (3 * m + 1) * (2 ^ (3 + 6 * p) - 3) + (60 * k + 4)
   *)

  (* Rewrite K via k: 2^(3+6p) = 8 * 64^p = 8 * (9*k+1) *)
  (* RHS now:
       (3 * m + 1) * (2 ^ (3 + 6 * p) - 3) + (60 * k + 4)
   *)

  (* 4. Express Num / 9 as E *)
  set (E := 72 * m * k + 44 * k + 8 * m + 4 : Z).

  assert (HNum : Num = 9 * E).
  {
    unfold Num, E.
    rewrite Hk.  (* 64^p = 9*k + 1 *)
    ring.
  }

  assert (HNum_div9 : Num / 9 = E).
  {
    rewrite HNum.
    replace (9 * E) with (E * 9) by ring.
    rewrite Z.div_mul by lia.
    reflexivity.
  }

  rewrite HNum_div9.
  (* Goal now:
       3 * E - 9 * m - 3
       = (3 * m + 1) * (2 ^ (3 + 6 * p) - 3) + (60 * k + 4)
   *)

  (* 5. Rewrite K in terms of k using 2^(3+6p) = 8*64^p *)
  unfold pow2 in *.
  repeat rewrite Z.pow_add_r by lia.
  change (2 ^ 3) with 8.

  replace (2 ^ (6 * p)) with (64 ^ p).
  2:{
    rewrite (Z.pow_mul_r 2 6 p) by lia.
    change (2 ^ 6) with 64.
    reflexivity.
  }
    (* Expand K in terms of k *)
  unfold K, pow2 in *.
  repeat rewrite Z.pow_add_r by lia.
  change (2 ^ 3) with 8.

  (* Turn 2^(6*p) into 64^p, then use Hk *)
  replace (2 ^ (6 * p)) with (64 ^ p).
  2:{
    rewrite Z.pow_mul_r by lia.
    change (2 ^ 6) with 64.
    reflexivity.
  }
  rewrite Hk.  (* now K = 8 * (9 * k + 1) - 3 *)

  (* Reduce calc_r Omega_1 m *)
  cbv [calc_r get_input_reqs] in *.
  (* after this, calc_r Omega_1 m should be 3 * m + 1 *)

  (* Everything is now a polynomial in m,k *)
  unfold E.
  ring.
Qed.

Lemma drift_equation_Omega_2 :
  forall (p m : Z),
    p >= 0 ->
    let x  := construct_x Omega_2 m in
    let xp := x_prime Omega_2 p m in
    (* Omega_2: alpha = 1, o-type -> Delta = 5*q_p - 1 *)
    let K     := pow2 (1 + 6 * p) - 3 in
    let q_p   := (pow64 p - 1) / 3 in
    let Delta := 5 * q_p - 1 in
    let predicted := (calc_r Omega_2 m) * K + Delta in
    
    tag xp - tag x = predicted.
Proof.
  intros p m Hp x xp K q_p Delta predicted.
  unfold x, xp, construct_x, x_prime, F_transform, tag,
         get_input_reqs, get_params, calc_r in *.
  cbv [alpha beta c delta get_params get_input_reqs] in *.
  (* For Omega_2 we now have:
       x  = 18*m + 12 + 5
       xp = 6 * (((9*m*2 + 17) * 64^p - 8) / 9) + 5
       calc_r Omega_2 m = 3*m + 2
       K   = pow2 (1 + 6*p) - 3
       q_p = (pow64 p - 1) / 3  (we'll unfold pow64 later)
   *)

  (* 0. Expand pow2 / pow64 in the local lets *)
  unfold pow2, pow64, K, q_p, Delta, predicted in *.
  (* Now:
       K     = 2 ^ (1 + 6 * p) - 3
       q_p   = (64 ^ p - 1) / 3
       Delta = 5 * ((64 ^ p - 1) / 3) - 1
   *)

  (* 1. Name the big numerator as Num *)
  set (Num := (9 * m * 2 + 17) * 64 ^ p + -8) in *.
  (* So xp = 6 * (Num / 9) + 5 *)

  (* 2. Compute tag xp: (xp - 1)/2 = 3*(Num/9) + 2 *)

  assert (Htag_xp : (6 * (Num / 9) + 5 - 1) / 2 = 3 * (Num / 9) + 2).
  {
    replace (6 * (Num / 9) + 5 - 1) with (6 * (Num / 9) + 4) by ring.
    replace (6 * (Num / 9) + 4)
      with (2 * (3 * (Num / 9) + 2)) by ring.
    set (ONum := (3 * (Num / 9) + 2)).
    replace (2 * ONum) with (ONum * 2) by lia.
    rewrite Z.div_mul by lia.
    ring.
  }

  (* 3. Compute tag x: (x - 1)/2 = 9*m + 8 *)
  assert (Htag_x : (18 * m + 12 + 5 - 1) / 2 = 9 * m + 8).
  {
    replace (18 * m + 12 + 5 - 1) with (18 * m + 16) by ring.
    replace (18 * m + 16)
      with (2 * (9 * m + 8)) by ring.
    set (Om := (9 * m + 8)).
    replace (2 * Om) with (Om * 2) by lia.
    rewrite Z.div_mul by lia.
    ring.
  }
    (* Normalize the xp-part to match Htag_xp *)
  replace ((6 * (((9 * m * 2 ^ 1 + 17) * 64 ^ p + -8) / 9) + 5 - 1) / 2)
    with ((6 * (Num / 9) + 5 - 1) / 2).
  2:{
    unfold Num.
    (* simplify 2^1 to 2 *)
    replace (2 ^ 1) with 2 by (compute; reflexivity).
    ring.
  }

  (* Normalize the x-part to match Htag_x *)
  replace ((18 * m + 6 * 2 + 5 - 1) / 2)
    with ((18 * m + 12 + 5 - 1) / 2).
  2:{
      replace (6 * 2) with 12 by ring.
      ring. }

  (* Now these match Htag_xp and Htag_x exactly *)
  rewrite Htag_xp, Htag_x.


  (* 4. Use tag identities in the goal *)  
  (* LHS: (3*(Num/9) + 2) - (9*m + 8) *)
  replace (3 * (Num / 9) + 2 - (9 * m + 8))
    with (3 * (Num / 9) - 9 * m - 6) by ring.
  (* Goal is now:
       3 * (Num / 9) - 9 * m - 6
       = (3 * m + 2) * (2 ^ (1 + 6 * p) - 3)
         + (5 * ((64 ^ p - 1) / 3) - 1)
   *)

  (* 5. Introduce k with 64^p = 9*k + 1 *)
  destruct (pow64_exists_k p Hp) as [k Hk].
  (* Hk : 64 ^ p = 9 * k + 1 *)

  assert (Hq : (64 ^ p - 1) / 3 = 3 * k).
  {
    rewrite Hk.
    replace (9 * k + 1 - 1) with (9 * k) by ring.
    replace (9 * k) with (3 * (3 * k)) by ring.
    replace (3 * (3 * k)) with (k * 3 * 3) by ring.
    rewrite Z.div_mul by lia.
    lia.    
  }
  unfold q_p in *.
  unfold Delta, q_p, pow64 in *.
  (* Rewrite Delta using Hq: q_p = 3*k, so Delta = 15*k - 1 *)
  rewrite Hq.
  replace (5 * (3 * k) - 1) with (15 * k - 1) by ring.
  (* Goal:
       3 * (Num / 9) - 9 * m - 6
       = (3 * m + 2) * (2 ^ (1 + 6 * p) - 3) + (15 * k - 1)
   *)

  (* 6. Express Num / 9 as an integer E *)
  set (E := 18 * m * k + 17 * k + 2 * m + 1 : Z).

  assert (HNum : Num = 9 * E).
  {
    unfold Num, E.
    rewrite Hk.  (* 64^p = 9*k + 1 *)
    ring.
  }

  assert (HNum_div9 : Num / 9 = E).
  {
    rewrite HNum.
    replace (9 * E) with (E * 9) by ring.
    rewrite Z.div_mul by lia.
    reflexivity.
  }

  rewrite HNum_div9.
  (* Goal:
       3 * E - 9 * m - 6
       = (3 * m + 2) * (2 ^ (1 + 6 * p) - 3) + (15 * k - 1)
   *)

  (* 7. Rewrite K = 2^(1+6p) - 3 in terms of k *)
  (* 2^(1+6p) = 2 * 2^(6p) = 2 * 64^p *)
  repeat rewrite Z.pow_add_r by lia.
  change (2 ^ 1) with 2.

  replace (2 ^ (6 * p)) with (64 ^ p).
  2:{
    rewrite Z.pow_mul_r by lia.
    change (2 ^ 6) with 64.
    reflexivity.
  }
  
  (* Now K = 2 * (9 * k + 1) - 3 = 18 * k - 1 *)
  (* 8. Simplify calc_r Omega_2 m and finish with ring *)
  cbv [calc_r get_input_reqs] in *.
  (* For Omega_2, calc_r = 3*m + 2 *)
  unfold E.
  (* Rewrite K in terms of k *)
  unfold K, pow2 in *.
  repeat rewrite Z.pow_add_r by lia.
  change (2 ^ 1) with 2.
  (* turn 2^(6*p) into 64^p *)
  replace (2 ^ (6 * p)) with (64 ^ p).
  2:{
    rewrite Z.pow_mul_r by lia.
    change (2 ^ 6) with 64.
    reflexivity.
  }
  rewrite Hk.  (* 64^p = 9*k + 1 *)
  (* Now K = 2 * (9*k + 1) - 3 = 18*k - 1 *)
  replace (2 * (9 * k + 1) - 3) with (18 * k - 1) by ring.
  ring.
Qed.

(** ========== Psi-family (ee) ========== *)

Lemma drift_equation_Psi_0_API :
  forall (p m : Z),
    p >= 0 ->
    let x  := construct_x Psi_0 m in
    let xp := x_prime Psi_0 p m in
    tag xp - tag x =
      calc_r Psi_0 m * (pow2 (2 + 6 * p) - 3)
      + 2 * calc_q_p p.
Proof.
  intros p m Hp x xp.
  unfold calc_q_p.
  apply drift_equation_Psi_0; assumption.
Qed.

Lemma drift_equation_Psi_1_API :
  forall (p m : Z),
    p >= 0 ->
    let x  := construct_x Psi_1 m in
    let xp := x_prime Psi_1 p m in
    tag xp - tag x =
      calc_r Psi_1 m * (pow2 (4 + 6 * p) - 3)
      + (8 * calc_q_p p + 2).
Proof.
  intros p m Hp x xp.
  unfold calc_q_p.
  apply drift_equation_Psi_1; assumption.
Qed.

Lemma drift_equation_Psi_2_API :
  forall (p m : Z),
    p >= 0 ->
    let x  := construct_x Psi_2 m in
    let xp := x_prime Psi_2 p m in
    tag xp - tag x =
      calc_r Psi_2 m * (pow2 (6 + 6 * p) - 3)
      + (32 * calc_q_p p + 10).
Proof.
  intros p m Hp x xp.
  unfold calc_q_p.
  apply drift_equation_Psi_2; assumption.
Qed.

(** ========== psi-family (eo) ========== *)

Lemma drift_equation_psi_0_API :
  forall (p m : Z),
    p >= 0 ->
    let x  := construct_x psi_0 m in
    let xp := x_prime psi_0 p m in
    tag xp - tag x =
      calc_r psi_0 m * (pow2 (4 + 6 * p) - 3)
      + (8 * calc_q_p p + 2).
Proof.
  intros p m Hp x xp.
  unfold calc_q_p.
  apply drift_equation_psi_0; assumption.
Qed.

Lemma drift_equation_psi_1_API :
  forall (p m : Z),
    p >= 0 ->
    let x  := construct_x psi_1 m in
    let xp := x_prime psi_1 p m in
    tag xp - tag x =
      calc_r psi_1 m * (pow2 (6 + 6 * p) - 3)
      + (32 * calc_q_p p + 10).
Proof.
  intros p m Hp x xp.
  unfold calc_q_p.
  apply drift_equation_psi_1; assumption.
Qed.

(* This one is the corrected one: psi_2 has Delta = 2 * q_p *)
Lemma drift_equation_psi_2_API :
  forall (p m : Z),
    p >= 0 ->
    let x  := construct_x psi_2 m in
    let xp := x_prime psi_2 p m in
    tag xp - tag x =
      calc_r psi_2 m * (pow2 (2 + 6 * p) - 3)
      + 2 * calc_q_p p.
Proof.
  intros p m Hp x xp.
  unfold calc_q_p.
  apply drift_equation_psi_2; assumption.
Qed.

(** ========== omega-family (oe) ========== *)

Lemma drift_equation_omega_0_API :
  forall (p m : Z),
    p >= 0 ->
    let x  := construct_x omega_0 m in
    let xp := x_prime omega_0 p m in
    tag xp - tag x =
      calc_r omega_0 m * (pow2 (3 + 6 * p) - 3)
      + (20 * calc_q_p p + 4).
Proof.
  intros p m Hp x xp.
  unfold calc_q_p.
  apply drift_equation_omega_0; assumption.
Qed.

Lemma drift_equation_omega_1_API :
  forall (p m : Z),
    p >= 0 ->
    let x  := construct_x omega_1 m in
    let xp := x_prime omega_1 p m in
    tag xp - tag x =
      calc_r omega_1 m * (pow2 (1 + 6 * p) - 3)
      + (5 * calc_q_p p - 1).
Proof.
  intros p m Hp x xp.
  unfold calc_q_p.
  apply drift_equation_omega_1; assumption.
Qed.

Lemma drift_equation_omega_2_API :
  forall (p m : Z),
    p >= 0 ->
    let x  := construct_x omega_2 m in
    let xp := x_prime omega_2 p m in
    tag xp - tag x =
      calc_r omega_2 m * (pow2 (5 + 6 * p) - 3)
      + (80 * calc_q_p p + 24).
Proof.
  intros p m Hp x xp.
  unfold calc_q_p.
  apply drift_equation_omega_2; assumption.
Qed.

(** ========== Omega-family (oo) ========== *)

Lemma drift_equation_Omega_0_API :
  forall (p m : Z),
    p >= 0 ->
    let x  := construct_x Omega_0 m in
    let xp := x_prime Omega_0 p m in
    tag xp - tag x =
      calc_r Omega_0 m * (pow2 (5 + 6 * p) - 3)
      + (80 * calc_q_p p + 24).
Proof.
  intros p m Hp x xp.
  unfold calc_q_p.
  apply drift_equation_Omega_0; assumption.
Qed.

Lemma drift_equation_Omega_1_API :
  forall (p m : Z),
    p >= 0 ->
    let x  := construct_x Omega_1 m in
    let xp := x_prime Omega_1 p m in
    tag xp - tag x =
      calc_r Omega_1 m * (pow2 (3 + 6 * p) - 3)
      + (20 * calc_q_p p + 4).
Proof.
  intros p m Hp x xp.
  unfold calc_q_p.
  apply drift_equation_Omega_1; assumption.
Qed.

Lemma drift_equation_Omega_2_API :
  forall (p m : Z),
    p >= 0 ->
    let x  := construct_x Omega_2 m in
    let xp := x_prime Omega_2 p m in
    tag xp - tag x =
      calc_r Omega_2 m * (pow2 (1 + 6 * p) - 3)
      + (5 * calc_q_p p - 1).
Proof.
  intros p m Hp x xp.
  unfold calc_q_p.
  apply drift_equation_Omega_2; assumption.
Qed.


Theorem diff_equation_correct :
  forall (t : Token) (p m : Z),
    p >= 0 ->
    let x  := construct_x t m in
    let xp := x_prime t p m in
    tag xp - tag x = predicted_drift t p m.
Proof.
  intros t p m Hp x xp.
  (* Open up predicted_drift so each constructor case is explicit *)
  unfold x, xp, construct_x, x_prime, F_transform, get_input_reqs, get_params, pow2, pow64 in *.  

  destruct t;
    cbn [get_params calc_K calc_q_p alpha beta c delta get_params get_input_reqs] in *.

  destruct (pow64_exists_k p Hp) as [k Hk].
  
  (* 2. Replace 64^p with (9k+1) EVERYWHERE immediately *)
  rewrite Hk in *.

   - (* Psi_0 *)
    (* Goal: tag (x_prime Psi_0 p m) - tag (construct_x Psi_0 m)
              = [formula that we already proved in drift_equation_Psi_0] *)
    match goal with | [ |- context[?N / 9] ] => set (Num := N) end.    

    assert (Hxp_Num : xp = 6 * (Num / 9) + 1).
    {
      subst xp Num.
      unfold x_prime, F_transform, get_params, get_input_reqs in *.
      cbn [alpha beta c delta pow2 pow64] in *.
      rewrite Hk.
      reflexivity.
    }

    (* Rewrite LHS into tag xp - tag x *)
    rewrite <- Hxp_Num.
    change (18 * m + 6 * 0 + 1) with x.

    (* Now use the API definition of predicted drift *)
    unfold predicted_drift, calc_K, calc_q_p, delta_drift.
    cbn [get_params alpha].
    unfold calc_q_p.

    (* And finish by the core lemma *)
    apply drift_equation_Psi_0; assumption.    

  - (* Psi_1 *)
    match goal with | [ |- context[?N / 9] ] => set (Num := N) end.
    destruct (pow64_exists_k p Hp) as [k Hk].
    assert (Hxp_Num : xp = 6 * (Num / 9) + 1).
    {
      subst xp Num.
      unfold x_prime, F_transform, get_params, get_input_reqs in *.
      cbn [alpha beta c delta pow2 pow64] in *.
      rewrite Hk.
      reflexivity.
    }

    (* Rewrite LHS into tag xp - tag x *)
    rewrite <- Hxp_Num.
    subst Num.
    change (tag (18 * m + 6 * 1 + 1)) with (tag x).
    change (tag xp - tag (18 * m + 6 * 1 + 1)) with (tag xp - tag x).

    (* Expand predicted_drift so it matches drift_equation_Psi_1’s RHS *)
    unfold predicted_drift, calc_K, delta_drift, calc_q_p.
    cbn [get_params alpha].
    unfold calc_q_p.
    (* Psi_1 branch *)

    change x  with (construct_x Psi_1 m).
    change xp with (x_prime    Psi_1 p m).
    unfold predicted_drift, calc_K, delta_drift, calc_q_p; cbn [get_params alpha].
    apply drift_equation_Psi_1_API; assumption.    

  - (* Psi_2 *)
    match goal with | [ |- context[?N / 9] ] => set (Num := N) end.
    destruct (pow64_exists_k p Hp) as [k Hk].
    assert (Hxp_Num : xp = 6 * (Num / 9) + 1).
    {
      subst xp Num.
      unfold x_prime, F_transform, get_params, get_input_reqs in *.
      cbn [alpha beta c delta pow2 pow64] in *.
      rewrite Hk.
      reflexivity.
    }
    (* 1. Relate 18*m + 6*2 + 1 to construct_x Psi_2 m *)
    assert (Hx_val : construct_x Psi_2 m = 18 * m + 6 * 2 + 1).
    {
      (* This should be just computation + ring, depending on your definition *)
      unfold construct_x, F_transform, get_params, get_input_reqs.
      cbn [alpha beta c delta pow2 pow64].
      (* You may or may not need [ring] here; often [reflexivity] is enough. *)
      reflexivity.
    }

    (* 2. Relate 6 * (Num / 9) + 1 to x_prime Psi_2 p m *)
    assert (Hxp_val : x_prime Psi_2 p m = 6 * (Num / 9) + 1).
    {
      (* This is exactly how you defined [Num] earlier *)
      unfold x_prime, F_transform, get_params, get_input_reqs in *.
      cbn [alpha beta c delta pow2 pow64] in *.
      (* if [Num] is defined as the numerator, this should be definitional: *)
      reflexivity.
    }
    (* 1. Turn 6 * (Num / 9) + 1 into xp using Hxp_Num *)
    rewrite <- Hxp_Num.
    (* Now the LHS is: tag xp - tag (18 * m + 6 * 2 + 1) *)

    (* 2. Turn 18 * m + 6 * 2 + 1 into x *)
    change (18 * m + 6 * 2 + 1) with x.
    (* Goal is now: *)
    (*   tag xp - tag x = predicted_drift Psi_2 p m *)

    (* 3. Unfold predicted_drift to expose calc_K / delta_drift *)
    unfold predicted_drift, calc_K, delta_drift, calc_q_p.
    cbn [get_params alpha].     (* makes calc_K Psi_2 p = pow2 (6 + 6 * p) - 3,
                                    and delta_drift Psi_2 p = 32 * ((pow64 p - 1)/3) + 10 *)

    (* 4. Align x and xp with construct_x / x_prime (for the API lemma) *)
    change x  with (construct_x Psi_2 m).
    change xp with (x_prime    Psi_2 p m).

    (* 5. Done: this matches drift_equation_Psi_2_API exactly *)
    apply drift_equation_Psi_2_API; assumption.

  - (* psi_0 *)
    match goal with | [ |- context[?N / 9] ] => set (Num := N) end.
    destruct (pow64_exists_k p Hp) as [k Hk].
    assert (Hxp_Num : xp = 6 * (Num / 9) + 5).
    {
      subst xp Num.
      unfold x_prime, F_transform, get_params, get_input_reqs in *.
      cbn [alpha beta c delta pow2 pow64] in *.
      rewrite Hk.
      reflexivity.
    }
    (* 1. Rewrite the explicit numerator form into [xp] *)
    rewrite <- Hxp_Num.        (* or whatever equality you have for this token *)

    (* 2. Rewrite the explicit linear form of x into [x] *)
    change (18 * m + 6*0 + 1) with x.   (* offset is 0,6,12, etc depending on token *)

    (* 3. Unfold the API and hook into the core lemma *)
    unfold predicted_drift, calc_K, delta_drift, calc_q_p.
    cbn [get_params alpha].
    unfold calc_q_p.

    change x  with (construct_x psi_0 m).
    change xp with (x_prime    psi_0 p m).
    
    apply drift_equation_psi_0_API; assumption.

  - (* psi_1 *)
    match goal with | [ |- context[?N / 9] ] => set (Num := N) end.
    destruct (pow64_exists_k p Hp) as [k Hk].
    assert (Hxp_Num : xp = 6 * (Num / 9) + 5).
    {
      subst xp Num.
      unfold x_prime, F_transform, get_params, get_input_reqs in *.
      cbn [alpha beta c delta pow2 pow64] in *.
      rewrite Hk.
      reflexivity.
    }
    (* 1. Rewrite the explicit numerator form into [xp] *)
    rewrite <- Hxp_Num.        (* or whatever equality you have for this token *)

    (* 2. Rewrite the explicit linear form of x into [x] *)
    change (18 * m + 6 + 1) with x.   (* offset is 0,6,12, etc depending on token *)

    (* 3. Unfold the API and hook into the core lemma *)
    unfold predicted_drift, calc_K, delta_drift, calc_q_p.
    cbn [get_params alpha].
    unfold calc_q_p.

    change x  with (construct_x psi_1 m).
    change xp with (x_prime    psi_1 p m).
    apply drift_equation_psi_1_API; assumption.
  - (* psi_2 *)
    match goal with | [ |- context[?N / 9] ] => set (Num := N) end.
    destruct (pow64_exists_k p Hp) as [k Hk].
    assert (Hxp_Num : xp = 6 * (Num / 9) + 5).
    {
      subst xp Num.
      unfold x_prime, F_transform, get_params, get_input_reqs in *.
      cbn [alpha beta c delta pow2 pow64] in *.
      rewrite Hk.
      reflexivity.
    }
    (* 1. Rewrite the explicit numerator form into [xp] *)
    rewrite <- Hxp_Num.        (* or whatever equality you have for this token *)

    (* 2. Rewrite the explicit linear form of x into [x] *)
    change (18 * m + 12 + 1) with x.   (* offset is 0,6,12, etc depending on token *)

    (* 3. Unfold the API and hook into the core lemma *)
    unfold predicted_drift, calc_K, delta_drift, calc_q_p.
    cbn [get_params alpha].
    unfold calc_q_p.

    change x  with (construct_x psi_2 m).
    change xp with (x_prime    psi_2 p m).
    apply drift_equation_psi_2_API; assumption.

  - (* omega_0 *)
    match goal with | [ |- context[?N / 9] ] => set (Num := N) end.
    destruct (pow64_exists_k p Hp) as [k Hk].
    assert (Hxp_Num : xp = 6 * (Num / 9) + 1).
    {
      subst xp Num.
      unfold x_prime, F_transform, get_params, get_input_reqs in *.
      cbn [alpha beta c delta pow2 pow64] in *.
      rewrite Hk.      
      reflexivity.
    }
    (* 1. Rewrite the explicit numerator form into [xp] *)
    rewrite <- Hxp_Num.        (* or whatever equality you have for this token *)

    (* 2. Rewrite the explicit linear form of x into [x] *)
    change (18 * m + 0 + 1) with x.   (* offset is 0,6,12, etc depending on token *)

    (* 3. Unfold the API and hook into the core lemma *)
    unfold predicted_drift, calc_K, delta_drift, calc_q_p.
    cbn [get_params alpha].
    unfold calc_q_p.

    change x  with (construct_x omega_0 m).
    change xp with (x_prime    omega_0 p m).
    apply drift_equation_omega_0_API; assumption.
  - (* omega_1 *)
    match goal with | [ |- context[?N / 9] ] => set (Num := N) end.
    destruct (pow64_exists_k p Hp) as [k Hk].
    assert (Hxp_Num : xp = 6 * (Num / 9) + 1).
    {
      subst xp Num.
      unfold x_prime, F_transform, get_params, get_input_reqs in *.
      cbn [alpha beta c delta pow2 pow64] in *.
      rewrite Hk.
      reflexivity.
    }
    (* 1. Rewrite the explicit numerator form into [xp] *)
    rewrite <- Hxp_Num.        (* or whatever equality you have for this token *)

    (* 2. Rewrite the explicit linear form of x into [x] *)
    change (18 * m + 6 + 1) with x.   (* offset is 0,6,12, etc depending on token *)

    (* 3. Unfold the API and hook into the core lemma *)
    unfold predicted_drift, calc_K, delta_drift, calc_q_p.
    cbn [get_params alpha].
    unfold calc_q_p.

    change x  with (construct_x omega_1 m).
    change xp with (x_prime    omega_1 p m).
    apply drift_equation_omega_1_API; assumption.

  - (* omega_2 *)
    match goal with | [ |- context[?N / 9] ] => set (Num := N) end.
    destruct (pow64_exists_k p Hp) as [k Hk].
    assert (Hxp_Num : xp = 6 * (Num / 9) + 1).
    {
      subst xp Num.
      unfold x_prime, F_transform, get_params, get_input_reqs in *.
      cbn [alpha beta c delta pow2 pow64] in *.
      rewrite Hk.
      reflexivity.
    }
    (* 1. Rewrite the explicit numerator form into [xp] *)
    rewrite <- Hxp_Num.        (* or whatever equality you have for this token *)

    (* 2. Rewrite the explicit linear form of x into [x] *)
    change (18 * m + 12 + 1) with x.   (* offset is 0,6,12, etc depending on token *)

    (* 3. Unfold the API and hook into the core lemma *)
    unfold predicted_drift, calc_K, delta_drift, calc_q_p.
    cbn [get_params alpha].
    unfold calc_q_p.

    change x  with (construct_x omega_2 m).
    change xp with (x_prime    omega_2 p m).
    apply drift_equation_omega_2_API; assumption.
  - (* Omega_0 *)
    match goal with | [ |- context[?N / 9] ] => set (Num := N) end.
    destruct (pow64_exists_k p Hp) as [k Hk].
    assert (Hxp_Num : xp = 6 * (Num / 9) + 5).
    {
      subst xp Num.
      unfold x_prime, F_transform, get_params, get_input_reqs in *.
      cbn [alpha beta c delta pow2 pow64] in *.
      rewrite Hk.
      reflexivity.
    }
    (* 1. Rewrite the explicit numerator form into [xp] *)
    rewrite <- Hxp_Num.        (* or whatever equality you have for this token *)

    (* 2. Rewrite the explicit linear form of x into [x] *)
    change (18 * m + 0 + 1) with x.   (* offset is 0,6,12, etc depending on token *)

    (* 3. Unfold the API and hook into the core lemma *)
    unfold predicted_drift, calc_K, delta_drift, calc_q_p.
    cbn [get_params alpha].
    unfold calc_q_p.

    change x  with (construct_x Omega_0 m).
    change xp with (x_prime    Omega_0 p m).
    apply drift_equation_Omega_0_API; assumption.

  - (* Omega_1 *)
    match goal with | [ |- context[?N / 9] ] => set (Num := N) end.
    destruct (pow64_exists_k p Hp) as [k Hk].
    assert (Hxp_Num : xp = 6 * (Num / 9) + 5).
    {
      subst xp Num.
      unfold x_prime, F_transform, get_params, get_input_reqs in *.
      cbn [alpha beta c delta pow2 pow64] in *.
      rewrite Hk.
      reflexivity.
    }
    (* 1. Rewrite the explicit numerator form into [xp] *)
    rewrite <- Hxp_Num.        (* or whatever equality you have for this token *)

    (* 2. Rewrite the explicit linear form of x into [x] *)
    change (18 * m + 6 + 1) with x.   (* offset is 0,6,12, etc depending on token *)

    (* 3. Unfold the API and hook into the core lemma *)
    unfold predicted_drift, calc_K, delta_drift, calc_q_p.
    cbn [get_params alpha].
    unfold calc_q_p.

    change x  with (construct_x Omega_1 m).
    change xp with (x_prime    Omega_1 p m).
    apply drift_equation_Omega_1_API; assumption.
  - (* Omega_2 *)
    match goal with | [ |- context[?N / 9] ] => set (Num := N) end.
    destruct (pow64_exists_k p Hp) as [k Hk].
    assert (Hxp_Num : xp = 6 * (Num / 9) + 5).
    {
      subst xp Num.
      unfold x_prime, F_transform, get_params, get_input_reqs in *.
      cbn [alpha beta c delta pow2 pow64] in *.
      rewrite Hk.
      reflexivity.      
    }
    (* 1. Rewrite the explicit numerator form into [xp] *)
    rewrite <- Hxp_Num.        (* or whatever equality you have for this token *)

    (* 2. Rewrite the explicit linear form of x into [x] *)
    change (18 * m + 12 + 1) with x.   (* offset is 0,6,12, etc depending on token *)

    (* 3. Unfold the API and hook into the core lemma *)
    unfold predicted_drift, calc_K, delta_drift, calc_q_p.
    cbn [get_params alpha].
    unfold calc_q_p.

    change x  with (construct_x Omega_2 m).
    change xp with (x_prime    Omega_2 p m).
    apply drift_equation_Omega_2_API; assumption.
Qed.
    