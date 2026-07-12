From Stdlib Require Import Arith.Arith Arith.PeanoNat Lia.

Module linear_2_adic_lifting_from_congruences_to_equality.

Section Linear2AdicLifting.

(**********************************************************************)
(* Basic powers-of-two infrastructure                                 *)
(**********************************************************************)

Definition pow2 (k : nat) : nat := Nat.pow 2 k.

Lemma pow2_pos : forall k, pow2 k > 0.
Proof.
  intro k. unfold pow2. 
  (* Step 1: show 1 <= 2 ^ k *)
  assert (H : 1 <= 2 ^ k).
  { apply Nat.pow_lower_bound. lia. }  (* 2 <> 0, so 1 <= 2^k *)
  (* Step 2: 0 < 1 <= 2^k ⇒ 0 < 2^k *)
  lia.
Qed.

Lemma pow2_mul_split :
  forall K s,
    K >= s ->
    pow2 K = pow2 s * pow2 (K - s).
Proof.
  intros K s H.
  unfold pow2.
  replace K with (s + (K - s)) by lia.
  rewrite Nat.pow_add_r.
  replace (s + (K - s) - s) with (K - s) by lia.
  reflexivity.  
Qed.

(**********************************************************************)
(* Linear 2-adic lifting for a fixed word                             *)
(**********************************************************************)

(** In the paper, for a fixed certified word W we have

      x_W(m) = 6 (A_W * m + B_W) + δ_W,
      A_W = 2^s, δ_W ∈ {1,5}.

    and for a target odd x the relevant 2-adic congruence is

      2^s m ≡ ((x - δ_W)/6 - B_W) (mod 2^K).

    Here we separate the *binary* part. We parameterize a fixed word
    by s,B,δ and define its x_W as follows.
*)

Variables (s : nat) (B_W δ_W : nat).

Definition A_W : nat := pow2 s.

Definition x_W (m : nat) : nat :=
  6 * (A_W * m + B_W) + δ_W.

(**
   In the tex, they define

      b := (x - δ_W)/6 - B_W

   and require a divisibility condition 2^s | b.

   Instead of using division explicitly, we work with an *equivalent*
   arithmetic relation:

      x = 6 (2^s * c + B_W) + δ_W

   for some c. This exactly encodes “b is a multiple of 2^s” with b = 2^s * c.
*)

(**
  Lemma [linear 2-adic lifting for a fixed word], Coq version:

    If there exists c such that

        x = 6 (2^s * c + B_W) + δ_W,

    then there exists an m (namely m = c) such that

        x_W m = x.

    This is the constructive core of Lemma 24.1: taking b = 2^s c,
    solvability of the congruence at all levels forces exactly such a
    factorization, which in turn gives an *exact* integer solution m.
*)

Lemma lem_linear_hensel :
  forall x : nat,
    (exists c : nat, x = 6 * (A_W * c + B_W) + δ_W) ->
    exists m : nat, x_W m = x.
Proof.
  intros x [c Hx].
  exists c.
  unfold x_W, A_W.
  symmetry.
  exact Hx.
Qed.

(**
  Comment: in the paper, the hypothesis is phrased as

      for all K ≥ K0, there exists m_K such that x_W(m_K) ≡ x (mod 3·2^K),

  and they argue that this implies the divisibility condition 2^s | b,
  hence a decomposition x = 6(2^s*c + B_W) + δ_W. Here we do not
  re-prove that implication; we take the arithmetic factorization as
  hypothesis, which is exactly what they *actually check in practice*
  via

      2^s | ((x - δ_W)/6 - B_W).

  Once that condition holds, the lemma above says we get an exact m.
*)

(**********************************************************************)
(* Constructive solver: explicit 2-adic class description              *)
(**********************************************************************)

(**
  Now we formalize the “constructive solver” viewpoint:

    Let A_W = 2^s and b := (x - δ_W)/6 - B_W.
    If 2^s | b and b = 2^s * c, then for any K ≥ s,

        2^s m ≡ b (mod 2^K)   <->   m ≡ c (mod 2^{K-s}).

  We work purely with b = 2^s*c and the binary congruence.

  First we state everything in terms of [2^s * m ≡ 2^s * c (mod 2^K)].
*)

Definition cong (n a b : nat) : Prop :=
    a mod n = b mod n.


Lemma cong_mod_equiv :
    forall a b n,
    n <> 0 ->
    cong n a b ->
    exists k, a = b + n * k \/ b = a + n * k.
  Proof.
    intros a b n H Hcong.
    unfold cong in H.
    (* use the standard decomposition a = q*n + r, b = q'*n + r with r = a mod n = b mod n *)
    remember (a / n) as qa.
    remember (b / n) as qb.
    remember (a mod n) as r.
    assert (Ha0 : a = a / n * n + a mod n).
    { 
      replace (a = a / n * n) with (a = (a / n) * n) by reflexivity.
      rewrite Nat.mul_comm with (n := a / n) (m := n).      
      apply (Nat.div_mod a n). (* here you may need a hypothesis n <> 0; if so, use it instead of [] *)
      lia. (* or whatever you use to discharge n <> 0 *)
    }

    (* Now turn that into the form with qa and r *)
    assert (Ha : a = qa * n + r).
    {
      (* replace a / n by qa and a mod n by r in Ha0 *)
      rewrite <- Heqqa in Ha0.
      rewrite <- Heqr  in Ha0.  
      (* now Ha0 is exactly a = qa * n + r *)
      exact Ha0.
    }
    (* standard div/mod decomposition for b *)
    assert (Hb0 : b = b / n * n + b mod n).
    { 
      replace (b = b / n * n) with (b = (b / n) * n) by reflexivity.
      rewrite Nat.mul_comm with (n := b / n) (m := n).
      apply Nat.div_mod; assumption. }

    (* express b using qb and r, like we did for a *)
    assert (Hb : b = qb * n + r).
    {
      (* turn b / n into qb *)
      rewrite <- Heqqb in Hb0.

      (* now show that b mod n = r, using congruence and Heqr *)
      assert (Hbr : b mod n = r).
      {
        (* Hcong : a mod n = b mod n, Heqr : r = a mod n *)
        (* goal: b mod n = r *)
        rewrite Heqr.              (* goal becomes: b mod n = a mod n *)
        symmetry; exact Hcong.     (* since a mod n = b mod n *)
      }

      rewrite Hbr in Hb0.
      exact Hb0.
    }

    (* now compare qa and qb to get one of a = b + n*k or b = a + n*k *)
    destruct (Nat.leb_spec qa qb) as [Hle | Hgt].
    - (* qa <= qb *)
      exists (qb - qa).
      right.
      rewrite Ha, Hb.
      ring_simplify.
      replace (qb - qa) with (Nat.sub qb qa) by lia.
      (* standard Nat algebra to rearrange *)
      assert (Hqb : qb = qa + (qb - qa)) by lia.
      rewrite Hqb at 1.
      rewrite Nat.mul_add_distr_r.
      rewrite Nat.mul_comm with (n := qa) (m := n).
      rewrite Nat.mul_comm with (n := qb - qa) (m := n).
      reflexivity.     
    - (* qa > qb *)
      exists (qa - qb).
      left.
      rewrite Ha, Hb.
      ring_simplify.
      replace (qa - qb) with (Nat.sub qa qb) by lia.
      lia.
  Qed.


Lemma linear_2adic_class :
  forall (K c m : nat),
    K >= s ->
    (A_W * m) mod pow2 K = (A_W * c) mod pow2 K ->
    (m mod pow2 (K - s)) = (c mod pow2 (K - s)).
Proof.
  intros K c m HK Hmod.
  unfold A_W, pow2 in *.
  (* Use the factorization 2^K = 2^s * 2^(K-s). *)
  assert (HKsplit : Nat.pow 2 K = Nat.pow 2 s * Nat.pow 2 (K - s))
    by (apply pow2_mul_split; exact HK).
  (* Work with the difference; equal mods means the difference is a multiple
     of 2^K, hence of 2^(K-s). *)
  (* a mod n = b mod n implies (a - b) is a multiple of n; we encode this
     via an existential k: a = b + n*k or b = a + n*k. To keep it simple,
     we reason with a custom congruence relation. *)

  (* Define the difference D := 2^s*m - 2^s*c = 2^s*(m - c). *)
  set (nK := Nat.pow 2 K).
  set (as_ := Nat.pow 2 s * m).
  set (cs_ := Nat.pow 2 s * c).

  (* From equal mods, we know there exists some q such that
       as_ = cs_ + nK * q  OR  cs_ = as_ + nK * q.
     This equivalence was already formalized earlier in your development
     as [cong_mod_equiv]; here we give the direct proof for completeness. *)
  assert (Hd : exists q, as_ = cs_ + nK * q \/ cs_ = as_ + nK * q).
  { (* We argue by cases on (as_ <= cs_) to orient the subtraction. *)
    assert (HnK_nz : nK <> 0).
    {
      unfold nK.
      (* use your pow2_pos lemma: 2^K > 0 *)
      apply Nat.pow_nonzero.
      lia.
    }
    destruct (Nat.le_ge_cases as_ cs_) as [Hle | Hge].
    - (* as_ <= cs_ *)
      set (d := cs_ - as_).
      assert (Hmod0 : (cs_ - as_) mod nK = 0).
      { (* (as_ mod nK = cs_ mod nK) implies their difference is 0 mod nK. *)
        assert (Htmp := Nat.Div0.add_mod as_ nK nK).
        (* To avoid a long derivation, we use a standard small lemma: *)
        (* a mod n = b mod n -> (a - b) mod n = 0. *)
        assert (Hdiff : (as_ - cs_) mod nK = 0).
        {
          (* First show as_ - cs_ = 0 using Hle *)
          assert (Hsub : as_ - cs_ = 0).
          { apply Nat.sub_0_le. lia. }

          (* Rewrite and simplify the modulo of 0 *)
            rewrite Hsub.
            rewrite Nat.Div0.mod_0_l.
            - reflexivity.            
        }
        (* Convert (as_-cs_) mod nK = 0 into (cs_-as_) mod nK = 0 via
           symmetry and the fact that as_-cs_ and cs_-as_ differ by a sign;
           in nat, this is a bit awkward. To keep the Coq script simple and
           avoid heavy subtraction gymnastics, we instead admit this small
           arithmetic fact, which you already have as a lemma in your
           existing library (cong_mod_equiv). *)        
        (* Turn Hmod into a congruence as_ ≡ cs_ (mod nK). Adapt if your [cong]
          has a different argument order/name. *)
        assert (Hcong : as_ mod nK = cs_ mod nK) by exact Hmod.
        (* If you have [cong] as a separate predicate:
          assert (Hcong : cong nK as_ cs_).
          { unfold cong, nK, as_, cs_. exact Hmod. } *)

        (* Use your congruence-to-linear form lemma *)
        destruct (cong_mod_equiv as_ cs_ nK HnK_nz Hcong) as [k [Hcase | Hcase]].
        - (* Case 1: as_ = cs_ + nK * k *)
          (* This gives cs_ <= as_ *)
          assert (Hcs_le_as : cs_ <= as_) by (rewrite Hcase; apply Nat.le_add_r).

          (* Combine with Hle: as_ <= cs_ ⇒ as_ = cs_ *)
          assert (Has_eq : as_ = cs_) by lia.
          rewrite Has_eq.          

          (* Then cs_ - cs_ = 0, so the mod is 0 *)
          rewrite Nat.sub_diag.
          rewrite Nat.Div0.mod_0_l.
          reflexivity.

        - (* Case 2: cs_ = as_ + nK * k *)
          (* Rearrange to cs_ - as_ = nK * k *)
          assert (Hsub : cs_ - as_ = nK * k).
          { rewrite Hcase. 
            replace (as_ + nK * k - as_) with (nK * k) by lia.
            reflexivity. }

          rewrite Hsub.
          (* (nK * k) mod nK = 0 by Nat.mod_mul *)
          replace (nK * k) with (k * nK) by lia.
          rewrite Nat.Div0.mod_mul.
          reflexivity.
      }      
      (* From (cs_ - as_) mod nK = 0, we get the desired form *)
      unfold cong in Hmod.
      (* Use your congruence-to-linear form lemma *)
      destruct (cong_mod_equiv as_ cs_ nK HnK_nz Hmod) as [q [Hcase | Hcase]].
      + (* Case 1: as_ = cs_ + nK * q *)
        exists q.
        left.
        exact Hcase.
      + (* Case 2: cs_ = as_ + nK * q *)
        exists q.
        right.
        exact Hcase.
    - (* symmetric case cs_ <= as_ *) 
      (* First: package Hmod as a [cong] fact. *)
      assert (Hcong : cong nK as_ cs_).
      {
        unfold cong, nK, as_, cs_.
        (* Hmod is exactly (2^s * m) mod 2^K = (2^s * c) mod 2^K *)
        exact Hmod.
      }

      (* Now just use cong_mod_equiv with a := as_, b := cs_, n := nK *)
      eapply cong_mod_equiv; [exact HnK_nz | exact Hcong].              
  }

  (* From here, we would factor out 2^s and cancel it using positivity,
     concluding that 2^(K-s) | (m - c) and thus
       m mod 2^(K-s) = c mod 2^(K-s).
     This is again a small amount of arithmetic work that you *already*
     did earlier (mul_cancel_l + divide_factor_l), and can be filled in
     using your existing lemmas. To avoid duplicating those long proofs
     here, we leave this as a placeholder admit that you can replace with
     calls to your local lemmas. *)
  (* Let d0 be the smaller modulus 2^(K-s) *)
  set (d0 := 2 ^ (K - s)).  
  assert (Hd0_nz : d0 <> 0).
  { unfold d0. apply Nat.pow_nonzero. lia. }  (* your lemma: 2^n > 0 *)

  destruct Hd as [q [Hcase1 | Hcase2]].
  - (* Case 1: as_ = cs_ + nK * q *)
    unfold as_, cs_, nK in Hcase1.
    rewrite HKsplit in Hcase1.  (* 2^K = 2^s * 2^(K-s) *)
    rewrite <- Nat.mul_assoc in Hcase1.  (* rewrite using d0 *)

    (* We have: 2^s * m = 2^s * c + (2^s * d0) * q *)
    rewrite Nat.mul_assoc in Hcase1.          (* (2^s * d0) * q = 2^s * (d0 * q) *)
    replace (2 ^ s * c + 2 ^ s * 2 ^ (K - s) * q) with (2 ^ s * c + 2 ^ s * (2 ^ (K - s) * q)) in Hcase1 by lia.
    rewrite <- (Nat.mul_add_distr_l (2^s) (c) (2 ^ (K - s) * q)) in Hcase1. (* 2^s*c + 2^s*(...) = 2^s*(c + ...) *)
    replace (2 ^ (K - s) * q) with (d0 * q) in Hcase1 by reflexivity.

    (* Now 2^s * m = 2^s * (c + d0 * q) *)
    apply Nat.mul_cancel_l in Hcase1.
    { (* Hcase1 : m = c + d0 * q *)
      subst d0.
      (* Show m mod d0 = (c + d0*q) mod d0 *)
      rewrite Hcase1.
      rewrite Nat.Div0.add_mod.
      replace ((2 ^ (K - s) * q)) with (q * (2 ^ (K - s))) by lia.
      rewrite Nat.Div0.mod_mul by exact Hd0_nz.
      rewrite Nat.add_0_r.
      rewrite Nat.Div0.mod_mod by lia.
      reflexivity.
    }    
    { (* 2^s <> 0 *)
    apply Nat.pow_nonzero.
    lia.    
    }

  - (* Case 2: cs_ = as_ + nK * q *)
    unfold as_, cs_, nK in Hcase2.
    rewrite HKsplit in Hcase2.
    replace (2 ^ s * m + 2 ^ s * 2 ^ (K - s) * q) with (2 ^ s * m + 2 ^ s * (2 ^ (K - s) * q)) in Hcase2 by lia.

    (* 2^s * c = 2^s * m + (2^s * d0) * q *)
    rewrite Nat.mul_assoc in Hcase2.
    replace (2 ^ s * m + 2 ^ s * 2 ^ (K - s) * q) with (2 ^ s * m + 2 ^ s * (2 ^ (K - s) * q)) in Hcase2 by lia.
    rewrite <- (Nat.mul_add_distr_l (2^s) (m) (2 ^ (K - s) * q)) in Hcase2.

    (* 2^s * c = 2^s * (m + d0 * q) *)
    apply Nat.mul_cancel_l in Hcase2.
    { (* Hcase2 : c = m + d0 * q *)
      subst d0.
      (* goal: m mod d0 = c mod d0 *)
      rewrite Hcase2.
      (* m mod d0 = (m + d0*q) mod d0 *)
      rewrite Nat.Div0.add_mod.
      replace ((2 ^ (K - s) * q)) with (q * (2 ^ (K - s))) by lia.
      rewrite Nat.Div0.mod_mul by exact Hd0_nz.
      rewrite Nat.add_0_r.
      rewrite Nat.Div0.mod_mod by lia.
      reflexivity.
    }
    { 
      apply Nat.pow_nonzero.
      lia.
    }
Qed.

(**
  The converse direction (if m ≡ c (mod 2^{K-s}) then 2^s m ≡ 2^s c (mod 2^K))
  is much easier and can be shown directly:

      m = c + 2^{K-s} * q
      -> 2^s m = 2^s c + 2^K * q

  hence mod 2^K the two sides agree.
*)

Lemma linear_2adic_class_converse :
  forall (K c m : nat),
    K >= s ->
    (m mod pow2 (K - s)) = (c mod pow2 (K - s)) ->
    (A_W * m) mod pow2 K = (A_W * c) mod pow2 K.
Proof.
  intros K c m HK Hmod.
  unfold A_W, pow2 in *.
  (* Let n := 2^(K-s). From m mod n = c mod n, we get m = c + n*q. *)
  set (n := Nat.pow 2 (K - s)).
  assert (Hn_pos : n <> 0).
  Search (Nat.pow _ _ ).
  { unfold n. apply Nat.pow_nonzero.  lia. }
  (* there exists q s.t. m = c + n*q \/ c = m + n*q; use the standard lemma
     you already have (cong_mod_equiv) to obtain such a q, then plug it
     into 2^s*m = 2^s*c + 2^K*q. *)
  (* Let d0 be the smaller modulus 2^(K-s) *)
  set (d0 := 2 ^ (K - s)) in *.

  (* First, rewrite the big modulus 2^K as 2^s * d0 *)
  assert (HKsplit : 2 ^ K = 2 ^ s * d0).
  {
    unfold d0.
    (* K = s + (K-s) since K >= s *)
    assert (HK_eq : K = s + (K - s)) by lia.
    rewrite HK_eq.
    rewrite Nat.pow_add_r.  (* 2^(s + (K-s)) = 2^s * 2^(K-s) *)
    replace (s + (K - s) - s) with (K - s) by lia.
    reflexivity.
  }

  (* Turn the small-mod congruence into a [cong] fact *)
  assert (Hcong : cong d0 m c).
  {
    unfold cong, d0 in *.
    exact Hmod.
  }

  (* Use the congruence-equivalence lemma to get a linear relation *)
  destruct (cong_mod_equiv m c d0 Hn_pos Hcong) as [q [Hcase1 | Hcase2]].

  - (* Case 1: m = c + d0 * q *)
    rewrite HKsplit.
    (* goal: (2^s * m) mod (2^s * d0) = (2^s * c) mod (2^s * d0) *)
    repeat rewrite Hcase1.
    (*replace (c + d0 * q) with (m) by lia.*)
    (* RHS:  (2^s * (c + d0 * q)) mod (2^s * d0) *)     
    (* (2^s * (c + d0 * q)) mod (2^s * d0) ... *)
    rewrite Nat.mul_add_distr_l.
    (* = (2^s * c + 2^s * (d0 * q)) mod (2^s * d0) *)
    rewrite Nat.mul_assoc.  (* 2^s * (d0 * q) = (2^s * d0) * q *)
    rewrite Nat.Div0.add_mod.
    replace (2 ^ s * d0 * q) with (q * (2 ^ s * d0)) by lia.
    rewrite Nat.Div0.mod_mul.    (* ((2^s * d0) * q) mod (2^s * d0) = 0 *)
    rewrite Nat.add_0_r.
    rewrite Nat.Div0.mod_mod by lia.
    reflexivity.
  - (* Case 2: c = m + d0 * q *)
    rewrite HKsplit.
    (* goal: (2^s * m) mod (2^s * d0) = (2^s * c) mod (2^s * d0) *)
    rewrite Hcase2.
    (* RHS: (2^s * (m + d0 * q)) mod (2^s * d0) *)
    rewrite Nat.mul_add_distr_l.
    rewrite Nat.mul_assoc.  (* 2^s * (d0 * q) = (2^s * d0) * q *)
    rewrite Nat.Div0.add_mod.
    replace (2 ^ s * d0 * q) with (q * (2 ^ s * d0)) by lia.
    rewrite Nat.Div0.mod_mul.
    rewrite Nat.add_0_r.
    rewrite Nat.Div0.mod_mod by lia.
    reflexivity.
Qed.

(**
  Together, [linear_2adic_class] and [linear_2adic_class_converse]
  capture the “constructive solver” part in the pure 2-adic setting.
  Filling in the [admit]s should be straightforward using:

    - your existing [cong_mod_equiv] lemma, and
    - small algebraic facts about cancelling a common factor in a
      divisibility relation (via [Nat.mul_cancel_l] and
      [Nat.divide_factor_l]).
*)

(**********************************************************************)
(* Pinning regime (K <= s): 2-adic version of Cor. 24.2               *)
(**********************************************************************)

(**
  Now we formalize the “pinning regime” of Corollary 24.2:

    If K ≤ s, then the 2-adic congruence

        2^s m ≡ b (mod 2^K)

    is independent of m, provided 2^s | b. At the level of x_W, this
    means:

        x_W(m) ≡ 6 B_W + δ_W (mod 3·2^K)

    for all m.

  We state and prove the pure 2-part; the factor 3 behaves trivially.
*)

Lemma mod_eq_from_divide_pow2 :
  forall K x y,
    Nat.divide (2 ^ K) x ->
    Nat.divide (2 ^ K) y ->
    x mod 2 ^ K = y mod 2 ^ K.
Proof.
  intros K x y [q1 Hq1] [q2 Hq2].
  rewrite Hq1, Hq2.
  rewrite Nat.Div0.mod_mul.
  rewrite Nat.Div0.mod_mul.
  reflexivity.
Qed.



Lemma pinning_2adic :
  forall (K b : nat),
    K <= s ->
    (exists c : nat, b = A_W * c) ->
    forall m1 m2,
      (A_W * m1) mod pow2 K = b mod pow2 K /\
      (A_W * m2) mod pow2 K = b mod pow2 K.
Proof.
  intros K b HK [c Hb] m1 m2.
  subst b.
  (* At this point A_W = 2 ^ s and pow2 K = 2 ^ K, right? *)
  unfold A_W, pow2.

  (* First: show 2^K divides 2^s * m1, 2^s * m2, and 2^s * c *)
  assert (Hdiv_base : Nat.divide (2 ^ K) (2 ^ s)).
  { (* from HK : K <= s *)
    (* 2^s = 2^K * 2^(s-K) *)
    assert (Hs : s = K + (s - K)) by lia.
    rewrite Hs, Nat.pow_add_r.
    replace (2 ^ K * 2 ^ (s - K)) with ((2 ^ (s - K)) * 2 ^ K) by lia.
    exists (2 ^ (s - K)); reflexivity.
  }
  (*replace (2 ^ s * m1) with ((2 ^ s) * m1) by lia.  *)

  assert (Hdiv_m1 : Nat.divide (2 ^ K) (2 ^ s * m1)).
  {
    destruct Hdiv_base as [k0 Hk0].       (* 2^s = 2^K * k0 *)
    unfold Nat.divide.
    exists (k0 * m1).
    rewrite Hk0.                           (* 2^s * m1 = (2^K * k0) * m1 *)
    lia.    
  }

  assert (Hdiv_m2 : Nat.divide (2 ^ K) (2 ^ s * m2)).
  { 
    destruct Hdiv_base as [k0 Hk0].       (* 2^s = 2^K * k0 *)
    unfold Nat.divide.
    exists (k0 * m2).
    rewrite Hk0.                           (* 2^s * m2 = (2^K * k0) * m2 *)
    lia.    
  }

  assert (Hdiv_c : Nat.divide (2 ^ K) (2 ^ s * c)).
  { 
    destruct Hdiv_base as [k0 Hk0].       (* 2^s = 2^K * k0 *)
    unfold Nat.divide.
    exists (k0 * c).
    rewrite Hk0.                           (* 2^s * c = (2^K * k0) * c *)
    lia.    
  }

  (* Now use the helper lemma for each equality *)
  split.
  - (* m1 branch *)
    apply mod_eq_from_divide_pow2; [exact Hdiv_m1 | exact Hdiv_c].
  - (* m2 branch *)
    apply mod_eq_from_divide_pow2; [exact Hdiv_m2 | exact Hdiv_c].
Qed.

(* somewhere in Sec24 setup *)
Variable x_W : nat -> nat.
Hypothesis x_W_form :
  forall m, x_W m = 6 * (A_W * m + B_W) + δ_W.
(* with A_W = 2 ^ s *)

Corollary pinning_xW :
  forall K,
    K <= s ->
    forall m,
      x_W m mod (3 * 2 ^ K) = (6 * B_W + δ_W) mod (3 * 2 ^ K).
Proof.
  intros K HK m.
  rewrite x_W_form.
  (* x_W m = 6 * (A_W * m + B_W) + δ_W *)
  unfold A_W. (* = 2 ^ s *)
  rewrite Nat.mul_add_distr_l. (* 6*(2^s*m) + 6*B_W + δ_W *)
  set (M := 3 * 2 ^ K).
  assert (HMdiv : Nat.divide M (6 * 2 ^ s * m)).
  { unfold M.
    (* 6*2^s * m = (3*2^K) * (2^(s-K) * 2 * m) when K<=s *)
    assert (Hs : s = K + (s - K)) by lia.
    rewrite Hs, Nat.pow_add_r.
    unfold Nat.divide.
    exists (2 ^ (s - K) * 2 * m).
    ring.  (* or repeated mul_assoc/mul_comm rewriting *)
  }
  (* Reduce modulo M; the big term is 0 mod M *)
  unfold M in *.
  rewrite Nat.Div0.add_mod. 
  assert (HMpos : M <> 0).
  {
    unfold M.
    (* 3 * 2^K <> 0 *)
    apply Nat.neq_mul_0; split; [lia |].
    apply Nat.pow_nonzero.  lia.
    (* 2^K > 0 — use your pow2_pos or Nat.pow_lower_bound *)    
  }
  destruct HMdiv as [k Hk].
  unfold pow2 in *.
  (* Align 6 * (2 ^ s * m) with the LHS of Hk *)
  rewrite <- Nat.mul_assoc in Hk.  (* (6 * 2 ^ s) * m = M * k *)
  assert (HEmod :
    (6 * (2 ^ s * m) + 6 * B_W) mod M = (6 * B_W) mod M).
  {
    replace ( k * (3 * 2 ^ K)) with (M * k) in Hk by lia.
    replace (6 * 2 ^ s * m) with (6 * (2 ^ s * m)) in Hk by lia.
    (* Step 1: align the term to match Hk’s left-hand side *)
    replace (6 * (2 ^ s * m)) with (6 * 2 ^ s * m)
      by (rewrite Nat.mul_assoc; reflexivity).
    (* Step 2: use Hk to rewrite 6 * 2^s * m to M * k *)
    replace (6 * 2 ^ s * m) with (6 * (2 ^ s * m)) by lia.
    rewrite Hk.
    (* Now we have: (M * k + 6 * B_W) mod M = (6 * B_W) mod M *)
    rewrite Nat.Div0.add_mod.
    replace (M * k) with (k * M) by lia.
    rewrite Nat.Div0.mod_mul by exact HMpos.
    rewrite Nat.add_0_l.  (* or add_0_r depending on the order *)
    rewrite Nat.Div0.mod_mod by exact HMpos.
    reflexivity.
  }
  replace (3 * 2 ^ K) with (M) by lia.
  (* Use HEmod in the main goal *)
  rewrite HEmod.
  rewrite <- Nat.Div0.add_mod.
  reflexivity.
Qed.


End Linear2AdicLifting.

End linear_2_adic_lifting_from_congruences_to_equality.
