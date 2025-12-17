From Coq Require Import Arith.Arith Arith.PeanoNat Lia.
From Coq Require Import ZArith.
Open Scope Z_scope.

Module Appendix_E_Identity_Derivation.
(**
  Appendix E: Derivation of the identity 3 x'_p + 1 = 2^{alpha+6p} x.

  This module formally proves the algebraic identity that underpins the
  inverse calculus. It verifies that the "Lifted" inverse map actually
  inverts the Collatz function.

  We prove:
    3 * x'_p + 1 = 2^(alpha+6p) * x
    
  Preconditions:
    1. alpha >= 1 (so beta is well-defined).
    2. The row parameters are valid (beta, c, delta defined as in paper).
    3. The inverse step is valid (the numerator is divisible by 9).
*)

(* Helper: 64^p = 2^(6p) *)
Lemma pow_64_is_pow_2_6p : forall (p : nat),
  64 ^ Z.of_nat p = 2 ^ (6 * Z.of_nat p).
Proof.
  intros p.
  replace 64 with (2^6) by reflexivity.
  rewrite <- Z.pow_mul_r; try lia.  
Qed.

(**
  Theorem E.1 [Forward identity for a lifted row]:
  The derived formula for x'_p satisfies the backward Collatz relation.
*)
Lemma Forward_identity_for_a_lifted_row :
  forall (alpha p : nat)
         (beta c delta j p6 m : Z),
    (alpha >= 1)%nat ->
    beta = (2 ^ (Z.of_nat (alpha - 1))) * (6 * j + p6) ->
    2 * c + 3 * delta + 1 = 0 ->
    (* The numerator must be divisible by 9 for the step to be an integer *)
    (beta * (64 ^ (Z.of_nat p)) + c) mod 9 = 0 -> 
    
    (* Conclusion: 3 * x'_p + 1 = 2^(alpha+6p) * x *)
    3 * (6 * ( (2 ^ (Z.of_nat (alpha + 6 * p))) * m
               + (beta * (64 ^ (Z.of_nat p)) + c) / 9) + delta) + 1
    = (2 ^ (Z.of_nat (alpha + 6 * p))) * (18 * m + 6 * j + p6).
Proof.
  intros alpha p beta c delta j p6 m Halpha Hbeta Hc Hdiv.
  (* 1. Expand the LHS: 3 * (6 * (...)) becomes 18 * (...) *)
  rewrite Z.mul_add_distr_l. (* 3 * (6*... + delta) *)
  rewrite Z.mul_assoc with (n:=3) (m:=6).
  change (3 * 6) with 18.
  
  (* LHS = 18 * (2^E * m) + 18 * ((beta*64^p + c)/9) + 3*delta + 1 *)
  rewrite Z.mul_add_distr_l.
  
  (* 2. Simplify the integer division term using Hdiv *)
  (* Logic: If X mod 9 = 0, then 18 * (X / 9) = 2 * X *)
  (* 2. Simplify the integer division term using Hdiv *)
  (* Logic: If X mod 9 = 0, then 9 * (X / 9) = X *)
  replace 18 with (2 * 9) by reflexivity.
  rewrite Z.mul_assoc. (* Turns (2*9)*Term into 2*(9*Term) *)  
  (* Cancel the 2*9*2^...*m part *)
  replace (2 ^ Z.of_nat (alpha + 6 * p) * (2 * 9 * m + 6 * j + p6))
    with (2 * 9 * 2 ^ Z.of_nat (alpha + 6 * p) * m
          + 2 ^ Z.of_nat (alpha + 6 * p) * (6 * j + p6)) by ring.  
  (* Cancel that common part: *)
  apply Z.add_cancel_l with
    (p := 2 * 9 * 2 ^ Z.of_nat (alpha + 6 * p) * m).
  set (N := beta * 64 ^ Z.of_nat p + c) in *.
  assert (Hdiv_eq : 9 * (N / 9) = N).
  {
    (* standard div-mod equality: N = 9*(N/9) + N mod 9 *)    
    pose proof (Z.div_mod N 9) as Hdm. (* sometimes named Z.div_mod or Z.div_mod' *)
    (* Hdm : N = 9 * (N / 9) + N mod 9 *)
    rewrite Hdiv in Hdm.       (* N mod 9 = 0 *)
    (* N = 9 * (N / 9) + 0 *)
    replace (9 * (N / 9)) with N by lia.
    reflexivity.    
  }
  (* Now rewrite 2*9*(N/9) as 2*N *)
  rewrite <- Hdiv_eq.
  set (A := 2 * 9 * 2 ^ Z.of_nat (alpha + 6 * p) * m) in *.
  
  apply Z.add_cancel_l.  (* goal: A + (...) = A + (...) *)
  assert (Hdiv' : (9 * (N / 9)) / 9 = N / 9).
  { rewrite Hdiv_eq. reflexivity. }
  rewrite Hdiv'.
  (* We are at: 
    A + 2 * 9 * (N / 9) + 3 * delta + 1
    = A + 2 ^ Z.of_nat (alpha + 6 * p) * (6 * j + p6)
  *)
  (* 1. Cancel A on both sides *)
  apply Z.add_cancel_l with (p := A).
  (* Goal: 2 * 9 * (N / 9) + 3 * delta + 1
            = 2 ^ Z.of_nat (alpha + 6 * p) * (6 * j + p6) *)
  (* 2. Use 9 * (N/9) = N to turn the 2*9*(N/9) into 2*N *)
  replace (2 * 9 * (N / 9)) with (2 * N)
    by (rewrite <- Hdiv_eq; lia).
  (* Goal is now: 2 * N + 3 * delta + 1
                  = 2 ^ Z.of_nat (alpha + 6 * p) * (6 * j + p6) *)
  (* 3. Expand N and use Hbeta, Hc *)
  subst N.           (* N := beta * 64 ^ Z.of_nat p + c *)
  rewrite Hbeta.     (* beta in terms of 2^(alpha-1)*(6j+p6) *)
  (* LHS is: 2 * (2 ^ Z.of_nat (alpha - 1) * (6 * j + p6) * 64 ^ Z.of_nat p + c)
              + 3 * delta + 1 *)
  (* Distribute 2 and group the c + delta part *)
  change (2 * (2 ^ Z.of_nat (alpha - 1) * (6 * j + p6) * 64 ^ Z.of_nat p + c)
          + 3 * delta + 1)
    with (2 * 2 ^ Z.of_nat (alpha - 1) * (6 * j + p6) * 64 ^ Z.of_nat p
          + (2 * c + 3 * delta + 1)).
  apply Z.add_cancel_l with (p := A).     
  assert (Hcancel: 2 * (2 ^ Z.of_nat (alpha - 1) * (6 * j + p6) * 64 ^ Z.of_nat p)
    = 2 ^ Z.of_nat (alpha + 6 * p) * (6 * j + p6)).
  { 
    (* Let B := 6*j + p6 for readability *)
    set (B := 6 * j + p6) in *.
    (* Rearrange multiplications so the exponent part is visible *)
    repeat rewrite Z.mul_assoc in *.
    (* We want: 2 * (2 ^ (α-1) * B * 64^p) = 2^(α+6p) * B *)
    (* Step 1: prove the exponent identity without B *)
    assert (Hexp :
      2 * 2 ^ Z.of_nat (alpha - 1) * 64 ^ Z.of_nat p =
      2 ^ Z.of_nat (alpha + 6 * p)
    ).
    {
      (* rewrite 64^p as 2^(6p) *)      
      change (2 ^ 6)%Z with 64%Z.
      (* Now LHS is 2 * 2^(α-1) * 2^(6·p) *)
      repeat rewrite Z.mul_assoc.
      (* Rewrite the exponent alpha + 6p on the RHS as Z sums *)
      replace (Z.of_nat (alpha + 6 * p))
        with (Z.of_nat alpha + 6 * Z.of_nat p)%Z.
      2:{
        rewrite Nat2Z.inj_add, Nat2Z.inj_mul.
        change (Z.of_nat 6) with 6%Z.
        lia.
      }
      (* Use 2^(a+b) = 2^a * 2^b *)
      rewrite Z.pow_add_r by lia.
      (* Rewrite Z.of_nat alpha as 1 + (alpha-1) (since alpha≥1) *)
      assert (Halpha' :
        Z.of_nat alpha = 1 + Z.of_nat (alpha - 1)
      ).
      {        
        assert (Halpha_succ : alpha = S (alpha - 1)) by lia.
        rewrite Halpha_succ.
        (* now we just use the standard nat→Z successor lemma *)
        rewrite Nat2Z.inj_succ.
        lia.
      }
      rewrite Halpha' at 1.
      rewrite Z.pow_add_r by lia.
      change (2 ^ 1)%Z with 2%Z.
      rewrite Z.pow_mul_r with (a := 2) (b := 6) (c := Z.of_nat p) by lia.
      change (2 ^ 6)%Z with (64%Z).
      reflexivity.      
    }    
    repeat rewrite Z.mul_assoc.
    (* regroup left side to match Hexp *)
    replace (2 * 2 ^ Z.of_nat (alpha - 1) *B * 64 ^ Z.of_nat p)
      with ((2 * 2 ^ Z.of_nat (alpha - 1) * 64 ^ Z.of_nat p) * B) by lia.
    rewrite Hexp.  (* now LHS is 2^(alpha+6p) * B *)
    reflexivity.
  }
  (* Let E be the big product without c *)
  set (E := 2 ^ Z.of_nat (alpha - 1) * (6 * j + p6) * 64 ^ Z.of_nat p) in *.
  (* Separate the c, delta, 1 piece as (2*c + 3*delta + 1) *)
  replace (A + 2 * (E + c) + 3 * delta + 1)
    with (A + 2 * E + (2 * c + 3 * delta + 1)) by ring.
  (* Use the condition tying c and delta *)
  rewrite Hc. 
  replace (A + 2 * E + 0) with (A + 2 * E) by ring.
  (* Use the cancellation identity to replace 2*E *)
  rewrite Hcancel.
  (* Both sides are now syntactically identical *)
  reflexivity.
Qed.

End Appendix_E_Identity_Derivation.
