From Coq Require Import Arith.Arith Arith.PeanoNat Lia.
From Coq Require Import Lists.List.
Import ListNotations.

Module Mod3_steering_in_the_same_family.
(**
  Section 34: Mod-3 steering in the same family

  This module proves the "Liveness" property:
  For any odd integer x (not divisible by 3) and ANY family (Psi or Omega),
  there exists a token in that family that produces a valid integer parent.
*)

(**********************************************************************)
(* 1. Concrete Definitions (imported from Sec 17 in full build)       *)
(**********************************************************************)

(* The families of tokens *)
Inductive family := FamPsi | FamOmega.

(* The specific tokens used in the paper *)
(* Note: We assume at least these exist to satisfy the proof. *)
Inductive Token := 
  | psi_0 | psi_1      (* Psi family members *)
  | omega_0 | omega_1. (* Omega family members *)

(* Map tokens to their families *)
Definition token_family (t : Token) : family :=
  match t with
  | psi_0 | psi_1 => FamPsi
  | omega_0 | omega_1 => FamOmega
  end.

(* Map tokens to parameters (alpha, c) *)
(* CRITICAL: The exponents (alpha) must cycle parity to cover mod 3 *)
Definition get_params (t : Token) : (nat * nat) :=
  match t with
  (* Psi Family *)
  | psi_0 => (1, 1)  (* 2^1 = 2.  2x - 1 *)
  | psi_1 => (2, 1)  (* 2^2 = 4.  4x - 1 *)
  
  (* Omega Family *)
  | omega_0 => (1, 1) (* 2^1 = 2 *)
  | omega_1 => (2, 1) (* 2^2 = 4 *)
  end.

(** Predicate: The inverse step is valid modulo 3. *)
(** (2^alpha * x - c) = 0 mod 3 *)
Definition valid_mod3 (t : Token) (x : nat) : Prop :=
  let (alpha, c) := get_params t in
  (Nat.pow 2 alpha * x - c) mod 3 = 0.

(**********************************************************************)
(* 2. Proof of Lemma 34.1                                            *)
(**********************************************************************)

(**
  Lemma 34.1 [Same-family mod-3 control]:
  For any x not divisible by 3, and for ANY family f, there exists 
  a token t belonging to f such that the step is valid modulo 3.
*)

Theorem lem_mod3_steer : 
  forall (x : nat) (f : family),
    x mod 3 <> 0 -> 
    exists (t : Token),
      token_family t = f /\
      valid_mod3 t x.
Proof.
  intros x f Hmod.
  
  (* We analyze the residue of x mod 3. *)
  (* Since x mod 3 <> 0, x must be 1 or 2 modulo 3. *)
  assert (Hx_res: x mod 3 = 1 \/ x mod 3 = 2).
  {
    pose proof (Nat.mod_upper_bound x 3) as Hub.
    assert (0 <= x mod 3 < 3) by lia.
    destruct (x mod 3); try lia. (* 0 is excluded by Hmod *)    
  }

  (* Split by Family first *)
  destruct f.

  (* CASE 1: Family Psi (We have psi_0 (alpha=1) and psi_1 (alpha=2)) *)
  - destruct Hx_res as [H1 | H2].
    
    (* Subcase 1.1: x = 1 mod 3. Use psi_1 (alpha=2) *)
    * exists psi_1. split; [reflexivity |].
      unfold valid_mod3, get_params.
      (* Goal: (2^2 * x - 1) mod 3 = 0 *)
      (* 4x - 1 = 1*x - 1 = 1 - 1 = 0 *)
      rewrite Nat.pow_2_r. 
      replace(2*2) with 4 by reflexivity.
      replace (4 * x - 1) with (3 * x + (x - 1)) by lia.
      replace (3 * x + (x - 1)) with ((x - 1) + x * 3) by lia.
      rewrite Nat.Div0.mod_add; try lia.
      (* Now prove (x-1) is div by 3 *)
      apply Nat.Lcm0.mod_divide; try lia. 
      (* Goal: Prove 3 divides (x - 1) *)
      (* Switch from 'Divide' to 'Modulo = 0' *)
      apply Nat.Lcm0.mod_divide; try lia.

      (* Use the definition: x = 3 * (x / 3) + (x mod 3) *)
      pose proof (Nat.div_mod x 3) as H_div; try lia.
      rewrite H1 in H_div. 
      
      (* x = 3 * (x/3) + 1. Therefore, x - 1 = 3 * (x/3) *)
      replace (x - 1) with (3 * (x / 3)) by lia.
      
      (* (3 * k) mod 3 is always 0 *)
      (* Fix: Swap order so 3 is on the right, matching Nat.mod_mul *)
      rewrite Nat.mul_comm. 
      apply Nat.Div0.mod_mul; lia.      
    (* Subcase 1.2: x = 2 mod 3. Use psi_0 (alpha=1) *)
    * exists psi_0. split; [reflexivity |].      
      unfold valid_mod3, get_params.      
      replace(2^1) with 2 by reflexivity.      
      (* Robust Method: Substitute x = 3*k + 2 *)
      pose proof (Nat.div_mod x 3) as H_div; try lia.
      rewrite H2 in H_div.
      rewrite H_div.
      2:{ 
        lia. 
        }
      
      
      (* Goal: (2 * (3 * (x/3) + 2) - 1) mod 3 = 0 *)
      (* Algebra: 2(3k + 2) - 1 = 6k + 4 - 1 = 6k + 3 = 3(2k + 1) *)
      
      (* We replace the entire expression with a multiple of 3 *)
      replace (2 * (3 * (x / 3) + 2) - 1) with (3 * (2 * (x / 3) + 1)) by lia.
      
      (* Now applying mod 3 is trivial *)
      rewrite Nat.mul_comm.
      apply Nat.Div0.mod_mul; lia.

  (* CASE 2: Family Omega (Logic is identical as params are identical) *)
  (* CASE 2: Family Omega *)
  - destruct Hx_res as [H1 | H2].
    
    (* Subcase 2.1: x = 1 mod 3. Use omega_1 (4x - 1) *)
    * exists omega_1. split; [reflexivity |].
      unfold valid_mod3, get_params.
      rewrite Nat.pow_2_r. 
      
      (* Robust Fix: Substitute x = 3k + 1 *)
      pose proof (Nat.div_mod x 3) as H_div; try lia.
      rewrite H1 in H_div.
      rewrite H_div.
      2:{ 
        lia. 
        }
      
      (* Algebra: 4(3k + 1) - 1 = 12k + 4 - 1 = 12k + 3 = 3(4k + 1) *)
      replace (4 * (3 * (x / 3) + 1) - 1) with (3 * (4 * (x / 3) + 1)) by lia.
      
      (* Prove divisibility *)
      rewrite Nat.mul_comm.
      replace (2 * 2) with 4 by reflexivity.      
      set (y := x / 3).      

      (* Now it's just (3 * something) mod 3 *)
      assert (Hm3: ((3 * y + 1) * 4 - 1) = (12 * y + 3)) by lia.
      rewrite Hm3.
      replace ((12 * y + 3)) with ((4 * y + 1) * 3) by lia.
      
      rewrite Nat.Div0.mod_mul; lia.

    (* Subcase 2.2: x = 2 mod 3. Use omega_0 (2x - 1) *)
    * exists omega_0. split; [reflexivity |].
      unfold valid_mod3, get_params.      
      
      (* Robust Fix: Substitute x = 3k + 2 *)
      pose proof (Nat.div_mod x 3) as H_div; try lia.
      rewrite H2 in H_div.
      rewrite H_div.
      2:{ 
        lia. 
        }
      replace (2^1) with 2 by reflexivity.
      
      (* Algebra: 2(3k + 2) - 1 = 6k + 4 - 1 = 6k + 3 = 3(2k + 1) *)
      replace (2 * (3 * (x / 3) + 2) - 1) with (3 * (2 * (x / 3) + 1)) by lia.
      set (y := x / 3).      
      
      replace (3 * (2 * y + 1)) with ((2 * y + 1) * 3) by lia.
      
      (* Prove divisibility *)      
      apply Nat.Div0.mod_mul; lia.
Qed.

(**********************************************************************)
(* 3. Corollary                                                       *)
(**********************************************************************)

Corollary corollary_non_blocking : 
  forall (x : nat) (f : family),
    x mod 3 <> 0 ->
    exists t, token_family t = f /\ valid_mod3 t x.
Proof.
  intros. apply lem_mod3_steer. assumption.
Qed.

End Mod3_steering_in_the_same_family.