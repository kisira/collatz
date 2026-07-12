From Coq Require Import Arith.Arith Arith.PeanoNat Lia.

Module From_residues_to_exact_integers.
(**
  Section 33: From residues to exact integers

  This module formalizes Theorem 33.1 [Exact integers lie in the inverse tree
  of 1] from the paper:

      Every odd integer x >= 1 lies in the inverse tree of 1 under U.

  Logically, "x lies in the inverse tree of 1" means:
      exists k, U^k(x) = 1

  We do not re-define U here; instead we assume an abstract U and the
  Global Realization Theorem from Section 27, then derive the inverse-tree
  statement as a direct corollary.
*)

(**********************************************************************)
(* Abstract interface carried over from Section 27                    *)
(**********************************************************************)

(* Type of certified inverse words. *)
Parameter word : Type.

(* Length (number of steps / rows) of a word. *)
Parameter word_len : word -> nat.

(* Predicate: W is a certified inverse word. *)
Parameter certified_word : word -> Prop.

(* Accelerated Collatz forward map U. *)
Parameter U : nat -> nat.

(* Helper: Iterated Forward Map *)
Fixpoint U_iter (k : nat) (x : nat) : nat :=
  match k with
  | 0 => x
  | S k' => U (U_iter k' x)
  end.

(**
  Global Odd-Layer Realization Theorem (from Section 27):
  This is the "Dynamical Form" (Theorem 27.2).
  It asserts that for every odd x, we can find a word W such that
  applying U exactly |W| times yields 1.
*)
Axiom thm_odd_layer_global_1 :
  forall x : nat,
    Nat.Odd x ->
    exists (W : word) (m : nat),
      certified_word W /\
      U_iter (word_len W) x = 1.

(**********************************************************************)
(* "Inverse tree of 1" as a predicate                                 *)
(**********************************************************************)

(**
  Standard formulation of the Collatz Conjecture (for the accelerated map).
  x is in the inverse tree of 1 if some number of iterations reduces it to 1.
*)
Definition in_inverse_tree_of_1 (x : nat) : Prop :=
  exists k : nat, U_iter k x = 1.

(**********************************************************************)
(* Theorem: Exact integers lie in the inverse tree of 1              *)
(* (Corresponds to thm:residues-to-integers)                         *)
(**********************************************************************)

Theorem thm_residues_to_integers :
  forall x : nat,
    Nat.Odd x ->
    in_inverse_tree_of_1 x.
Proof.
  intros x Hodd.
  unfold in_inverse_tree_of_1.
  
  (* 1. Use the Global Realization Theorem from Section 27 *)
  (* This gives us a word W and a parameter m such that U^|W|(x) = 1 *)
  destruct (thm_odd_layer_global_1 x Hodd) as [W [m [Hcert HW]]].
  
  (* 2. The witness for the number of steps k is simply the length of W *)
  exists (word_len W).
  
  (* 3. The theorem guarantees exactly what we need *)
  exact HW.
Qed.

End From_residues_to_exact_integers.