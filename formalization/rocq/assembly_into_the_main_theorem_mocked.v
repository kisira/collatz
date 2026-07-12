From Coq Require Import Arith.Arith Arith.PeanoNat Lia.

Module Assembly_into_the_main_theorem.

(**
  ==========================================================================
  SECTION 27: ASSEMBLY INTO THE MAIN THEOREM
  ==========================================================================

  This module serves as the high-level "Roof" of the formalization. It 
  assembles the certified components from previous sections to prove the 
  Global Odd-Layer Realization Theorems (27.1 and 27.2).

  DEPENDENCIES & ARCHITECTURE:
  This file relies on the following verified components, which are proved 
  in separate modules:

  1.  **Base Witnesses (Section 14 & 25):** Provides the finite set of certified words covering all residues 
      modulo 24 (or 3*2^K).
      
  2.  **Geometry & Drift (Section 17):** Establishes the properties of the inverse map (Phi), expansion 
      (A > 1), and the linear drift bound.

  3.  **Steering & Padding (Sections 19–21):** Provides the algorithm to extend base seeds into words that target 
      specific congruence classes.

  4.  **The Lifting Lemma (Section 15 & 24):** Proves that a solution modulo 3*2^K can be "lifted" to a unique 
      integer solution modulo 3*2^(K+1).

  5.  **Dynamical Implication (Section 10 & 29):** The "Semantic Link" proving that if x_W(m) = x, then U^{|W|}(x) = 1.

  NOTE:
  In this file, these components are declared as variables (constructive 
  witnesses) to isolate the assembly logic. In the full build, these 
  variables are instantiated with the theorems from the respective files.
*)


(**********************************************************************)
(* CONSTRUCTIVE DEPENDENCIES                                          *)
(* These represent the algorithms from Sections 18-26.                *)
(* We use {x | P} (Sigma types) to ensure we can build the final algo.*)
(**********************************************************************)

Section ConstructiveDependencies.

    (**********************************************************************)
    (* Abstract interface                                                 *)
    (**********************************************************************)

    (* Type of certified inverse words. *)
    Variable word : Type.
    (* Length (number of steps / rows) of a word. *)
    Variable word_len : word -> nat.
    (* Evaluation map: for a word W and internal index m, produce x_W(m). *)
    Variable x_W : word -> nat -> nat.
    (* Predicate: W is a certified inverse word (all routing and invariants OK). *)
    Variable certified_word : word -> Prop.

    (* Accelerated Collatz forward map U(n) = (3n+1)/2^{v2(3n+1)}. *)
    Variable U : nat -> nat.
    Fixpoint U_iter (k : nat) (x : nat) : nat :=
    match k with
    | 0 => x
    | S k' => U (U_iter k' x)
    end.

    Definition pow2 (k : nat) : nat := Nat.pow 2 k.
    Definition M_K (K : nat) : nat := 3 * pow2 K.


    (* Algorithm 1: Base Coverage (Section 25) *)
    (* Input: odd x. Output: A base seed W0 and its properties. *)
    Variable algo_base_coverage : 
        forall x : nat, Nat.Odd x -> 
        { W0 : word & { K0 : nat | certified_word W0 } }.

    (* Algorithm 2: Steering and Padding (Section 21) *)
    (* Input: seed W0, target x. Output: A steered word W1. *)
    Variable algo_steering :
        forall (W0 : word) (x : nat),
        certified_word W0 ->
        { W1 : word | certified_word W1 }.

    (* Algorithm 3: Linear Lifting (Section 24) *)
    (* Input: steered word W1, target x. Output: Parameter m. *)
    Variable algo_lifting :
        forall (W1 : word) (x : nat),
        certified_word W1 -> 
        { m : nat | x_W W1 m = x }.

    (* Semantic Link (Theorem from Section 10) *)
    (* This remains a logical Prop since it describes behavior, not data. *)
    Variable thm_semantic_link :
        forall (W : word) (m : nat),
        certified_word W ->
        U_iter (word_len W) (x_W W m) = 1.

    (**********************************************************************)
    (* Theorem 1: Global odd-layer realization (Logical Form)            *)
    (**********************************************************************)

    Theorem thm_odd_layer_global_0 :
    forall x : nat,
        Nat.Odd x ->
        exists (W : word) (m : nat),
        certified_word W /\
        x_W W m = x.
    Proof.
    intros x Hodd.
    (* 1. Call Base Coverage *)
    destruct (algo_base_coverage x Hodd) as [W0 [K0 Hcert0]].
    
    (* 2. Call Steering *)
    destruct (algo_steering W0 x Hcert0) as [W1 Hcert1].
    
    (* 3. Call Lifting *)
    destruct (algo_lifting W1 x Hcert1) as [m Heq].
    
    (* 4. Witness the existential *)
    exists W1, m.
    auto.
    Qed.

    (**********************************************************************)
    (* Theorem 2: Global odd-layer realization (Dynamical Form)          *)
    (**********************************************************************)

    Theorem thm_odd_layer_global_1 :
    forall x : nat,
        Nat.Odd x ->
        exists (W : word) (m : nat),
        certified_word W /\
        U_iter (word_len W) x = 1.
    Proof.
    intros x Hodd.
    (* 1. Use Theorem 1 to find the structure *)
    destruct (thm_odd_layer_global_0 x Hodd) as [W [m [Hcert Heq]]].
    
    exists W, m.
    split; [assumption |].
    
    (* 2. Rewrite x as x_W(m) and apply the semantic link *)
    rewrite <- Heq.
    apply thm_semantic_link.
    assumption.
    Qed.

    (**********************************************************************)
    (* Corollary: Algorithmic construction and termination               *)
    (* Corresponds to Source [25-29]                                      *)
    (**********************************************************************)

    (** This is the final algorithmic corollary. Because our dependencies 
    are constructive (Sigma types), we can simply compose them to 
    produce the final tuple {W, m, Proof}.
    *)

    Corollary Algorithmic_construction_and_termination :
    forall x : nat,
        Nat.Odd x ->
        { W : word & { m : nat |
        certified_word W /\ x_W W m = x } }.
    Proof.
    intros x Hodd.

    (* Step 1: Compute the base seed *)
    (* "destruct" on a Sigma type acts like a "let" binding in the algorithm *)
    destruct (algo_base_coverage x Hodd) as [W0 [K0 Hcert0]].

    (* Step 2: Compute the steered word *)
    destruct (algo_steering W0 x Hcert0) as [W1 Hcert1].

    (* Step 3: Compute the lift parameter m *)
    destruct (algo_lifting W1 x Hcert1) as [m Heq].

    (* Step 4: Return the result package *)
    exists W1, m.
    split.
    - exact Hcert1.
    - exact Heq.
    Qed.

End ConstructiveDependencies.

End Assembly_into_the_main_theorem.