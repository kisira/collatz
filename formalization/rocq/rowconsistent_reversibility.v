From Coq Require Import Arith.Arith Arith.PeanoNat Lia.
From Coq Require Import Lists.List.
Import ListNotations.

Module Rowconsistent_reversibility.
(**
  Section 32: Row–consistent reversibility (with optional p-lift)

  This module defines the abstract interface for the reverse search:
    - Axiom 32.1 [Row–consistent reversibility]: Asserts soundness.
    - Corollary 32.2 [Algorithmic completeness]: Derived from the Axiom.

  We use 'Axiom' to formally declare the properties that the implementation 
  must satisfy.
*)

(**********************************************************************)
(* Abstract interface for rows and one-step dynamics                 *)
(**********************************************************************)

Inductive family := FamE | FamO.

Record row := {
  row_s     : family; (* parent family s ∈ {e,o} *)
  row_j     : nat;    (* router index j ∈ {0,1,2} *)
  row_alpha : nat;    (* exponent α in 3x'+1 = 2^α x *)
  row_beta  : nat;    (* β parameter in k_p = (β 64^p + c)/9 *)
  row_c     : nat;    (* c parameter in k_p *)
  row_delta : nat;    (* δ ∈ {1,5} matching family of the child *)
}.

(* The global list of rows in the unified table (for a fixed p-slice). *)
Parameter rows : list row.

(* Accelerated Collatz forward map U(n) = (3n+1)/2^{v2(3n+1)}. *)
Parameter U : nat -> nat.

(* Family and router extracted from an odd integer x. *)
Parameter s_of : nat -> family.
Parameter j_of : nat -> nat.

(**
  Logical predicate capturing all the semantic conditions that make x_prev
  a legal parent of y through row r with lift p:
    - y is odd, and δ ≡ y (mod 6),
    - U(y) = x_prev (forward certificate),
    - the parent indices (family, router) match (s,j).
*)
Definition legal_parent (r : row) (p : nat) (y x_prev : nat) : Prop :=
  Nat.Odd y /\
  (row_delta r mod 6 = y mod 6) /\
  U y = x_prev /\
  s_of x_prev = row_s r /\
  j_of x_prev = row_j r.

(**********************************************************************)
(* Reverse-One-Step(y,p): row-consistent reverse search              *)
(**********************************************************************)

(**
  The algorithm Reverse-One-Step(y,p).
  We declare it as a Parameter (an abstract function).
*)
Parameter reverse_one_step : nat (* y *) -> nat (* p *) -> option (row * nat).

(**********************************************************************)
(* Axiom: Row–consistent reversibility                               *)
(**********************************************************************)

(**
  Axiom 32.1:
  Asserts that [reverse_one_step] is sound and complete relative to the 
  rows in the table. If it returns (r, x_prev), that parent is valid. 
  If it returns None, no valid parent exists for this lift p.
*)

Axiom thm_row_consistent_reversibility :
  forall y p,
    Nat.Odd y ->
    match reverse_one_step y p with
    | Some (r, x_prev) =>
        In r rows /\ legal_parent r p y x_prev
    | None =>
        forall r x_prev,
          In r rows ->
          ~ legal_parent r p y x_prev
    end.

(**********************************************************************)
(* Corollary: Algorithmic completeness of reverse search             *)
(**********************************************************************)

(**
  Corollary 32.2:
  If an odd y has at least one legal parent via some row and some lift p,
  then [reverse_one_step y p] MUST return a result.
  
  (This is fully proved using the Axiom above.)
*)

Corollary cor_alg_complete_reverse :
  forall y p,
    Nat.Odd y ->
    (exists r x_prev, In r rows /\ legal_parent r p y x_prev) ->
    exists r' x_prev',
      reverse_one_step y p = Some (r', x_prev').
Proof.
  intros y p Hodd [r [x_prev [Hin Hlegal]]].
  
  (* We use the Axiom to analyze the behavior of the function *)
  pose proof (thm_row_consistent_reversibility y p Hodd) as Haxiom.
  
  destruct (reverse_one_step y p) as [[r_res x_res] |].
  - (* Case: Some result returned. Success. *)
    exists r_res, x_res.
    reflexivity.
  - (* Case: None returned. *)
    (* The Axiom says: if None, then FORALL r x, ~legal_parent. *)
    (* This contradicts our hypothesis Hlegal. *)
    exfalso.
    apply (Haxiom r x_prev Hin).
    exact Hlegal.
Qed.

End Rowconsistent_reversibility.