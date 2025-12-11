From Coq Require Import Arith.Arith Arith.PeanoNat Lia.

Module Same_family_steering_menu_and_monotone_padding_p0.

(**
  Section 19: Same-family steering menu and monotone padding (p = 0)

  This module is meant to formalize two conceptual lemmas from the paper:

  - [lem_monotone] ("Monotone (suffix-only) padding", Lemma 19.x):
      Given a target 2-adic level K and a terminal family (e or o),
      there exists a finite tail built from the steering-menu blocks
          Ψ₁, Ψ₂, Ω₁, Ω₀, ψ₂∘ω₁, ω₁∘ψ₂
      such that:
        * the tail strictly increases v₂(A) (monotonically),
        * it preserves the desired terminal family, and
        * appending a parity-cycle once flips the intermediate parity
          while preserving the terminal family.

  - [lem_routing_compat_prefix] ("Routing compatibility for the stabilized prefix"):
      After freezing a certified prefix W with parameters (A_W, B_W, δ_W),
      and after choosing a tail S from the same-family steering menu,
      the combined word W·S respects the same router choices inside W;
      i.e. appending S does not invalidate any last-row congruences used
      to certify W.

  The exact Coq statements of these lemmas depend on the global
  definitions of:
    - certified words W and their parameters (A_W, B_W, δ_W),
    - tails S (as words in the ψ/ω alphabet),
    - the “family” of a word or residue, and
    - the router / last-row congruence framework from Sections 16–18.
  
*)

Section AbstractMonotonePadding.

  (** Abstract type of words (e.g. list Letter in your project). *)
  Variable word : Type.

  (** Terminal families: even (e) or odd (o). *)
  Inductive family :=
  | FamE
  | FamO.

  (** For each word W we know:
      - its terminal family [family_of W],
      - its 2-adic valuation v2(A_W) as [v2A W].
   *)
  Variable family_of : word -> family.
  Variable v2A      : word -> nat.

  (** Append a tail block on the right: [app W T = W·T]. *)
  Variable app      : word -> word -> word.

  (*** Monotone same-family blocks from the steering menu ***)

  (** One block for the e-family (like Ψ₁ or Ψ₂). *)
  Variable block_e : word.
  Variable delta_e : nat.

  Hypothesis block_e_spec :
    forall W,
      family_of W = FamE ->
      family_of (app W block_e) = FamE /\
      v2A (app W block_e) = v2A W + delta_e.

  Hypothesis delta_e_pos : delta_e > 0.

  (** One block for the o-family (like Ω₁ or Ω₀). *)
  Variable block_o : word.
  Variable delta_o : nat.

  Hypothesis block_o_spec :
    forall W,
      family_of W = FamO ->
      family_of (app W block_o) = FamO /\
      v2A (app W block_o) = v2A W + delta_o.

  Hypothesis delta_o_pos : delta_o > 0.

  (*** Iterated padding by these blocks ***)

  Fixpoint pad_e (n : nat) (W : word) : word :=
    match n with
    | 0   => W
    | S k => pad_e k (app W block_e)
    end.

  Fixpoint pad_o (n : nat) (W : word) : word :=
    match n with
    | 0   => W
    | S k => pad_o k (app W block_o)
    end.

  Lemma pad_e_preserves_family :
    forall n W,
      family_of W = FamE ->
      family_of (pad_e n W) = FamE.
  Proof.
    induction n as [|n IH]; intros W HF; simpl.
    - exact HF.
    - destruct (block_e_spec W HF) as [HF' _].
      apply IH; exact HF'.
  Qed.

  Lemma pad_o_preserves_family :
    forall n W,
      family_of W = FamO ->
      family_of (pad_o n W) = FamO.
  Proof.
    induction n as [|n IH]; intros W HF; simpl.
    - exact HF.
    - destruct (block_o_spec W HF) as [HF' _].
      apply IH; exact HF'.
  Qed.

  Lemma pad_e_v2A :
    forall n W,
      family_of W = FamE ->
      v2A (pad_e n W) = v2A W + n * delta_e.
  Proof.
    induction n as [|n IH]; intros W HF; simpl.
    - lia.
    - destruct (block_e_spec W HF) as [HF' Hv].
      (* apply IH to the word (app W block_e) *)
      rewrite IH with (W := app W block_e); [| exact HF'].
      (* now we *do* have v2A (app W block_e) in the goal *)
      rewrite Hv.
      lia.      
  Qed.

  Lemma pad_o_v2A :
    forall n W,
      family_of W = FamO ->
      v2A (pad_o n W) = v2A W + n * delta_o.
  Proof.
    induction n as [|n IH]; intros W HF; simpl.
    - lia.
    - destruct (block_o_spec W HF) as [HF' Hv].
      rewrite IH with (W := app W block_o) by exact HF'.
      rewrite Hv.      
      lia.
  Qed.

  (** Purely arithmetic helper: given v, K, Δ>0, you can reach ≥K
      using v + n*Δ for some n. *)
  Lemma monotone_raise :
    forall v K delta,
      delta > 0 ->
      exists n, v + n * delta >= K.
  Proof.
    intros v K delta Hdelta.
    destruct (le_ge_dec K v) as [Hle | Hgt].
    - exists 0. lia.
    - (* Let n := K - v; since delta >= 1, v + n*delta >= v + n = K. *)
      exists (K - v).
      assert (Hstep : (K - v) * delta >= (K - v)).
      { replace delta with (1 + (delta - 1)) by lia.
        rewrite Nat.mul_add_distr_l. 
        replace ((K - v) * 1) with (K - v) by lia.
        assert (Hdelta_ge1 : delta >= 1) by lia.
        rewrite <- Nat.mul_1_r with (n := K - v).
        rewrite !Nat.mul_1_r in *.
        replace (K - v + (K - v) * (delta - 1))
          with ((K - v) * (1 + (delta - 1))) by lia.        
        rewrite Nat.mul_add_distr_l.
        nia.
      }
      lia.
  Qed.

  (** Monotone (suffix-only) padding, matching Lemma 19 (v₂-part). *)
  Lemma lem_monotone_padding :
    forall (K : nat) (W : word),
      match family_of W with
      | FamE =>
          exists n,
            let W' := pad_e n W in
            v2A W' >= K /\ family_of W' = FamE
      | FamO =>
          exists n,
            let W' := pad_o n W in
            v2A W' >= K /\ family_of W' = FamO
      end.
  Proof.
    intros K W.
    destruct (family_of W) eqn:Hf.
    - (* FamE case *)
      destruct (monotone_raise (v2A W) K delta_e delta_e_pos) as [n Hn].
      exists n.
      simpl.
      split.
      + rewrite pad_e_v2A by exact Hf. exact Hn.
      + apply pad_e_preserves_family; exact Hf.
    - (* FamO case *)
      destruct (monotone_raise (v2A W) K delta_o delta_o_pos) as [n Hn].
      exists n.
      simpl.
      split.
      + rewrite pad_o_v2A by exact Hf. exact Hn.
      + apply pad_o_preserves_family; exact Hf.
  Qed.

End AbstractMonotonePadding.

End Same_family_steering_menu_and_monotone_padding_p0.

