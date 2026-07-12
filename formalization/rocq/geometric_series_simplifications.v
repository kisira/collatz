From Coq Require Import Arith.Arith Arith.PeanoNat Lia.

Module Geometric_series_simplifications.

(** Section 17: Geometric-series simplifications for m_n (and x_n)

    This module formalizes the corollary "From m_n to x_n" from the
    paper, i.e. the linear relation

       x_n = 18 m_n + 6 j_n + δ_n.

    We keep the setup abstract, working over arbitrary sequences
    m_n, j_n and δ_n : nat -> nat, and define x_n from them as in
    the statement.
 *)

Section From_mn_to_xn.

  (** Abstract sequences m_n, j_n, δ_n. *)
  Variable m_n    : nat -> nat.
  Variable j_n    : nat -> nat.
  Variable delta_n : nat -> nat.

  (** Definition of x_n as in the paper: x_n = 18 m_n + 6 j_n + δ_n. *)
  Definition x_n (n : nat) : nat :=
    18 * m_n n + 6 * j_n n + delta_n n.

  (** Corollary [From m_n to x_n] (label: cor:xn-from-mn).

      At time n, x_n satisfies

         x_n = 18 m_n + 6 j_n + δ_n.

      In this abstract setting, this is just the definitional
      unfolding of [x_n].
   *)
  Corollary cor_xn_from_mn :
    forall n,
      x_n n = 18 * m_n n + 6 * j_n n + delta_n n.
  Proof.
    intros n; unfold x_n; lia.
  Qed.

End From_mn_to_xn.

End Geometric_series_simplifications.
