From Stdlib Require Import Arith.Arith Arith.PeanoNat Lia.


Module Routing_compatibility_no_branch_flips.

(**
  Abstract interface for a "prefix" and routing:

  - [prefix] is the type of certified prefixes (finite words of rows).
  - [len W] is the number of steps in W.
  - [router_plan W t] is the planned router choice j_{t+1} at step t.
  - [router_actual W t m] is the router actually taken at step t
    when running W on parameter m.
  - [routing_bound W S_star] expresses that S* is a valid 2-adic
    routing bound for W (i.e. Section 20's S* ≥ max s_t condition).

  Hypothesis [router_2adic_stable] captures the outcome of Section 20:
  once S* is a routing bound for W, the router at each step t depends
  only on m mod 2^{S*}.
*)
Section AbstractRoutingCompatibilityNoBranchFlips.
  Variable prefix : Type.

  Variable len : prefix -> nat.
  Variable router_plan   : prefix -> nat -> nat.
  Variable router_actual : prefix -> nat -> nat -> nat.
  Variable routing_bound : prefix -> nat -> Prop.

  Definition pow2 (k : nat) : nat := Nat.pow 2 k.

  (**
    2-adic stability of routing (abstract form of Section 20’s result):

    If [routing_bound W S_star] holds, then for every step t < len W,
    the router choice [router_actual W t m] depends only on m mod 2^{S*}.
  *)
  Hypothesis router_2adic_stable :
    forall (W : prefix) (S_star : nat),
      routing_bound W S_star ->
      forall t, t < len W ->
      forall m1 m2,
        m1 mod pow2 S_star = m2 mod pow2 S_star ->
        router_actual W t m1 = router_actual W t m2.

  (* ---------------------------------------------------------------------- *)
  (* 1. Routing compatibility on a fixed congruence class (lem:TD2-routing) *)
  (* ---------------------------------------------------------------------- *)

  (**
    This lemma corresponds to the "TD2 routing compatibility" statement:

    If:

    - S* is a routing bound for W,
    - m_star is a parameter for which the run along W uses exactly the
      planned routers [router_plan W t],
    - and m is any other parameter congruent to m_star modulo 2^{S*},

    then the run along W at m also uses the same routers:

      router_actual W t m = router_plan W t,  for all t < len W.
  *)

  Lemma lem_TD2_routing :
    forall (W : prefix) (S_star m_star : nat),
      routing_bound W S_star ->
      (forall t, t < len W -> router_actual W t m_star = router_plan W t) ->
      forall m,
        m mod pow2 S_star = m_star mod pow2 S_star ->
        forall t, t < len W ->
          router_actual W t m = router_plan W t.
  Proof.
    intros W S_star m_star Hbound Hbase m Hcong t Htlt.
    (* By 2-adic stability, router W t m = router W t m_star *)
    specialize (router_2adic_stable W S_star Hbound t Htlt m m_star Hcong) as Hstab.
    (* And we know router W t m_star = planned router *)
    specialize (Hbase t Htlt) as Hplan.
    now rewrite Hstab, Hplan.
  Qed.

  (* ---------------------------------------------------------------------- *)
  (* 2. Routing compatibility under the S* bound (lem:routing-compat-Sstar) *)
  (* ---------------------------------------------------------------------- *)

  (**
    This is essentially the same content as [lem_TD2_routing], but with
    emphasis on the role of S* as a global bound.

    Given:

      - [routing_bound W S_star],
      - a "base" parameter m_star realizing the planned routers,

    every parameter m in the same 2^{S*}-congruence class yields exactly
    the same routing on the prefix W.

    This is the formal "no branch flips" statement under the S* bound.
  *)

  Lemma lem_routing_compatibility_Sstar :
    forall (W : prefix) (S_star m_star : nat),
      routing_bound W S_star ->
      (forall t, t < len W -> router_actual W t m_star = router_plan W t) ->
      forall m,
        m mod pow2 S_star = m_star mod pow2 S_star ->
        forall t, t < len W ->
          router_actual W t m = router_plan W t.
  Proof.
    (* This is just [lem_TD2_routing] with the same hypotheses. *)
    intros W S_star m_star Hbound Hbase m Hcong t Htlt.
    apply lem_TD2_routing with (W := W) (S_star := S_star) (m_star := m_star);
      assumption.
  Qed.

  (* ---------------------------------------------------------------------- *)
  (* 3. Stable under padding (cor:stable-padding)                           *)
  (* ---------------------------------------------------------------------- *)

  (**
    Corollary: stability under padding.

    Intuitively, if W' is obtained by padding W on the right (i.e. adding
    extra rows after W), and if that padding does not change the routing
    behaviour on the first [len W] steps, then the "no branch flips" and
    routing-compatibility conclusions for W automatically transfer to W'
    on its prefix.

    We do not model concatenation explicitly here; instead we assume:

      - [len W <= len W'] so that the prefix of W' of length [len W] is
        at least defined,
      - on that prefix, planned routers coincide:
          router_plan W' t = router_plan W t,
      - and actual routers also coincide:
          router_actual W' t m = router_actual W t m
        for all m and t < len W.

    Then, if S* is a routing bound for W and m_star realizes the planned
    routers along W, any m in the same 2^{S*}-congruence class will also
    realize the planned routers along the prefix of W'.
  *)

  Corollary cor_stable_padding :
    forall (W W' : prefix) (S_star m_star : nat),
      len W <= len W' ->
      (forall t, t < len W -> router_plan W' t = router_plan W t) ->
      (forall t m, t < len W -> router_actual W' t m = router_actual W t m) ->
      routing_bound W S_star ->
      (forall t, t < len W -> router_actual W t m_star = router_plan W t) ->
      forall m,
        m mod pow2 S_star = m_star mod pow2 S_star ->
        forall t, t < len W ->
          router_actual W' t m = router_plan W' t.
  Proof.
    intros W W' S_star m_star Hlen_le Hplan_eq Hact_eq Hbound Hbase m Hcong t Htlt.
    (* First use routing compatibility on W *)
    assert(Hroute_W :
      router_actual W t m = router_plan W t).
    { eapply lem_routing_compatibility_Sstar; eauto. }
    (* Then transport this equality along W' using the prefix equalities *)
    rewrite (Hact_eq t m Htlt).
    rewrite Hroute_W.    
    rewrite <- (Hplan_eq t Htlt).
    reflexivity.    
  Qed.

End AbstractRoutingCompatibilityNoBranchFlips.

End Routing_compatibility_no_branch_flips.
