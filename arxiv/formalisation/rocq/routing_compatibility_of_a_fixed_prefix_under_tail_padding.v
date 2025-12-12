From Coq Require Import Arith.Arith Arith.PeanoNat Lia.

Module Routing_compatibility_of_a_fixed_prefix_under_tail_padding.

(**
  This file corresponds to Section 20:
  "Routing-compatibility of a fixed prefix under tail padding".

  It contains three main lemmas:

  - [lem_prefix_2adic_rc]   : 2-adic control of prefix indices
  - [lem_routing_compat_rc] : routing compatibility (no branch flips)
  - [lem_global_routing_compat] : global routing compatibility

  The exact Coq statements depend on the existing framework for:
    * certified words W,
    * the parameters A_t, B_t, δ_t, α_t,
    * the prefix indices m_t and router remainders r_{t+1}, j_{t+1},
    * and the “one-step floor” lemma.

  Below we give schematic lemma shapes and leave the proofs as [Admitted],
  to be filled using the concrete definitions from your project.
*)

(*** Small arithmetic helper you can reuse anywhere ***)

Lemma mul_ge_self_if_delta_ge_1 :
  forall (x delta : nat),
    delta >= 1 ->
    x * delta >= x.
Proof.
  intros x delta Hdelta.
  (* write delta = 1 + k *)
  replace delta with (1 + (delta - 1)) by lia.
  rewrite Nat.mul_add_distr_l.
  nia.
Qed.

(* Just to mirror notation in the paper: 2^k *)
Definition pow2 (k : nat) : nat := Nat.pow 2 k.

(* ---------------------------------------------------------------------- *)
(* 1. Non-zeroness of 2^s                                                 *)
(* ---------------------------------------------------------------------- *)

Lemma pow2_nonzero :
  forall s : nat, pow2 s <> 0.
Proof.
  intro s.
  unfold pow2.  
  assert (Hpos : 2 ^ s <> 0).  
  { apply (Nat.pow_nonzero 2 s); lia. }
  lia.
Qed.

(* ---------------------------------------------------------------------- *)
(* 2. Affine functions are stable on congruence classes modulo n          *)
(* ---------------------------------------------------------------------- *)

(**
  This lemma is the key general fact:

    If m1 ≡ m2 (mod n), then for any a,b

      a*m1 + b ≡ a*m2 + b (mod n).

  We phrase it using [Nat.mod] equalities rather than explicit "≡".
*)
Lemma affine_mod_stable :
  forall (a b n m1 m2 : nat),
    n <> 0 ->
    m1 mod n = m2 mod n ->
    (a * m1 + b) mod n = (a * m2 + b) mod n.
Proof.
  intros a b n m1 m2 Hn Hm.
  (* Push the mod inside using add_mod and mul_mod on both sides. *)  
  repeat rewrite Nat.add_mod by exact Hn.
  repeat rewrite Nat.mul_mod by exact Hn.
  (* Now both sides look like ((a*(mX mod n)) + (b mod n)) mod n. *)
  now rewrite Hm.
Qed.

(* A specialization to powers of two, which is what Section 20 uses. *)
Lemma affine_mod_pow2_stable :
  forall (a b s m1 m2 : nat),
    m1 mod pow2 s = m2 mod pow2 s ->
    (a * m1 + b) mod pow2 s = (a * m2 + b) mod pow2 s.
Proof.
  intros a b s m1 m2 Hm.
  apply affine_mod_stable; [apply pow2_nonzero | exact Hm].
Qed.

(* ---------------------------------------------------------------------- *)
(* 3. 2-adic control of a "prefix index" m_t                              *)
(* ---------------------------------------------------------------------- *)

(**
  This is the abstract version of "2-adic control of prefix indices" in
  Section 20, in the simplest useful form:

  Suppose for a given t you have already shown that

      m_t(m) = U_t * m + V_t

  as a function of the external parameter m (this is what you get after
  all the floor / /3 algebra using the one-step lemma and integrality).

  Then, for any s, once you fix m modulo 2^s, the value of m_t(m) modulo
  2^s is also fixed.

  In other words, m_t depends on m *only through* its residue mod 2^s.

  This is exactly the shape you use in the paper: you define U_t, V_t
  and s_t for each prefix step, and then later you choose S* so large
  that S* >= max_t s_t. That ensures that all m_t(m) are stabilized on
  your chosen congruence class of m.
*)

Lemma mt_mod_pow2_stable :
  forall (U_t V_t s : nat) (m1 m2 : nat),
    m1 mod pow2 s = m2 mod pow2 s ->
    (U_t * m1 + V_t) mod pow2 s = (U_t * m2 + V_t) mod pow2 s.
Proof.
  intros U_t V_t s m1 m2 Hm.
  (* Directly a specialization of affine_mod_pow2_stable. *)
  apply affine_mod_pow2_stable; exact Hm.
Qed.

(**
  You would typically use [mt_mod_pow2_stable] like this:

    - After doing the one-step floor algebra, you show that for your
      actual prefix W and step t there exist U_t and V_t so that

          m_t m = U_t * m + V_t

      for all m in some certified class.

    - Then you instantiate [mt_mod_pow2_stable] with those U_t, V_t, s_t:

          m1 mod 2^{s_t} = m2 mod 2^{s_t}
          -> m_t m1 mod 2^{s_t} = m_t m2 mod 2^{s_t}.

    - This is the "2-adic control" of m_t from Lemma 20.1 in the paper.
*)

(*** 1. 2-adic control of prefix indices (Lemma 20.1 in the paper) ***)

(**
  Mathematically:

    Let W_{<= t} be the length-t prefix of a certified word W.
    Then there exist integers U_t, V_t and s_t >= 0 such that

        m_t ≡ U_t * m + V_t  (mod 2^{s_t}),

    where m_t = floor(x_{W_{<=t}}(m) / 18) and
          x_{W_{<=t}}(m) = 6 (A_t m + B_t) + δ_t,
          A_t = 2^{sum_{i < t} α_i}.

    Moreover, one can take s_t <= 1 + sum_{i < t} α_i.
*)

(* Schematic version: you will want to plug in your actual types/functions. *)
Lemma lem_prefix_2adic_rc :
  (* TODO: replace [True] by:
     forall (W : word) (t : nat),
       exists (U_t V_t s_t : nat),
         (* m_t depends on m only via m mod 2^{s_t} *)
         (forall m1 m2,
            m1 mod 2 ^ s_t = m2 mod 2 ^ s_t ->
            m_t W t m1 = m_t W t m2)
         /\ s_t <= 1 + sum_alpha_prefix W t.
  *)
  True.
Proof.
  (* TODO: prove by induction on [t], using your “one-step floor” lemma
     and the fact that division by 3 is invertible modulo powers of 2. *)
  exact I.
Qed.

(*** 2. Routing compatibility (no branch flips) (Lemma 20.2) ***)

(**
  Mathematically:

    Let W be a fixed prefix of length L. Append a same-family padding tail
    so that the final congruence you solve constrains

        m ≡ m* (mod 2^{S*}), with S* >= max_{0 <= t < L} s_t,

    where s_t are from Lemma 20.1, and choose the solution class so that
    the mod-3 part matches the admissibility of W.

    Then along W at this m, all router remainders

        r_{t+1} ≡ 2^{α_t} m_t + k_t (mod 3)

    coincide with the predeclared routers j_{t+1}. Equivalently, every
    row in W remains admissible (no branch flips in the prefix).
*)

Lemma lem_routing_compat_rc :
  (* TODO: replace [True] by something like:

     forall (W : prefix) (L : nat) (m m_star : nat) (S_star : nat),
       length W = L ->
       (* 2-adic bound from Lemma 20.1 *)
       (forall t, t < L -> exists s_t, s_t <= S_star /\ ... ) ->
       m mod 2 ^ S_star = m_star mod 2 ^ S_star ->
       (* mod-3 admissibility condition for W at m *)
       admissible_entry_family W m ->
       (* conclusion: for all t < L, router remainder matches plan *)
       (forall t, t < L ->
          router_remainder W t m = planned_router W t).

     You can then prove this by combining:
       - lem_prefix_2adic_rc: m_t is fixed when m is fixed mod 2^{s_t},
       - the choice S* >= max s_t,
       - and the way you defined r_{t+1} from m_t and α_t, k_t.
  *)
  True.
Proof.
  (* TODO: proof: each m_t is fixed by the 2-adic congruence on m,
     and the mod-3 class was chosen compatibly, so all r_{t+1}
     equal the predeclared j_{t+1}. *)
  exact I.
Qed.

(*** 3. Global routing compatibility (Lemma 20.3) ***)

(**
  Mathematically (Lemma 20.3):

    Let W = T_0 ... T_{n-1} be a fixed certified prefix with planned
    router remainders r_{t+1} in {0,1,2}. Let

        x_t(m) = 6 (A_t m + B_t) + δ_t,
        m_t = floor(x_t / 18),
        j_{t+1} = floor(x_t / 6) mod 3.

    Then there exists a nonempty congruence class M of m
    (m ≡ m* mod 2^{S*} together with a fixed residue mod 3) such that
    for all m in M, the run of W is admissible and

        j_{t+1} = r_{t+1}  for every t,

    equivalently

        A_t m + B_t ≡ r_{t+1} (mod 3) for all t,

    so every division by 3 in the update is integral and the planned
    rows are used throughout W (no branch flips).
*)

Lemma lem_global_routing_compat :
  (* TODO: replace [True] by:

     forall (W : prefix),
       exists (m_star S_star : nat) (c3 : nat),
         (* c3 encodes the mod-3 class (0,1,2) compatible with the entry family *)
         (* M = { m | m ≡ m_star mod 2^{S_star}, and m ≡ c3 mod 3 } is nonempty *)
         (* and for all m in M and all t, the router plan is realized. *)

     The proof follows the paper: induct on t, use your one-step
     composition lemma and the routing-compatibility lemma above.
  *)
  True.
Proof.
  (* TODO: proof by induction on t, threading along the congruence
     class in m and using lem_routing_compat_rc. *)
  exact I.
Qed.


End Routing_compatibility_of_a_fixed_prefix_under_tail_padding.
