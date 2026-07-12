From Coq Require Import Arith Lia.

(* Convenience: 2^k as a nat. *)
Definition pow2 (k : nat) : nat := Nat.pow 2 k.

(* Useful facts about pow2 *)
Lemma pow2_pos : forall k, pow2 k <> 0.
Proof.
  intro k. unfold pow2. apply Nat.pow_nonzero. lia.
Qed.

Lemma pow2_dvd_pow2 : forall s K, s <= K -> Nat.divide (pow2 s) (pow2 K).
Proof.
  intros s K Hle.
  unfold pow2.
  (* 2^K = 2^s * 2^(K-s) *)
  exists (Nat.pow 2 (K - s)).
  rewrite <- Nat.pow_add_r.
  replace (s + (K - s)) with K by lia.
  ring.
Qed.

(* If two numbers are equal modulo n, then they are equal modulo any divisor d of n.
   We'll use it with d = 2^s dividing n = 2^K (when s <= K). *)
Lemma mod_eq_implies_mod_eq_of_divisor :
  forall a b n d,
    d <> 0 ->
    Nat.divide d n ->
    a mod n = b mod n ->
    a mod d = b mod d.
Proof.
  intros a b n d Hd0 [q Hn] Hmod.
  (* Use mod_mod: (x mod n) mod d = x mod d when d|n *)
  (* We can do it via rewriting with Hn and Nat.mod_mul_r / Nat.mod_mul_l style lemmas.
     A robust approach is to use Nat.mod_eq' characterization via congruence:
       a mod n = b mod n  ->  n | (a-b) in Z, but we're nat-only.
     Here we can do it by "mod twice" trick, since d|n implies:
       (x mod n) mod d = x mod d.
  *)
  assert (Hma : (a mod n) mod d = a mod d).
  {
    (* Standard lemma: Nat.mod_mul_r says (x mod (d*q)) mod d = x mod d *)
    (* We can prove directly using Nat.mod_mul_r if available; otherwise do a small proof. *)
    subst n.
    (* a mod (d*q) mod d = a mod d *)
    (* Coq has Nat.mod_mul_r: forall a b c, c<>0 -> a mod (b*c) mod b = a mod b *)
    (* We'll use it with b=d, c=q. *)
    rewrite Nat.mod_mul_r by exact Hd0.
    reflexivity.
  }
  assert (Hmb : (b mod n) mod d = b mod d).
  {
    subst n.
    rewrite Nat.mod_mul_r by exact Hd0.
    reflexivity.
  }
  (* Now reduce the given equality modulo d *)
  rewrite <- Hma.
  rewrite <- Hmb.
  rewrite Hmod.
  reflexivity.
Qed.

(* Key lemma 1: Congruences at precision K>=s force divisibility of RHS by 2^s,
   when the coefficient is exactly 2^s. *)
Lemma congruence_forces_pow2_divisibility :
  forall (s K RHS mK : nat),
    s <= K ->
    ( (pow2 s * mK) mod (pow2 K) = RHS mod (pow2 K) ) ->
    RHS mod (pow2 s) = 0.
Proof.
  intros s K RHS mK Hle HmodK.
  (* Reduce the congruence mod 2^s *)
  assert (Hred : (pow2 s * mK) mod (pow2 s) = RHS mod (pow2 s)).
  {
    eapply mod_eq_implies_mod_eq_of_divisor
      with (n := pow2 K) (d := pow2 s) (a := pow2 s * mK) (b := RHS).
    - apply pow2_pos.
    - apply pow2_dvd_pow2; exact Hle.
    - exact HmodK.
  }
  (* LHS is 0 because it's a multiple of 2^s *)
  rewrite Nat.mul_comm in Hred.
  (* Nat.mod_mul: (n*m) mod n = 0 *)
  rewrite Nat.mod_mul in Hred by (apply pow2_pos).
  symmetry in Hred.
  exact Hred.
Qed.

(* Key lemma 2: If RHS mod 2^s = 0, then there exists exact m with 2^s*m = RHS. *)
Lemma pow2_divisibility_gives_exact_solution :
  forall (s RHS : nat),
    RHS mod (pow2 s) = 0 ->
    exists m : nat, pow2 s * m = RHS.
Proof.
  intros s RHS Hmod0.
  exists (RHS / pow2 s).
  (* Use Nat.div_mod: RHS = (RHS / n)*n + RHS mod n *)
  pose proof (Nat.div_mod RHS (pow2 s) (pow2_pos s)) as Hdm.
  (* RHS = (RHS / 2^s)*2^s + RHS mod 2^s *)
  rewrite Hmod0 in Hdm.
  (* RHS = (RHS / 2^s)*2^s *)
  nia.
Qed.

(* Main bridge: if you can solve the congruence for all K>=s (with coefficient 2^s),
   then you get an exact integer solution m with 2^s*m = RHS. *)
Lemma congruences_to_exact_pow2_solution :
  forall (s RHS : nat),
    (forall K : nat, s <= K ->
      exists mK : nat,
        (pow2 s * mK) mod (pow2 K) = RHS mod (pow2 K)) ->
    exists m : nat, pow2 s * m = RHS.
Proof.
  intros s RHS Hall.
  specialize (Hall s (le_n s)).
  destruct Hall as [mS HmodS].
  (* From K=s congruence we can already conclude RHS mod 2^s = 0 *)
  have Hdiv0 : RHS mod (pow2 s) = 0.
  {
    (* Use the divisibility lemma with K=s *)
    eapply congruence_forces_pow2_divisibility with (K := s) (mK := mS); try lia.
    exact HmodS.
  }
  apply pow2_divisibility_gives_exact_solution; exact Hdiv0.
Qed.
