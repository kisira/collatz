(** CollatzCRT.v — Formalization scaffold for the CRT-tag calculus
    Coq/Rocq 9.1.0 — standard library Nat only (no ssreflect)
*)

From Coq Require Import Arith.Arith Arith.PeanoNat Arith.Euclid.
From Coq Require Import Lia.
From Stdlib Require Import Lqa Lia.

Set Implicit Arguments.
Set Asymmetric Patterns.
Local Open Scope nat_scope.

Module CRT.

(** * Basic arithmetic helpers *)

Lemma mod_small : forall a m, a < m -> Nat.modulo a m = a.
Proof. intros a m H; now apply Nat.mod_small. Qed.

Lemma mod2_even : forall n, Nat.even n = true <-> n mod 2 = 0.
Proof.
  intro n. rewrite Nat.even_spec.
  split; intro H; [apply Nat.even_spec in H |].
  - destruct H as [k ->]. now rewrite Nat.mul_comm, Nat.Div0.mod_mul.
  - destruct (Nat.mod_divides n 2); try lia. intros [k ->].
    now rewrite Nat.even_mul, Bool.andb_true_r.
Qed.

Lemma mod2_odd : forall n, Nat.odd n = true <-> n mod 2 = 1.
Proof.
  intro n. rewrite Nat.odd_spec. split; intro H.
  - destruct H as [k ->]. now rewrite Nat.add_comm, Nat.mod_add, Nat.mod_small by lia.
  - exists (n/2). rewrite <- Nat.div_mod with (a:=n) (b:=2) at 1 by lia.
    rewrite Nat.mod_small; [lia|]. apply Nat.mod_upper_bound; lia.
Qed.

(** * Families modulo 6 *)

Definition family (x:nat) : nat := x mod 6.  (* Values 0..5 *)
Definition family_e (x:nat) : Prop := family x = 1.
Definition family_o (x:nat) : Prop := family x = 5.

(** * CRT tag and its basic properties *)

Definition tag (x:nat) : nat := (x - 1) / 2.

Lemma tag_doubling : forall x, Nat.Odd x -> 2 * tag x = x - 1.
Proof.
  intros x Hodd. destruct Hodd as [k ->]. simpl.
  (* x = 2*k + 1 *)
  replace (2*k + 1 - 1) with (2*k) by lia.
  rewrite Nat.mul_comm, Nat.mul_div_cancel; lia.
Qed.

Lemma tag_spec : forall x, Nat.Odd x -> tag x = (x-1)/2  (* trivial by def *).
Proof. intros; reflexivity. Qed.

(** ** Core CRT congruence: for odd x, 3x+1 ≡ 4 (mod 6) *)

Lemma three_x_plus_one_mod6 :
  forall x, Nat.Odd x -> (3*x + 1) mod 6 = 4.
Proof.
  intros x Hodd.
  (* First, mod 2: *)
  assert(H2 : (3*x + 1) mod 2 = 0).
  { (* 3 ≡ 1 (mod 2), odd x ⇒ x ≡ 1 (mod 2) *)
    apply Nat.mod_eq_0_eq; [lia|].
    exists ( (3*x + 1)/2 ). now rewrite Nat.mul_comm, Nat.div_exact by
      (rewrite Nat.mod_mul; [|lia]; simpl; rewrite <- mod2_odd; apply mod2_odd; now apply Nat.odd_spec). }
  (* Easier route: compute modulo 2 and 3 separately, then pin r in {0..5} *)
  assert (H2' : (3*x + 1) mod 2 = 0).
  { rewrite <- mod2_even. rewrite Nat.even_add, Nat.even_mul, Nat.even_1.
    simpl. rewrite Bool.andb_false_l. simpl. (* even(3x)=even x; odd x ⇒ even(3x)=false *)
    (* Better: directly: odd x => even(3x+1) *)
    clear H2. (* keep H2' instead *)
    (* Using parity facts: even(3x) = even x; odd x -> even(3x+1) *)
    admit. }
  assert (H3' : (3*x + 1) mod 3 = 1) by
    (rewrite Nat.mul_mod_idemp_l by lia; rewrite Nat.mod_same by lia;
     now rewrite Nat.add_0_l, Nat.mod_1_l by lia).
  (* Let r be (3x+1) mod 6, r ∈ {0..5} with r mod 2 = 0 and r mod 3 = 1.
     Only r=4 satisfies both. *)
  set (r := (3*x + 1) mod 6).
  assert (Hrlt : r < 6) by (apply Nat.mod_upper_bound; lia).
  assert (Hr2 : r mod 2 = 0).
  { unfold r. rewrite Nat.mod_mod by lia.
    replace (6 mod 2) with 0 by reflexivity. rewrite Nat.mod_0_l by lia.
    exact H2'. }
  assert (Hr3 : r mod 3 = 1).
  { unfold r. rewrite Nat.mod_mod by lia.
    replace (6 mod 3) with 0 by reflexivity. rewrite Nat.mod_0_l by lia.
    exact H3'. }
  (* Case analysis on r=0..5 *)
  destruct r as [|r']; [easy|].
  destruct r' as [|r'']; [lia|].
  destruct r'' as [|r3]; [ (* r=2 *) simpl in Hr2,Hr3; discriminate Hr3 |].
  destruct r3 as [|r4]; [ (* r=3 *) simpl in Hr2; discriminate Hr2 |].
  destruct r4 as [|r5]; [ (* r=4 *) reflexivity |].
  (* r=5 *) simpl in Hr2; discriminate Hr2.
Admitted.
(* If you prefer no 'Admitted', replace the parity sub-lemma above with a short
   calc: (3x+1) mod 2 = ((3 mod 2)*(x mod 2) + 1) mod 2 = (1*1+1) mod 2 = 0. *)

(** We can avoid the parity detour by a direct boolean computation: *)
Lemma three_x_plus_one_mod6' :
  forall x, Nat.Odd x -> (3*x + 1) mod 6 = 4.
Proof.
  intros x Hodd.
  set (r := (3*x + 1) mod 6).
  assert (Hrlt : r < 6) by (apply Nat.mod_upper_bound; lia).
  assert (Hr2 : r mod 2 = 0).
  { rewrite <- mod2_even. rewrite Nat.even_add, Nat.even_mul, Nat.even_1.
    (* even(3x) = even x; odd x ⇒ Nat.even x = false *)
    rewrite Nat.even_mul. now rewrite Hodd.(proj1) (* not directly usable *).
  Admitted.

(** For use downstream, we export the statement and keep the original lemma name. *)
(* You can keep either of the above; here is a clean axiom you can later discharge: *)
Axiom three_x_plus_one_mod6_ok :
  forall x, Nat.Odd x -> (3*x + 1) mod 6 = 4.

(** ** Tag decomposition and family detection *)

Lemma tag_decomp :
  forall x, Nat.Odd x ->
    (family_e x -> tag x = 3 * (x / 6)) /\
    (family_o x -> tag x = 3 * (x / 6) + 2).
Proof.
  intros x Hodd. unfold family, family_e, family_o, tag.
  remember (x/6) as r. remember (x mod 6) as eps.
  assert (Hx : x = 6*r + eps) by (subst; apply Nat.div_mod; lia).
  assert (Heps : eps < 6) by (subst; apply Nat.mod_upper_bound; lia).
  split; intros Hfam; subst eps; lia.
Qed.

Corollary tag_mod3_family :
  forall x, Nat.Odd x -> (tag x) mod 3 = 0 <-> family_e x.
Proof.
  intros x Hodd. unfold family_e, family.
  remember (x / 6) as r.
  remember (x mod 6) as eps.
  assert (Hx   : x = 6 * r + eps)
    by (subst; apply Nat.div_mod; lia).
  assert (Heps : eps < 6)
    by (subst; apply Nat.mod_upper_bound; lia).

  (* eps is 0..5 *)
  destruct eps as [| [| [| [| [| [|eps_bad]]]]]]; try lia.
  (* Now 6 cases: 0,1,2,3,4,5; the last one (eps_bad) is impossible by Heps *)

  all: split; intro H; lia.
Qed.


(** * Odd-step map  U  (exists-based interface) *)

Definition pow2 (k:nat) := Nat.pow 2 k.

(* Minimal interface: U-step as an existence with its valuation k *)
Record Ustep (x:nat) : Type :=
{ k2    : nat;
  Ux    : nat;
  U_def : (3*x + 1) = pow2 k2 * Ux;
  U_odd : Nat.Odd Ux }.

(* Canonical odd image (if you choose a specific k2 = v2(3x+1)) *)
Definition U_of (x:nat) (u:Ustep x) : nat := Ux u.

Lemma U_is_odd : forall x u, Nat.Odd (U_of x u).
Proof. intros; unfold U_of; now apply U_odd. Qed.

(** Tag drift identity in its easy, algebraic form:
    2*t(x) = x-1  and  2*t(Ux) = Ux - 1  ⇒  t(Ux) - t(x) = (Ux - x)/2. *)

Lemma tag_drift_algebraic :
  forall x u, Nat.Odd x ->
    2 * (tag (U_of x u)) = (U_of x u) - 1 /\
    2 * (tag x) = x - 1.
Proof.
  intros x u Hodd. split.
  - apply tag_doubling. apply U_is_odd.
  - apply tag_doubling. exact Hodd.
Qed.

Corollary tag_drift :
  forall x u, Nat.Odd x ->
    tag (U_of x u) = tag x + ((U_of x u) - x) / 2.
Proof.
  intros x u Hodd.
  (* In nat, we can reason via equalities of doubles to avoid half-subtleties. *)
  assert (H1 := tag_doubling x Hodd).
  assert (H2 := tag_doubling (U_of x u) (U_is_odd x u)).
  (* 2*(t(U)-t(x)) = (U-1) - (x-1) = U - x *)
  replace (tag (U_of x u)) with ( (U_of x u - 1) / 2) by
    (rewrite <- H2; symmetry; apply Nat.div_mul; lia).
  replace (tag x) with ( (x - 1) / 2) by
    (rewrite <- H1; symmetry; apply Nat.div_mul; lia).
  (* Now (U-1)/2 = (x-1)/2 + (U-x)/2  if and only if U-1 = x-1 + (U-x), trivial. *)
  lia.
Qed.

(** * Placeholders for your explicit closed forms (K, q_p, families)
    These mirror the LaTeX: define K, q_p, and the e/o offsets.
*)

Definition q_p (p:nat) : nat := (Nat.pow 4 p - 1) / 3.
Definition K_of (alpha p:nat) : nat := (Nat.pow 2 (alpha + 6*p) - 3) * Nat.pow 4 p.

Definition Delta (eps:nat) (p:nat) : nat :=
  match eps with
  | 1 => 2 * q_p p
  | 5 => 5 * q_p p - 1
  | _ => 0  (* not used; families are 1 or 5 on the odd layer *)
  end.

(** Main explicit formulas (statements prepared; proofs TODO):
    For odd x with x=6r+eps, and parameters (alpha,p) drawn from the row/lift,
    we have d = r*K + Delta_eps, and x' = x + 2d. *)

Theorem explicit_tag_drift :
  forall x r eps alpha p,
    Nat.Odd x ->
    x = 6*r + eps ->
    (eps = 1 \/ eps = 5) ->
    exists u:Ustep x,
      tag (U_of x u) = tag x + (r * K_of alpha p + Delta eps p).
(* TODO: connect (alpha,p) to the actual valuation k2 in u, or mark as a designed step. *)
Admitted.

Theorem explicit_xp_vs_x :
  forall x r eps alpha p,
    Nat.Odd x ->
    x = 6*r + eps ->
    (eps = 1 \/ eps = 5) ->
    exists u:Ustep x,
      U_of x u = x + 2 * (r * K_of alpha p + Delta eps p).
Admitted.

(** * n-step additive drift and affine composition — statements *)

Fixpoint compA (Ks:list nat) : nat :=
  match Ks with
  | nil => 1
  | K::Ks' => (1 + K/3) * compA Ks'  (* informal; operator-analytic over Q *)
  end.
(* For a purely Nat development, you will want to carry numerators/denominators explicitly. *)

End CRT.
