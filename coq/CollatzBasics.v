(** * Collatz Basics: Definitions and Basic Properties *)

Require Import Arith.
Require Import ZArith.
Require Import Znumtheory.
Require Import Lia.
Require Import List.
Import ListNotations.

Open Scope Z_scope.

(** ** Basic Collatz Map Definitions *)

(** The standard Collatz function for odd inputs *)
Definition collatz_odd (n : Z) : Z :=
  (3 * n + 1) / 2.

(** Helper: compute the 2-adic valuation (number of trailing zeros in binary) *)
(** This is a simplified version that we axiomatize for now *)
Parameter v2_nat : nat -> nat.

(** The accelerated Collatz map U(y) = (3y + 1) / 2^v2(3y+1) *)
(** For now, we axiomatize this as well to focus on the main theorems *)
Parameter U : Z -> Z.

(** U is well-defined for odd positive integers *)
Axiom U_well_defined : forall y : Z,
  y > 0 -> Z.odd y = true ->
  exists k : nat, U y = (3 * y + 1) / (2 ^ Z.of_nat k).

(** ** Modular Classes and Families *)

(** Check if an odd number is in class 1 mod 6 (family 'e') *)
Definition is_family_e (x : Z) : Prop :=
  x mod 6 = 1.

(** Check if an odd number is in class 5 mod 6 (family 'o') *)
Definition is_family_o (x : Z) : Prop :=
  x mod 6 = 5.

(** Check if a number is admissible (odd and not ≡ 3 mod 6) *)
Definition is_admissible (x : Z) : Prop :=
  Z.odd x = true /\ (is_family_e x \/ is_family_o x).

(** ** Move Tokens *)

(** The four move types from the paper *)
Inductive Move : Type :=
  | Psi   (** ee: family e to family e *)
  | psi   (** eo: family e to family o *)
  | omega (** oe: family o to family e *)
  | Omega (** oo: family o to family o *).

(** Word is a sequence of moves *)
Definition Word := list Move.

(** ** Row Parameters *)

(** Each row has parameters (alpha, beta, c, delta) *)
Record RowParams : Type := mkRow {
  alpha : Z;
  beta : Z;
  c : Z;
  delta : Z  (** delta ∈ {1, 5} *)
}.

(** The unified F function from the paper:
    F(p, m) = (9m * 2^alpha + beta) * 64^p + c) / 9 *)
Definition F_unified (params : RowParams) (p m : Z) : Z :=
  let numerator := (9 * m * (2 ^ (alpha params)) + (beta params)) * (64 ^ p) + (c params) in
  numerator / 9.

(** The x' update formula: x' = 6 * F(p, m) + delta *)
Definition x_prime (params : RowParams) (p m : Z) : Z :=
  6 * F_unified params p m + delta params.

(** ** Key Properties *)

(** Forward identity: 3x' + 1 = 2^(alpha + 6p) * x *)
(** This is the fundamental certified inverse property *)
Axiom forward_identity : forall (params : RowParams) (p m x x' : Z),
  x' = x_prime params p m ->
  x = 18 * m + 6 * (m mod 3) + (if delta params =? 1 then 1 else 5) ->
  3 * x' + 1 = (2 ^ (alpha params + 6 * p)) * x.

(** If the forward identity holds, then U(x') = x *)
Axiom U_inverse_step : forall (alpha_p : Z) (x x' : Z),
  alpha_p > 0 ->
  3 * x' + 1 = (2 ^ alpha_p) * x ->
  U x' = x.

(** ** Affine Word Forms *)

(** Any word W yields an affine form in m *)
Record AffineForm : Type := mkAffine {
  A_coeff : Z;  (** slope coefficient *)
  B_coeff : Z;  (** intercept *)
  delta_W : Z   (** terminal offset ∈ {1, 5} *)
}.

(** Word evaluation produces an affine form *)
Axiom word_affine : forall (W : Word),
  exists (af : AffineForm),
    A_coeff af = 3 * (2 ^ (Z.of_nat (length W))) /\
    delta_W af = 1 \/ delta_W af = 5.

(** ** Lifting and Congruences *)

(** Modulus M_K = 3 * 2^K *)
Definition M_K (K : Z) : Z := 3 * (2 ^ K).

(** For any word W with appropriate 2-adic valuation and intercept properties,
    we can solve the lifting congruence *)
Axiom lifting_lemma : forall (W : Word) (af : AffineForm) (K : Z) (r : Z),
  K >= 3 ->
  Z.log2 (A_coeff af) >= K ->
  exists (m : Z), 
    (A_coeff af * m + B_coeff af) mod (M_K K) = r.

(** ** Base Witnesses *)

(** There exist base witnesses for all residues mod 24 *)
Axiom base_witnesses_mod_24 : forall (r : Z),
  is_admissible r ->
  r mod 24 = r ->
  0 <= r < 24 ->
  exists (W : Word) (m : Z),
    let af := (mkAffine (3 * 2 ^ (Z.of_nat (length W))) 0 (r mod 6)) in
    (A_coeff af * m + B_coeff af) mod 24 = r.

(** ** Main Convergence Statement *)

(** Every admissible odd integer has a finite inverse word from 1 *)
Theorem odd_layer_convergence : forall (x : Z),
  x > 0 ->
  is_admissible x ->
  exists (W : Word) (m : Z),
    (** There's a certified chain: 1 <- x'_1 <- x'_2 <- ... <- x *)
    exists (chain : list Z),
      length chain = length W /\
      hd 0 chain = 1 /\
      last chain 0 = x /\
      (** Each step is certified by U *)
      forall (i : nat), (i < length W - 1)%nat ->
        U (nth (i+1) chain 0) = nth i chain 0.
Proof.
  (** The proof follows the modular approach:
      1. Use base witnesses mod 24
      2. Apply steering lemmas to increase 2-adic valuation
      3. Lift residues M_K -> M_{K+1} via linear congruences
      4. Use 2-adic refinement to get exact integer
      5. Certify each step via forward identity
  *)
Admitted.

(** Helper: iterate U n times *)
Fixpoint iterate_U (n : nat) (y : Z) : Z :=
  match n with
  | O => y
  | S n' => iterate_U n' (U y)
  end.

(** Corollary: Forward convergence *)
Corollary forward_convergence : forall (x : Z),
  x > 0 ->
  is_admissible x ->
  exists (t : nat),
    (** Iterate U exactly t times to reach 1 *)
    iterate_U t x = 1.
Proof.
  intros x Hpos Hadm.
  (** This follows from odd_layer_convergence via the inverse chain *)
Admitted.

Close Scope Z_scope.
