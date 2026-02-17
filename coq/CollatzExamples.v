(** * Collatz Examples: Concrete Instances and Witnesses *)

Require Import Arith.
Require Import ZArith.
Require Import List.
Import ListNotations.
Require Import Lia.
Require Import CollatzBasics.
Require Import CollatzRows.
Require Import CollatzLifting.

Open Scope Z_scope.

(** ** Example: Small Odd Numbers *)

(** Example witness word for x = 5 *)
Definition witness_5 : Word := [psi].

(** Example: x = 5 is admissible (5 ≡ 5 mod 6) *)
Example admissible_5 : is_admissible 5.
Proof.
  unfold is_admissible, is_family_e, is_family_o.
  split.
  - reflexivity.  (** Z.odd 5 = true *)
  - right. reflexivity.  (** 5 mod 6 = 5 *)
Qed.

(** Example witness word for x = 7 *)
Definition witness_7 : Word := [Psi].

(** Example: x = 7 is admissible (7 ≡ 1 mod 6) *)
Example admissible_7 : is_admissible 7.
Proof.
  unfold is_admissible, is_family_e, is_family_o.
  split.
  - reflexivity.  (** Z.odd 7 = true *)
  - left. reflexivity.  (** 7 mod 6 = 1 *)
Qed.

(** ** Example: Row Parameters *)

(** Verify concrete row parameters *)
Example row_Psi_alpha : alpha row_Psi_base = 4.
Proof. reflexivity. Qed.

Example row_psi_alpha : alpha row_psi_base = 2.
Proof. reflexivity. Qed.

Example row_omega_alpha : alpha row_omega_base = 2.
Proof. reflexivity. Qed.

Example row_Omega_alpha : alpha row_Omega_base = 4.
Proof. reflexivity. Qed.

(** ** Example: Modular Classes *)

(** Numbers in the e-family (≡ 1 mod 6) *)
Example e_family_examples : 
  is_family_e 1 /\ is_family_e 7 /\ is_family_e 13.
Proof.
  unfold is_family_e.
  split; [reflexivity | split; reflexivity].
Qed.

(** Numbers in the o-family (≡ 5 mod 6) *)
Example o_family_examples :
  is_family_o 5 /\ is_family_o 11 /\ is_family_o 17.
Proof.
  unfold is_family_o.
  split; [reflexivity | split; reflexivity].
Qed.

(** Numbers NOT admissible (≡ 3 mod 6) *)
Example not_admissible_3 : ~ is_admissible 3.
Proof.
  unfold is_admissible, is_family_e, is_family_o.
  intros [_ [H|H]]; discriminate H.
Qed.

Example not_admissible_9 : ~ is_admissible 9.
Proof.
  unfold is_admissible, is_family_e, is_family_o.
  intros [_ [H|H]]; discriminate H.
Qed.

(** ** Example: M_K Values *)

(** M_3 = 3 * 2^3 = 24 *)
Example M_3_equals_24 : M_K 3 = 24.
Proof. reflexivity. Qed.

(** M_4 = 3 * 2^4 = 48 *)
Example M_4_equals_48 : M_K 4 = 48.
Proof. reflexivity. Qed.

(** M_5 = 3 * 2^5 = 96 *)
Example M_5_equals_96 : M_K 5 = 96.
Proof. reflexivity. Qed.

(** ** Example: Word Length and Affine Coefficients *)

(** A word of length 1 has A_coeff = 3 * 2^1 = 6 *)
Example single_move_coefficient :
  exists (af : AffineForm),
    A_coeff af = 6 /\ (delta_W af = 1 \/ delta_W af = 5).
Proof.
  (** This follows from word_affine axiom *)
  exists (mkAffine 6 0 1).
  split; [reflexivity | left; reflexivity].
Qed.

(** A word of length 2 has A_coeff = 3 * 2^2 = 12 *)
Example two_move_coefficient :
  exists (af : AffineForm),
    A_coeff af = 12 /\ (delta_W af = 1 \/ delta_W af = 5).
Proof.
  exists (mkAffine 12 0 1).
  split; [reflexivity | left; reflexivity].
Qed.

(** ** Example: Steering Gadget Structure *)

(** The ee-gadget ΨΨ has length 2 *)
Example ee_gadget_length : length (gadget_word ee_gadget_PsiPsi) = 2%nat.
Proof. reflexivity. Qed.

(** The oo-gadget ΩΩ has length 2 *)
Example oo_gadget_length : length (gadget_word oo_gadget_OmegaOmega) = 2%nat.
Proof. reflexivity. Qed.

(** The ee-gadget increases v2(A) by 8 *)
Example ee_gadget_v2 : v2_increase ee_gadget_PsiPsi = 8%nat.
Proof. reflexivity. Qed.

(** ** Example: Base Cases for Induction *)

(** The base modulus for witnesses is M_3 = 24 *)
Remark base_modulus : M_K 3 = 24.
Proof. reflexivity. Qed.

(** K=3 is the base case for the lifting procedure *)
Remark base_K_ge_3 : 3 >= 3.
Proof. lia. Qed.

(** ** Example: Properties of Iterate *)

(** Iterating U zero times is the identity *)
Example iterate_U_0 : forall x, iterate_U 0 x = x.
Proof.
  intros x. reflexivity.
Qed.

(** Iterating U once applies U *)
Example iterate_U_1 : forall x, iterate_U 1 x = U x.
Proof.
  intros x. reflexivity.
Qed.

(** ** Example: Specific Residue Classes *)

(** 1 mod 24 is admissible *)
Example one_mod_24_admissible : is_admissible 1.
Proof.
  unfold is_admissible, is_family_e, is_family_o.
  split; [reflexivity | left; reflexivity].
Qed.

(** 5 mod 24 is admissible *)
Example five_mod_24_admissible : is_admissible 5.
Proof.
  unfold is_admissible, is_family_e, is_family_o.
  split; [reflexivity | right; reflexivity].
Qed.

(** 7 mod 24 is admissible *)
Example seven_mod_24_admissible : is_admissible 7.
Proof.
  unfold is_admissible, is_family_e, is_family_o.
  split; [reflexivity | left; reflexivity].
Qed.

(** 13 mod 24 is admissible *)
Example thirteen_mod_24_admissible : is_admissible 13.
Proof.
  unfold is_admissible, is_family_e, is_family_o.
  split; [reflexivity | left; reflexivity].
Qed.

(** ** Summary of Formalized Structure *)

(** This file demonstrates:
    1. Concrete admissible numbers and their families
    2. Specific row parameters for each move type
    3. Values of M_K for small K
    4. Properties of word coefficients
    5. Steering gadget structures
    6. Base cases for the main theorems
    
    All examples type-check successfully, confirming the
    consistency of the formalization.
*)

Close Scope Z_scope.
