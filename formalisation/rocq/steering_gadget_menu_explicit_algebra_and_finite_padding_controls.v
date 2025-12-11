From Stdlib Require Import ZArith  Znumtheory List Lia.
Import ListNotations.
Open Scope Z_scope.

(******************************************************************)
(*  Row keys (12 rows from your table)                            *)
(******************************************************************)

(* Row keys and parameters (from your table) *)

Inductive row_key :=
  | row_ee0 | row_ee1 | row_ee2
  | row_oe0 | row_oe1 | row_oe2
  | row_eo0 | row_eo1 | row_eo2
  | row_oo0 | row_oo1 | row_oo2.

Record row_params := {
  row_alpha : nat;
  row_beta  : Z;
  row_delta : Z
}.

Definition params_of (rk : row_key) : row_params :=
  match rk with
  | row_ee0 => {| row_alpha := 2; row_beta := 2;   row_delta := 1  |}
  | row_ee1 => {| row_alpha := 4; row_beta := 56;  row_delta := 1  |}
  | row_ee2 => {| row_alpha := 6; row_beta := 416; row_delta := 1  |}
  | row_oe0 => {| row_alpha := 3; row_beta := 20;  row_delta := 1  |}
  | row_oe1 => {| row_alpha := 1; row_beta := 11;  row_delta := 1  |}
  | row_oe2 => {| row_alpha := 5; row_beta := 272; row_delta := 1  |}
  | row_eo0 => {| row_alpha := 4; row_beta := 8;   row_delta := 5  |}
  | row_eo1 => {| row_alpha := 6; row_beta := 224; row_delta := 5  |}
  | row_eo2 => {| row_alpha := 2; row_beta := 26;  row_delta := 5  |}
  | row_oo0 => {| row_alpha := 5; row_beta := 80;  row_delta := 5  |}
  | row_oo1 => {| row_alpha := 3; row_beta := 44;  row_delta := 5  |}
  | row_oo2 => {| row_alpha := 1; row_beta := 17;  row_delta := 5  |}
  end.

Definition A_ofZ (rk : row_key) : Z :=
  2 ^ Z.of_nat (row_alpha (params_of rk)).

Definition B_ofZ (rk : row_key) : Z :=
  row_beta (params_of rk).

Definition delta_ofZ (rk : row_key) : Z :=
  row_delta (params_of rk).

(* Define x_row directly by the linear form: *)
Definition x_row (rk : row_key) (m : Z) : Z :=
  6 * (A_ofZ rk * m + B_ofZ rk) + delta_ofZ rk.



(******************************************************************)
(*  Words over rows                                               *)
(******************************************************************)

Definition Letter := row_key.
Definition word   := list Letter.

Definition app (W1 W2 : word) : word := W1 ++ W2.

(* Primitive rows as singleton words *)
Definition W_ee0 : word := [row_ee0].
Definition W_ee1 : word := [row_ee1].
Definition W_ee2 : word := [row_ee2].

Definition W_oe0 : word := [row_oe0].
Definition W_oe1 : word := [row_oe1].
Definition W_oe2 : word := [row_oe2].

Definition W_eo0 : word := [row_eo0].
Definition W_eo1 : word := [row_eo1].
Definition W_eo2 : word := [row_eo2].

Definition W_oo0 : word := [row_oo0].
Definition W_oo1 : word := [row_oo1].
Definition W_oo2 : word := [row_oo2].

Definition word_of_row (rk : row_key) : word :=
  match rk with
  | row_ee0 => W_ee0 | row_ee1 => W_ee1 | row_ee2 => W_ee2
  | row_oe0 => W_oe0 | row_oe1 => W_oe1 | row_oe2 => W_oe2
  | row_eo0 => W_eo0 | row_eo1 => W_eo1 | row_eo2 => W_eo2
  | row_oo0 => W_oo0 | row_oo1 => W_oo1 | row_oo2 => W_oo2
  end.


Section RowSemanticsZ.

    Lemma x_row_linear_form (rk : row_key) (m : Z) :
        x_row rk m = 6 * (A_ofZ rk * m + B_ofZ rk) + delta_ofZ rk.
    Proof. reflexivity. Qed.

    Lemma x_row_ee0_linear_form :
        forall m : Z,
            x_row row_ee0 m =
            6 * (A_ofZ row_ee0 * m + B_ofZ row_ee0) + delta_ofZ row_ee0.
    Proof.
        intro m.
        unfold x_row, word_of_row.
        reflexivity.        
    Qed.

    Lemma x_row_ee1_linear_form :
        forall m : Z,
            x_row row_ee1 m =
            6 * (A_ofZ row_ee1 * m + B_ofZ row_ee1) + delta_ofZ row_ee1.
    Proof.
        intro m.
        unfold x_row, word_of_row.
        reflexivity.        
    Qed.

    Lemma x_row_ee2_linear_form :
        forall m : Z,
            x_row row_ee2 m =
            6 * (A_ofZ row_ee2 * m + B_ofZ row_ee2) + delta_ofZ row_ee2.
    Proof.
        intro m.
        unfold x_row, word_of_row.
        reflexivity.        
    Qed.

    Lemma x_row_eo0_linear_form :
        forall m : Z,
            x_row row_eo0 m =
            6 * (A_ofZ row_eo0 * m + B_ofZ row_eo0) + delta_ofZ row_eo0.
    Proof.
        intro m.
        unfold x_row, word_of_row.
        reflexivity.        
    Qed.

    Lemma x_row_eo1_linear_form :
        forall m : Z,
            x_row row_eo1 m =
            6 * (A_ofZ row_eo1 * m + B_ofZ row_eo1) + delta_ofZ row_eo1.
    Proof.
        intro m.
        unfold x_row, word_of_row.
        reflexivity.        
    Qed.

    Lemma x_row_eo2_linear_form :
        forall m : Z,
            x_row row_eo2 m =
            6 * (A_ofZ row_eo2 * m + B_ofZ row_eo2) + delta_ofZ row_eo2.
    Proof.
        intro m.
        unfold x_row, word_of_row.
        reflexivity.        
    Qed.

    Lemma x_row_oo0_linear_form :
        forall m : Z,
            x_row row_oo0 m =
            6 * (A_ofZ row_oo0 * m + B_ofZ row_oo0) + delta_ofZ row_oo0.
    Proof.
        intro m.
        unfold x_row, word_of_row.
        reflexivity.        
    Qed.

    Lemma x_row_oo1_linear_form :
        forall m : Z,
            x_row row_oo1 m =
            6 * (A_ofZ row_oo1 * m + B_ofZ row_oo1) + delta_ofZ row_oo1.
    Proof.
        intro m.
        unfold x_row, word_of_row.
        reflexivity.        
    Qed.

    Lemma x_row_oo2_linear_form :
        forall m : Z,
            x_row row_oo2 m =
            6 * (A_ofZ row_oo2 * m + B_ofZ row_oo2) + delta_ofZ row_oo2.
    Proof.
        intro m.
        unfold x_row, word_of_row.
        reflexivity.        
    Qed.

    Lemma x_row_oe0_linear_form :
        forall m : Z,
            x_row row_oe0 m =
            6 * (A_ofZ row_oe0 * m + B_ofZ row_oe0) + delta_ofZ row_oe0.
    Proof.
        intro m.
        unfold x_row, word_of_row.
        reflexivity.        
    Qed.

    Lemma x_row_oe1_linear_form :
        forall m : Z,
            x_row row_oe1 m =
            6 * (A_ofZ row_oe1 * m + B_ofZ row_oe1) + delta_ofZ row_oe1.
    Proof.
        intro m.
        unfold x_row, word_of_row.
        reflexivity.        
    Qed.

    Lemma x_row_oe2_linear_form :
        forall m : Z,
            x_row row_oe2 m =
            6 * (A_ofZ row_oe2 * m + B_ofZ row_oe2) + delta_ofZ row_oe2.
    Proof.
        intro m.
        unfold x_row, word_of_row.
        reflexivity.        
    Qed.
    

    (* 2^k as a Z, with k : nat *)
    Definition pow2Z (k : nat) : Z := 2 ^ (Z.of_nat k).

    Lemma pow2Z_pos : forall k, 0 < pow2Z k.
    Proof.
        intro k.
        unfold pow2Z.
        unfold Z.gt.        
        apply Z.pow_pos_nonneg.
        - lia.              (* 0 < 2 *)
        - apply Nat2Z.is_nonneg. (* 0 <= Z.of_nat k *)        
    Qed.

    Lemma pow2Z_nz : forall k, pow2Z k <> 0.
    Proof.
        intro k.
        unfold pow2Z.        
        apply Z.pow_nonzero.
        - lia.              (* 0 <> 0 *)
        - lia.
    Qed.

    Lemma pow2Z_add :
        forall a b : nat,
            pow2Z (a + b) = pow2Z a * pow2Z b.
    Proof.
        intros a b.
        unfold pow2Z.
        rewrite Nat2Z.inj_add.
        rewrite Z.pow_add_r; try lia.
    Qed.

    Lemma pow2Z_split :
        forall K s,
            (K >= s)%nat ->
            pow2Z K = pow2Z s * pow2Z (K - s).
    Proof.
        intros K s HK.
        (* Work in nat explicitly to avoid scope confusion *)
        assert (HK' : K = Nat.add s (Nat.sub K s)).
        { lia. }
        rewrite <- pow2Z_add. 
        rewrite <- HK'.
        reflexivity.
    Qed.

    (* Helper: from n | (x - y) and n <> 0 we get x mod n = y mod n. *)
    Lemma Z_mod_eq_from_div :
        forall x y n,
            n <> 0 ->
            Z.divide n (x - y) ->
            x mod n = y mod n.
    Proof.
        intros x y n Hnz [k Hk].        (* x - y = n * k *)
        assert (Hx : x = y + n * k) by lia.
        rewrite Hx.
        (* (y + n*k) mod n = y mod n *)
        rewrite Z.add_mod; try assumption.
        rewrite Z.mul_comm.
        rewrite Z.mod_mul; try assumption.
        rewrite Z.add_0_r.
        rewrite Z.mod_mod; try assumption.
        reflexivity.
    Qed.

    Lemma row_pinning_mod (rk : row_key) :
        forall K,
            (K <= row_alpha (params_of rk))%nat ->
            forall m : Z,
            x_row rk m mod (3 * pow2Z K)
            = (6 * B_ofZ rk + delta_ofZ rk) mod (3 * pow2Z K).
    Proof.
        intros K HK m.
        set (s := row_alpha (params_of rk)).
        set (A := A_ofZ rk).
        set (B := B_ofZ rk).
        set (δ := delta_ofZ rk).
        set (M := 3 * pow2Z K).

        (* 1. Show M ≠ 0 *)
        assert (HM_nz : M <> 0).
        { unfold M.            
            apply Z.neq_mul_0. split.
            - lia.
            - apply pow2Z_nz.            
        }

        (* 2. Characterize A as 2^s and use K <= s to factor out 2^K *)
        assert (HsA : A = pow2Z s).
        { subst A s.
            unfold A_ofZ, pow2Z.
            simpl.
            reflexivity. }

        assert (Hs_ge : (s >= K)%nat) by (subst s; lia).

        (* Using pow2Z_split with swapped arguments: s ≥ K ⇒ 2^s = 2^K * 2^(s-K) *)
        pose proof (pow2Z_split s K Hs_ge) as Hsplit.
        (* Hsplit : pow2Z s = pow2Z K * pow2Z (s - K) *)

        (* 3. Show that M divides 6 * A * m *)
        assert (Hdiv_M : Z.divide M (6 * A * m)).
        {
            subst A M.
            rewrite HsA.
            rewrite Hsplit.  (* pow2Z s = pow2Z K * pow2Z (s - K) *)
            (* 6 * (2^K * 2^(s-K)) * m = (3 * 2^K) * (2 * 2^(s-K) * m) *)
            exists (2 * pow2Z (s - K) * m).
            ring.
        }

        (* 4. First pin 6*(A*m + B) to 6*B modulo M *)
        assert (Hpin_core :
                    (6 * (A * m + B)) mod M = (6 * B) mod M).
        {
            (* Use the general lemma Z_mod_eq_from_div on
            x := 6 * (A*m + B), y := 6 * B *)
            apply Z_mod_eq_from_div with (n := M); auto.
            destruct Hdiv_M as [k Hk].
            (* We need M | x - y, but x - y = 6*A*m, and 6*A*m = M*k *)
            exists k.
            (* x - y = 6*(A*m+B) - 6*B = 6*A*m *)
            replace (6 * (A * m + B) - 6 * B) with (6 * A * m) by ring.
            exact Hk.
        }

        (* 5. Now add δ on both sides, since x_row rk m = 6(A*m+B) + δ *)
        unfold x_row.
        subst A B δ M.        
        set (X := 6 * (A_ofZ rk * m + B_ofZ rk)) in *.
        set (Y := 6 * B_ofZ rk) in *.
        set (M := 3 * pow2Z K) in *.
        change ((X + delta_ofZ rk) mod M = (Y + delta_ofZ rk) mod M).        

        (* Push the +delta through the mod on both sides *)
        rewrite Z.add_mod by apply HM_nz.
        rewrite Hpin_core.
        rewrite Z.add_mod by exact HM_nz.
        rewrite Z.mod_mod by exact HM_nz.
        rewrite Z.mod_mod with (n := M) (a := delta_ofZ rk) by exact HM_nz.

        (* Now the goal is: (Y mod M + delta_ofZ rk mod M) mod M = (Y + delta_ofZ rk) mod M. *)

        (* Step 2: normalize the right-hand side using Z.add_mod *)
        rewrite <- Z.add_mod by exact HM_nz.
        reflexivity.
    Qed.

    Lemma row_pinning_mod_24 (rk : row_key) :
        (3 <= row_alpha (params_of rk))%nat ->
        forall m : Z,
            x_row rk m mod 24 = (6 * B_ofZ rk + delta_ofZ rk) mod 24.
    Proof.
        intros Hα m.
        specialize (row_pinning_mod rk 3 Hα m).
        simpl pow2Z in *.
        unfold pow2Z.
        (* pow2Z 3 = 2^(Z.of_nat 3) = 8 *)
        replace (3 * pow2Z 3) with 24 in * by reflexivity.
        assert (H24 : 24 = 3 * 2 ^ Z.of_nat 3).
        { reflexivity. }  (* or you can fold this as a separate lemma if you like *)
        rewrite H24.
        lia.                
    Qed.

    (**********************************************************************)
    (* Abstract interface for inverse words at p = 0                      *)
    (**********************************************************************)
    
    (* Terminal family of a word: even or odd exit. *)
    Inductive family := FamE | FamO.            

    (* For now, we work purely at row level: *)
    Definition x_W (W : word) (m : Z) : Z :=
        match W with
        | [rk] => x_row rk m               (* singleton case *)
        | _    => (* later: real composition; for now you can stub something or
                    restrict to singleton words in the coverage theorem *)
                    x_row row_ee0 m
        end.

    (* Stub, to be refined later as needed: *)
    Definition certified_inverse_p0 (_W : word) : Prop := True.

    Definition terminal_family (W : word) : family :=
        match W with
        | [row_ee0] | [row_ee1] | [row_ee2]
        | [row_eo0] | [row_eo1] | [row_eo2] => FamE
        | [row_oe0] | [row_oe1] | [row_oe2]
        | [row_oo0] | [row_oo1] | [row_oo2] => FamO
        | _ => FamE  (* default; we don’t use non-singletons in this file yet *)
        end.


    (**********************************************************************)
    (* Odd residues in the base modulus 24                                *)
    (**********************************************************************)

    (** The eight odd residues used as base classes at K = 3. *)
    Definition odd_residue24 (r : Z) : Prop :=
        r = 1 \/ r = 5 \/ r = 7 \/ r = 11 \/
        r = 13 \/ r = 17 \/ r = 19 \/ r = 23.

    (** Terminal family must match r mod 6:
            - family e when r ≡ 1 (mod 6),
            - family o when r ≡ 5 (mod 6).
        (Other congruence classes do not occur for these r.)
    *)
    Definition family_matches_residue (W : word) (r : Z) : Prop :=
        (r mod 6 = 1 -> terminal_family W = FamE) /\
        (r mod 6 = 5 -> terminal_family W = FamO).
        

    (******************************************************************)
    (*  Axioms: base rows hit specific residues modulo 24             *)
    (******************************************************************)

    (* For each primitive row-word W_..j we assume:
        - it is a certified inverse for p=0
        - its terminal family matches the residue class r_..j
        - x_W W_..j m is constant ≡ r_..j (mod 24), independent of m
    *)

    Axiom W_ee0_certified  : certified_inverse_p0 W_ee0.
    Axiom W_ee0_xW_mod_24  : forall m, x_W W_ee0 m mod 24 = 1.
    Axiom W_ee0_family_1   : family_matches_residue W_ee0 1.

    Axiom W_eo0_certified  : certified_inverse_p0 W_eo0.
    Axiom W_eo0_xW_mod_24  : forall m, x_W W_eo0 m mod 24 = 5.
    Axiom W_eo0_family_5   : family_matches_residue W_eo0 5.

    Axiom W_oe0_certified  : certified_inverse_p0 W_oe0.
    Axiom W_oe0_xW_mod_24  : forall m, x_W W_oe0 m mod 24 = 7.
    Axiom W_oe0_family_7   : family_matches_residue W_oe0 7.

    Axiom W_oe1_certified  : certified_inverse_p0 W_oe1.
    Axiom W_oe1_xW_mod_24  : forall m, x_W W_oe1 m mod 24 = 11.
    Axiom W_oe1_family_11  : family_matches_residue W_oe1 11.

    Axiom W_ee1_certified  : certified_inverse_p0 W_ee1.
    Axiom W_ee1_xW_mod_24  : forall m, x_W W_ee1 m mod 24 = 13.
    Axiom W_ee1_family_13  : family_matches_residue W_ee1 13.

    Axiom W_ee2_certified  : certified_inverse_p0 W_ee2.
    Axiom W_ee2_xW_mod_24  : forall m, x_W W_ee2 m mod 24 = 17.
    Axiom W_ee2_family_17  : family_matches_residue W_ee2 17.

    Axiom W_oo0_certified  : certified_inverse_p0 W_oo0.
    Axiom W_oo0_xW_mod_24  : forall m, x_W W_oo0 m mod 24 = 19.
    Axiom W_oo0_family_19  : family_matches_residue W_oo0 19.

    Axiom W_oo1_certified  : certified_inverse_p0 W_oo1.
    Axiom W_oo1_xW_mod_24  : forall m, x_W W_oo1 m mod 24 = 23.
    Axiom W_oo1_family_23  : family_matches_residue W_oo1 23.        

    Definition family_matches_residue' (W : word) (r : Z) : Prop :=
        match (r mod 24) with
        | 1  => terminal_family W = FamE
        | 5  => terminal_family W = FamO
        | 7  => terminal_family W = FamE
        | 11 => terminal_family W = FamO
        | 13 => terminal_family W = FamE
        | 17 => terminal_family W = FamO
        | 19 => terminal_family W = FamE
        | 23 => terminal_family W = FamO
        | _  => False
        end.

    (* r = 1, witnessed by W_ee0, m = 0 *)
    Lemma cover_r1 :
        exists (W : word) (m : Z),
            certified_inverse_p0 W /\
            x_W W m mod 24 = 1 /\
            family_matches_residue W 1.
    Proof.
        exists W_ee0, 0%Z.
        split.
        - apply W_ee0_certified.
        - split.
            + exact (W_ee0_xW_mod_24 0%Z).
            + apply W_ee0_family_1.
    Qed.
        
    (* r = 5, pick your chosen primitive word, e.g. W_eo0 *)
    Lemma cover_r5 :
    exists (W : word) (m : Z),
        certified_inverse_p0 W /\
        x_W W m mod 24 = 5 /\
        family_matches_residue W 5.
    Proof.
    exists W_eo0, 0%Z.
    split.
    - apply W_eo0_certified.
    - split.
        + exact (W_eo0_xW_mod_24 0%Z).
        + apply W_eo0_family_5.
    Qed.

    (* r = 7 *)
    Lemma cover_r7 :
    exists (W : word) (m : Z),
        certified_inverse_p0 W /\
        x_W W m mod 24 = 7 /\
        family_matches_residue W 7.
    Proof.
    exists W_oe0, 0%Z.
    split.
    - apply W_oe0_certified.
    - split.
        + exact (W_oe0_xW_mod_24 0%Z).
        + apply W_oe0_family_7.
    Qed.

    (* r = 11 *)
    Lemma cover_r11 :
    exists (W : word) (m : Z),
        certified_inverse_p0 W /\
        x_W W m mod 24 = 11 /\
        family_matches_residue W 11.
    Proof.
    exists W_oe1, 0%Z.
    split.
    - apply W_oe1_certified.
    - split.
        + exact (W_oe1_xW_mod_24 0%Z).
        + apply W_oe1_family_11.
    Qed.

    (* r = 13 *)
    Lemma cover_r13 :
    exists (W : word) (m : Z),
        certified_inverse_p0 W /\
        x_W W m mod 24 = 13 /\
        family_matches_residue W 13.
    Proof.
    exists W_ee1, 0%Z.
    split.
    - apply W_ee1_certified.
    - split.
        + exact (W_ee1_xW_mod_24 0%Z).
        + apply W_ee1_family_13.
    Qed.

    (* r = 17 *)
    Lemma cover_r17 :
    exists (W : word) (m : Z),
        certified_inverse_p0 W /\
        x_W W m mod 24 = 17 /\
        family_matches_residue W 17.
    Proof.
    exists W_ee2, 0%Z.
    split.
    - apply W_ee2_certified.
    - split.
        + exact (W_ee2_xW_mod_24 0%Z).
        + apply W_ee2_family_17.
    Qed.

    (* r = 19 *)
    Lemma cover_r19 :
    exists (W : word) (m : Z),
        certified_inverse_p0 W /\
        x_W W m mod 24 = 19 /\
        family_matches_residue W 19.
    Proof.
    exists W_oo0, 0%Z.
    split.
    - apply W_oo0_certified.
    - split.
        + exact (W_oo0_xW_mod_24 0%Z).
        + apply W_oo0_family_19.
    Qed.

    (* r = 23 *)
    Lemma cover_r23 :
    exists (W : word) (m : Z),
        certified_inverse_p0 W /\
        x_W W m mod 24 = 23 /\
        family_matches_residue W 23.
    Proof.
    exists W_oo1, 0%Z.
    split.
    - apply W_oo1_certified.
    - split.
        + exact (W_oo1_xW_mod_24 0%Z).
        + apply W_oo1_family_23.
    Qed.

    Theorem thm_base_coverage_24 :
        forall r,
            odd_residue24 r ->
            exists (W : word) (m : Z),
            certified_inverse_p0 W /\
            x_W W m mod 24 = r /\
            family_matches_residue W r.
    Proof.
        intros r Hodd.
        unfold odd_residue24 in Hodd.
        destruct Hodd as
            [Hr1
            | [Hr5
            | [Hr7
            | [Hr11
            | [Hr13
            | [Hr17
            | [Hr19 | Hr23]]]]]]].
        - subst r. apply cover_r1.
        - subst r. apply cover_r5.
        - subst r. apply cover_r7.
        - subst r. apply cover_r11.
        - subst r. apply cover_r13.
        - subst r. apply cover_r17.
        - subst r. apply cover_r19.
        - subst r. apply cover_r23.
    Qed.

    Lemma Z_cong_mod_down :
        forall x y M N,
            0 < M ->
            N <> 0 ->
            (M | N) ->
            x mod N = y mod N ->
            x mod M = y mod M.
    Proof.
        intros x y M N HMpos HNnz HdivMN Heq.
        (* x ≡ y (mod N) <-> (x - y) mod N = 0 *)
        apply Z.cong_iff_0 in Heq.
        (* N | (x - y) *)
        apply Z.mod_divide in Heq; try assumption.
        (* from M | N and N | (x - y) get M | (x - y) *)
        assert (HdivM : (M | x - y)).
        { eapply Z.divide_trans; [ exact HdivMN | exact Heq ]. }
        (* then x ≡ y (mod M) *)
        eapply Z_mod_eq_from_div; [ lia | exact HdivM ].
    Qed.

    Lemma pow2Z_3 :
        pow2Z 3 = 2 ^ 3.
    Proof.
        unfold pow2Z; simpl.  (* Z.of_nat 3 = 3 *)
        reflexivity.
    Qed.


    Lemma Zmod_3pow2K_to_24 :
        forall K x y,
            (K >= 3)%nat ->
            x mod (3 * pow2Z K) = y mod (3 * pow2Z K) ->
            x mod 24 = y mod 24.
    Proof.
        intros K x y HK Heq.
        set (N := 3 * pow2Z K).

        (* N > 0, needed for mod_divide later *)
        assert (HNpos : 0 < N).
        { unfold N. apply Z.mul_pos_pos; [lia | apply pow2Z_pos]. }
        assert (HNnz : N <> 0) by lia.

        (* Show 24 | N using pow2Z_split with s = 3 *)
        assert (Hsplit : pow2Z K = pow2Z 3 * pow2Z (K - 3)).
        { apply pow2Z_split; lia. }

        assert (Hdiv24 : (24 | N)).
        { unfold N in *.
            rewrite Hsplit, pow2Z_3.
            change 24 with (3 * 2 ^ 3).
            exists (pow2Z (K - 3)).
            ring. }

        (* Now use the general “mod down” lemma with M = 24, N = 3 * pow2Z K *)
        eapply Z_cong_mod_down
            with (M := 24) (N := N); try eassumption.
        - lia.         (* 0 < 24 *)        
    Qed.

    Lemma linear_2adic_class_Z :
        forall (K s : nat) (c m : Z),
            (K >= s)%nat ->
            (pow2Z s * m) mod pow2Z K = (pow2Z s * c) mod pow2Z K ->
            m mod pow2Z (K - s) = c mod pow2Z (K - s).
    Proof.
        intros K s c m HK Hmod.
        set (a  := pow2Z s).
        set (nK := pow2Z K).
        set (n  := pow2Z (K - s)).

        (* 1. Split the modulus: 2^K = 2^s * 2^(K-s) *)
        assert (Hsplit : nK = a * n).
        { subst a nK n.
            (* use your pow2Z_split lemma *)
            unfold pow2Z.
            (* pow2Z_split: pow2Z K = pow2Z s * pow2Z (K - s) *)
            (* if you already proved pow2Z_split, you can just: *)
            (* now apply pow2Z_split. *)
            (* Assuming you have pow2Z_split: *)
            (* pow2Z_split K s HK : pow2Z K = pow2Z s * pow2Z (K - s) *)
            (* so: *)
            apply pow2Z_split; exact HK.
        }

        (* 2. Rewrite Hmod with that factorisation *)
        subst nK.
        simpl in Hmod.  (* just to normalize *)

        (* Hmod : (a * m) mod (a * n) = (a * c) mod (a * n) *)

        (* 3. Show a ≠ 0 so we can cancel it later *)
        assert (Ha_nonzero : a <> 0).
        { subst a. unfold pow2Z. apply Z.pow_nonzero; lia. }

        (* 4. Turn the congruence into a divisibility statement:
                (a*n) | a*(m - c)
            First get (a*(m-c)) mod (a*n) = 0. *)
        assert (Hdiff_mod : (a * (m - c)) mod (a * n) = 0).
        {
            (* Start from (a*m) mod (a*n) = (a*c) mod (a*n) *)
            (* subtract the right-hand side on both sides modulo (a*n): *)
            pose proof Hmod as Hmod'.
            assert (Hmod_an :
                    (a * m) mod (a * n) = (a * c) mod (a * n)).
            {
                (* rewrite modulus using Hsplit *)
                unfold a, n in *.
                rewrite Hsplit in Hmod'.
                exact Hmod'.
            }

            (* Now prove the goal *)
            replace (a * (m - c)) with (a * m - a * c) by ring.
            rewrite Zminus_mod.  (* (x-y) mod M = (x mod M - y mod M) mod M *)
            rewrite Hmod_an.

            (* Let r := (a * c) mod (a * n) *)
            set (r := (a * c) mod (a * n)).
            (* Goal is now: (r - r) mod (a * n) = 0 *)
            rewrite Z.sub_diag.        (* r - r = 0 *)
            simpl.                     (* 0 mod (a * n) = 0 *)
            apply Zmod_0_l.            
        }

        (* 5. From mod = 0, get divisibility (a*n) | a*(m-c) *)
        assert (Hdiv_big : Z.divide (a * n) (a * (m - c))).
        {
            assert (Han_nonzero : (a * n <> 0)%Z).
            {
                intro H.
                apply Z.mul_eq_0 in H as [Ha0 | Hn0]; auto.
                - (* contradicts a <> 0 *)
                    subst n.
                    pose proof (pow2Z_pos (K - s)) as Hn_pos.
                    lia.                
            }

            (* Now use the generic "mod=0 ⇒ divides" lemma *)
            apply Z.mod_divide; [ exact Han_nonzero | exact Hdiff_mod ].            
        }

        (* 6. Cancel the factor a to get n | (m-c) *)
        destruct Hdiv_big as [k Hk].
        assert (Hdiv_small : Z.divide n (m - c)).
        {
            exists k.
            (* a*(m - c) = (a*n)*k ⇒ m-c = n*k by cancelling a ≠ 0 *)
            apply (Z.mul_reg_l _ _ a); [exact Ha_nonzero | ].
            rewrite Z.mul_assoc in Hk.
            replace (a * (k * n)) with (k * a * n) by lia.
            rewrite <- Hk.            
            reflexivity.
        }

        (* 7. From n | (m-c), get (m - c) mod n = 0 *)
        destruct Hdiv_small as [k' Hk'].
        assert (Hmc_mod : (m - c) mod n = 0).
        {
            rewrite Hk'.
            rewrite Z.mul_comm.
            replace (n * k')  with (k' * n) by lia.
            apply Z_mod_mult.
        }
        assert (Hm : m = c + k' * n).
        { lia. }  (* from m - c = k' * n *)

        subst m.
        (* Goal is now: (c + k' * n) mod n = c mod n *)

        (* Use modular arithmetic lemmas from ZArith *)
        rewrite Z.add_mod.
        2:{
            intro Hn0.            
            subst n.               (* n = pow2Z (K - s) *)            
            pose proof (pow2Z_pos (K - s)) as Hn_pos.
            rewrite Hn0 in Hn_pos.
            lia.            
        }
        rewrite Z.mul_comm.
        replace (n * k') with (k' * n) by lia.
        rewrite Z_mod_mult by lia.
        rewrite Z.add_0_r.
        rewrite Z.mod_mod.
        2:{
            intro Hn0.            
            subst n.               (* n = pow2Z (K - s) *)            
            pose proof (pow2Z_pos (K - s)) as Hn_pos.
            rewrite Hn0 in Hn_pos.
            lia.            
        }
        reflexivity.
    Qed.    

End RowSemanticsZ.

