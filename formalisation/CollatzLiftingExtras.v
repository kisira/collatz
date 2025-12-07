(** CollatzLiftingExtras.v *)
From Coq Require Import Arith.PeanoNat Arith.Arith.
From Coq Require Import micromega.Lia.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(* 2^k on nat *)
Fixpoint pow2 (k:nat) : nat :=
  match k with
  | 0 => 1
  | S k' => 2 * pow2 k'
  end.

Definition M (K:nat) : nat := 3 * pow2 K.
Definition a_of (t:nat) : nat := 3 * pow2 t.

Lemma pow2_add : forall a b, pow2 (a + b) = pow2 a * pow2 b.
Proof.
  induction a as [|a IHa]; intro b.
  - simpl. 
    rewrite Nat.add_0_r. 
    reflexivity.
  - simpl. 
    replace (S a + b) with (S (a + b)) by lia.
    simpl. 
    rewrite IHa. 
    simpl.
    lia.    
Qed.

Lemma pow2_pos : forall k, pow2 k > 0.
Proof.
  induction k; simpl; lia.
Qed.

Lemma pow2_nonzero : forall k, pow2 k <> 0.
Proof.
  intro k.
  specialize (pow2_pos k) as H.
  lia.
Qed.

Lemma pow2_mul : forall a b, pow2 (a + b) = pow2 a * pow2 b.
Proof.
  induction a; intro b; simpl.
  - lia.
  - rewrite IHa. nia.
Qed.

Lemma pow2_split : forall a b, b <= a -> pow2 a = pow2 b * pow2 (a - b).
Proof.
  intros a b Hb.
  replace a with (b + (a - b)) at 1 by lia.
  rewrite pow2_add.
  reflexivity.
Qed.


Lemma pow2_ge1 n : 1 <= pow2 n.
Proof.
  induction n; simpl.
  - lia.
  - specialize (IHn).
    lia.
Qed.

Lemma pow2_mod_pow2_0 : forall n m, m <= n -> pow2 n mod pow2 m = 0.
Proof.
  intros n m Hmn.
  rewrite (pow2_split Hmn).
  rewrite Nat.mul_comm.                (* get (.. * pow2 m) mod pow2 m *)
  apply Nat.Div0.mod_mul.  
Qed.

Lemma pow2_lt_succ k : pow2 k < pow2 (S k).
Proof.
  simpl. (* pow2 (S k) = 2 * pow2 k *)
  pose proof (pow2_pos k) as Hpos.
  (* 2 * x > x for x ≥ 1 *)
  replace (pow2 k) with (1 * pow2 k) at 1 by lia.
  specialize (Nat.mul_lt_mono_pos_r 1 2 (pow2 k)).
  (* Or just do it directly: *)
  nia.
Qed.

(* Strictly increasing by stepping from n to m one successor at a time *)
Lemma pow2_lt_mono (n m : nat) :
  n < m -> pow2 n < pow2 m.
Proof.
  revert n.
  induction m as [|m IH]; intros n Hlt; [inversion Hlt|].
  destruct (Nat.lt_ge_cases n m) as [Hnm|Hmn].
  - (* n < m < S m *)
    specialize (IH n Hnm).
    eapply Nat.lt_trans; [exact IH|].
    apply pow2_lt_succ.
  - (* n = m *)
    assert (n = m) by lia. subst n.
    apply pow2_lt_succ.
Qed.

(* For completeness: if n < m, the remainder is pow2 n (nonzero) *)
Lemma pow2_mod_pow2_small : forall n m, n < m -> pow2 n mod pow2 m = pow2 n.
Proof.
  intros n m Hlt.
  apply Nat.mod_small.
  apply pow2_lt_mono.
  exact Hlt.
Qed.

Lemma add_sub_of_le (a b : nat) :
  a <= b -> a + (b - a) = b.
Proof.
  intro H.
  rewrite Nat.add_comm.  
  now apply Nat.sub_add.
Qed.

(* If m ≤ n, then 2^n = 2^m * 2^(n-m); taking mod 2^m gives 0. *)
Lemma pow2_mod0_when_le m n :
  m <= n -> pow2 n mod pow2 m = 0.
Proof.
  intros Hmn.
  pose (k := n - m).
  assert (Hdecomp : n = m + k) by (subst k; symmetry; apply add_sub_of_le; exact Hmn).
  (* Rewrite 2^n as 2^(m+k) = 2^m * 2^k and reduce modulo 2^m. *)
  rewrite Hdecomp, pow2_add.  
  rewrite Nat.mul_comm.
  apply Nat.Div0.mod_mul; exact Hnz.    
Qed.

(* Symmetric helper *)
Lemma pow2_mod0_when_ge m n :
  n <= m -> pow2 m mod pow2 n = 0.
Proof. intros H; apply pow2_mod0_when_le; exact H. Qed.

Lemma pow2_S k : pow2 (S k) = 2 * pow2 k.
Proof. reflexivity. Qed.

Lemma gcd_pow2_step m n :
  Nat.gcd (pow2 (S m)) (pow2 (S n)) = 2 * Nat.gcd (pow2 m) (pow2 n).
Proof.
  rewrite !pow2_S.
  (* gcd (2*x) (2*y) = 2*gcd x y *)
  now rewrite Nat.gcd_mul_mono_l.
Qed. 

(* (* Bridge: pow2 equals 2^n *)
Lemma pow2_spec : forall n, pow2 n = 2 ^ n.
Proof.
  induction n as [|k IH]; simpl; [reflexivity|].
  simpl.
  rewrite IH, Nat.pow_succ_r'.             (* 2^(S k) = 2^k * 2 *)
  now rewrite Nat.mul_comm.                (* 2 * 2^k = 2^k * 2 *)
Qed.

(* Bridge lemma: recursive pow2 equals Nat.pow 2 k *)
Lemma pow2_is_pow : forall k, pow2 k = 2 ^ k.
Proof.
  induction k as [|k IH]; simpl.
  - reflexivity.
  - rewrite IH.                 (* pow2 k -> 2^k *)
    (* 2 * 2^k = 2^k * 2 = 2^(S k) *)
    rewrite Nat.pow_succ_r'.    (* 2^(S k) = 2^k * 2 *)
    now rewrite Nat.mul_comm.
Qed.
 *)
Lemma pow2_0 : pow2 0 = 1. Proof. reflexivity. Qed.

(* --- minimal add_mod / mul_mod / mod_mul (with d<>0) --------------------- *)

Lemma add_mod (a b d : nat) (Hd : d <> 0) :
  (a + b) mod d = (a mod d + b mod d) mod d.
Proof. now apply Nat.Div0.add_mod. Qed.

Lemma mul_mod (a b d : nat) (Hd : d <> 0) :
  (a * b) mod d = ((a mod d) * (b mod d)) mod d.
Proof. now apply Nat.Div0.mul_mod. Qed.

Lemma mod_mul (a d : nat) (Hd : d <> 0) :
  (a * d) mod d = 0.
Proof. now apply Nat.Div0.mod_mul. Qed.

Lemma mod_mod (a d : nat) (Hd : d <> 0) :
  (a mod d) mod d = a mod d.
Proof. now apply Nat.Div0.mod_mod. Qed.

Lemma add_mod_idemp_l (a d : nat) (Hd : d <> 0) :
  (a + d) mod d = a mod d.
Proof.
  rewrite add_mod by exact Hd.
  rewrite Nat.Div0.mod_same by exact Hd.
  rewrite Nat.add_0_r; apply mod_mod; exact Hd.
Qed.

(* --- a couple gcd facts (often missing due to namespace diffs) ----------- *)

(*Nat.gcd_1_l : forall n, Nat.gcd 1 n = 1

Nat.gcd_0_r : forall n, Nat.gcd n 0 = n

Nat.gcd_0_l : forall n, Nat.gcd 0 n = n

Nat.gcd_comm : forall a b, Nat.gcd a b = Nat.gcd b a

Nat.gcd_assoc : forall a b c, Nat.gcd a (Nat.gcd b c) = Nat.gcd (Nat.gcd a b) c*)

Lemma gcd_0_r (a : nat) : Nat.gcd a 0 = a.
Proof. now rewrite Nat.gcd_0_r. Qed.

Lemma gcd_0_l (b : nat) : Nat.gcd 0 b = b.
Proof. now rewrite Nat.gcd_0_l. Qed.

Lemma divide_one_is_one d : Nat.divide d 1 -> d = 1.
Proof.
  intros [k Hk]. (* 1 = d*k *)
  destruct k as [|k']; [now simpl in Hk|].
  (* 1 = d*(S k'). Since d>=1, the only way is d=1 and k'=0 *)
  assert (d <= 1) by (rewrite Hk; destruct d; lia).
  destruct d; lia.
Qed.

(* gcd divides each argument *)
Lemma gcd_divides_r a b : Nat.divide (Nat.gcd a b) b.
Proof. apply Nat.gcd_divide_r. Qed.

Lemma gcd_1_r (a : nat) : Nat.gcd a 1 = 1.
Proof.
  (* gcd(a,1) | 1, hence it must be 1 *)
  apply divide_one_is_one, gcd_divides_r.
Qed.

Lemma gcd_comm (a b : nat) : Nat.gcd a b = Nat.gcd b a.
Proof. apply Nat.gcd_comm. Qed.

Lemma gcd_1_l (a : nat) : Nat.gcd 1 a = 1.
Proof.
  (* symmetry + previous lemma *)
  rewrite Nat.gcd_comm.
  apply gcd_1_r.
Qed.

(* --- a couple of “div exact when mod=0” helpers -------------------------- *)


Lemma div_exact_by_mod (a d : nat) :
  d <> 0 -> a mod d = 0 -> d * (a / d) = a.
Proof.
  intros Hd Hz.
  (* a = d*(a/d) + a mod d *)
  rewrite (Nat.div_mod a d) by exact Hd.
  (* replace the remainder by 0 *)
  rewrite Hz.
  (* d*(a/d) + 0 = d*(a/d) *)
  rewrite Nat.add_0_r.
  rewrite <- (Nat.mul_comm (a / d)  d).
  rewrite Nat.mul_comm.                            (* (a/d * d / d) * d *)
  (* (x*d)/d = x when d <> 0 *)
  rewrite (Nat.div_mul (a / d) d) by lia.          (* becomes (a/d) * d *)  
  (* both sides are now identical *)
  reflexivity.
Qed.

(* Lemma pow64_mod9_via_pow2 : forall p, (pow2 (6*p)) mod 9 = 1.
Proof.
  intro p. rewrite pow2_is_pow, Nat.pow_mul_r.
  (* 2^6 = 64, so (2^(6p)) = 64^p *)
  replace (Nat.pow 2 6) with 64 by reflexivity.
  now apply pow64_mod9_eq1.
Qed. *)

(* --- lifting-specific gcd and congruence lemmas ------------------------- *)

Lemma min_succ_succ (m n : nat) :
  Nat.min (S m) (S n) = S (Nat.min m n).
Proof.  
  destruct (le_ge_dec m n) as [Hmn | Hnm]. (* total order on nat *)
  - (* case m <= n *)
    assert (HSmn : S m <= S n) by lia.
    rewrite (Nat.min_l _ _ HSmn).
    rewrite (Nat.min_l _ _ Hmn).
    reflexivity.
  - (* case n < m, hence n <= m *)
    assert (Hnlem : n <= m) by lia.
    assert (HSnSm : S n <= S m) by lia.
    rewrite (Nat.min_r _ _ HSnSm).
    rewrite (Nat.min_r _ _ Hnlem).
    reflexivity.
Qed.

Lemma gcd_pow2_min m n :
  Nat.gcd (pow2 m) (pow2 n) = pow2 (Nat.min m n).
Proof.
  (* Induct on m, do a case split on n *)
  revert n.
  induction m as [|m IH]; intro n.
  - (* m = 0 *) simpl.               (* pow2 0 = 1 *)
    lia.
  - destruct n as [|n].
    + (* n = 0 *) simpl.
      now rewrite gcd_1_r.
    + (* both S _ *)      

      (* Use the step lemma and the IH *)
      rewrite gcd_pow2_step.
      rewrite IH.
      (* min (S m) (S n) = S (min m n), and pow2 (S k) = 2*pow2 k *)
      now rewrite min_succ_succ, pow2_S.
Qed.


(** gcd(a, M_K) = 3 * 2^{min(t,K)} — a folklore fact used in your lemma. *)
(* Lemma gcd_pow2_min m n :
  Nat.gcd (pow2 m) (pow2 n) = pow2 (Nat.min m n).
Proof.
  (* WLOG split on m ≤ n. *)
  destruct (Nat.le_ge_cases m n) as [Hle|Hge].
  - (* m ≤ n *)
    (* write 2^n = 2^m * 2^(n-m) and factor 2^m out of both sides *)
    pose (r := n - m).
    assert (Hpow : pow2 n = pow2 m * pow2 r).
    { rewrite <-pow2_add. f_equal. lia. }
    rewrite Hpow.
    rewrite Nat.gcd_comm.
    rewrite Nat.gcd_mul_mono_l.
    now rewrite Nat.gcd_1_r, Nat.mul_1_r, Nat.min_l by exact Hle.
  - (* n ≤ m *) 
    (* symmetric case *)
    pose (r := m - n).
    assert (Hpow : pow2 m = pow2 n * pow2 r) by
      (subst r; rewrite <-Nat.add_sub_assoc by exact Hge; rewrite Nat.add_comm; apply pow2_add).
    rewrite Hpow.
    rewrite Nat.gcd_mul_mono_r.
    now rewrite Nat.gcd_1_r, Nat.mul_1_r, Nat.min_r by exact Hge.
Qed.
 *)
Lemma gcd_a_M :
  forall t K, Nat.gcd (a_of t) (M K) = 3 * pow2 (Nat.min t K).
Proof.
  intros t K.
  (* gcd(3*2^t, 3*2^K) = 3*gcd(2^t,2^K) = 3*2^{min(t,K)} *)
  unfold a_of, M.                      (* a_of t = 3 * pow2 t,  M K = 3 * pow2 K *)
  (* pull out the common 3 from the gcd *)
  rewrite Nat.gcd_mul_mono_l.
  (* reduce gcd of powers of 2 *)
  rewrite gcd_pow2_min.
  reflexivity.
Qed.

Lemma gcd_three_pow2_min t K :
  Nat.gcd (3 * pow2 (S t)) (3 * pow2 K) = 3 * pow2 (Nat.min (S t) K).
Proof.
  (* factor the common 3, then use the previous lemma *)
  symmetry.
  rewrite Nat.gcd_mul_mono_l.
  now rewrite gcd_pow2_min.
Qed.

Lemma mod_of_multiple_left (a d m : nat) :
  Nat.divide d a -> (a * m) mod d = 0.
Proof.
  intros [q Hq].                      (* a = d*q *)
  subst a.
  destruct d as [|d'].
  - (* d = 0 *) simpl. lia.   (* (0*m) mod 0 = 0 in Coq's nat semantics *)
  - (* d = S d' *)
    assert (Hassoc : (q * S d') * m = S d' * (q * m)).
    { rewrite Nat.mul_comm with (n := q) (m := S d').
      rewrite <- Nat.mul_assoc.
      reflexivity.
    }
    rewrite Hassoc.            (* (q * S d') * m = S d' * (q * m) *)
    rewrite Nat.mul_comm with (n := S d') (m := q * m).
    apply Nat.Div0.mod_mul.                (* (a*b) mod a = 0 when a<>0 *)    
Qed.

Lemma mod_idem_same' a d : (a mod d) mod d = a mod d.
Proof.
  destruct d as [|d']; [reflexivity|].
  now apply Nat.Div0.mod_mod.
Qed.

Lemma mod_reduce_factor 
  (x d c : nat) :
  c > 0 ->
  (x mod (d * c)) mod d = x mod d.
Proof.
  intros Hcpos.
  destruct d as [|d'].
  - (* d = 0 *)
    (* In Coq, a mod 0 = a, so both sides are x. *)
    simpl. reflexivity.
  - (* d = S d' *)
    set (D := S d' * c).
    assert (HD : D <> 0) by (unfold D; nia).
    (* Division algorithm at modulus D: x = D * (x / D) + (x mod D) *)
    pose proof (Nat.div_mod x D HD) as Hdecomp.
    (* Rewrite the RHS “x mod (S d')” using the decomposition of x at modulus D *)
    replace (x mod (S d')) with
      (((D * (x / D)) + (x mod D)) mod (S d'))
      by (rewrite <- Hdecomp; reflexivity).
    (* Split the sum under mod (S d') *)
    rewrite (Nat.Div0.add_mod (D * (x / D)) (x mod D) (S d')) by lia.
    assert (Hzero : (D * (x / D)) mod (S d') = 0).
    { apply mod_of_multiple_left.
      exists c. unfold D. lia.
    }
    rewrite Hzero.
    rewrite Nat.add_0_l.
    rewrite mod_idem_same'.
    reflexivity.
Qed.

Lemma mod_reduce_factor_comm (x d c : nat) :
  c > 0 ->
  (x mod (c * d)) mod d = x mod d.
Proof.
  intro Hcpos.
  rewrite Nat.mul_comm.
  apply mod_reduce_factor; exact Hcpos.
Qed.

Lemma divides_iff_mod0 (x d : nat) (Hd : d <> 0) :
  Nat.divide d x <-> x mod d = 0.
Proof.
  split.
  - intros [q ->]. now rewrite Nat.Div0.mod_mul by exact Hd.
  - intro Hz.
    apply Nat.Lcm0.mod_divide; assumption.
Qed.

(** A nat-version of “∃m, a m ≡ r (mod N)”  <-> gcd(a,N) | r. *)
Lemma last_row_congruence_targeting_nat :
  forall (t K r : nat),
    let a := a_of t in               (* a = 3 * 2^t *)
    let modN := M K in               (* modN = 3 * 2^K *)
    Nat.gcd a modN = 3 * pow2 (Nat.min t K) ->
    (exists m, (a * m) mod modN = r mod modN)
    <-> Nat.divide (3 * pow2 (Nat.min t K)) r.
Proof.
  intros t K r a modN Hgcd; split.
  - (* (->) If the congruence has a solution, the gcd divides r *)
    intros [m Hcong].
    (* Let d be the explicit gcd value. *)
    set (d := 3 * pow2 (Nat.min t K)).
    assert (Hd : d <> 0).
    { unfold d.
      intro Hd0.
      apply Nat.mul_eq_0 in Hd0 as [H3 | Hpow].
      - lia.      
      - apply pow2_nonzero in Hpow as Hpow'.
        contradiction.
    }
    assert (HmodNpos : modN > 0).
    { unfold modN, M.
      pose proof (pow2_pos K) as HK.
      lia.
    }
    (* Since d | modN (because d = gcd(a,modN)), we can drop the modulus down to d. *)
    assert (Hdown : (a * m) mod d = r mod d).
    { assert (Hdiv_d_modN : Nat.divide d modN).
      { unfold d.
        rewrite <- Hgcd.
        apply Nat.gcd_divide_r.
      }
      destruct Hdiv_d_modN as [c Hc].
      assert (Hcpos : c > 0).
      { destruct c as [|c'].
        - exfalso.
          rewrite Hc in HmodNpos.
          simpl in HmodNpos.
          lia.
        - lia.
      }
      pose proof (mod_reduce_factor_comm (a * m) d Hcpos) as Hmod_am.
      pose proof (mod_reduce_factor_comm r d Hcpos) as Hmod_r.
      rewrite <- Hmod_am.
      rewrite <- Hmod_r.
      rewrite Hc in Hcong.
      apply (f_equal (fun x => x mod d)) in Hcong.
      exact Hcong.
    }
    assert (Hdiv_d_a : Nat.divide d a).
    { unfold d.
      rewrite <- Hgcd.
      apply Nat.gcd_divide_l.
    }
    assert (Hleft0 : (a * m) mod d = 0).
    { apply mod_of_multiple_left.
      exact Hdiv_d_a.
    }
    (* Therefore r mod d = 0, hence d | r. *)
    rewrite Hleft0 in Hdown.
    apply (proj2 (divides_iff_mod0 r Hd)).
    symmetry. exact Hdown.
  - (* (<-) If d divides r, produce a solution m *)
    intro Hdr.
    set (d := 3 * pow2 (Nat.min t K)).
    assert (Hd : d <> 0).
    { unfold d.
      intro Hd0.
      apply Nat.mul_eq_0 in Hd0 as [H3 | Hpow].
      - discriminate H3.
      - apply pow2_nonzero in Hpow.
        contradiction.
    }
    (* Two cases: t <= K or t > K *)
    destruct (Nat.leb_spec t K) as [Hle | Hgt].
    + assert (Hmin : Nat.min t K = t) by (apply Nat.min_l; exact Hle).
      rewrite Hmin in Hdr.
      destruct Hdr as [s Hr].
      exists s.
      rewrite Hr.
      rewrite (Nat.mul_comm a s).
      unfold a, a_of.
      reflexivity.
    + assert (Hmin : Nat.min t K = K) by (apply Nat.min_r; lia).
      unfold d in Hdr.
      rewrite Hmin in Hdr.
      destruct Hdr as [s Hr].
      assert (HmodNnz : 3 * pow2 K <> 0).
      { intro H.
        apply Nat.mul_eq_0 in H as [H3 | Hpow]; [lia | exfalso; apply pow2_nonzero in Hpow; exact Hpow].
      }
      exists 0%nat.
      rewrite Nat.mul_0_r.
      unfold modN, M.
      rewrite Hr.
      rewrite Nat.Div0.mod_0_l by exact HmodNnz.
      rewrite Nat.mul_comm with (s) (3 * pow2 K).
      rewrite Nat.mul_comm.
      now rewrite Nat.Div0.mod_mul.
Qed.

(** Pinning regime: if K <= t then a=3·2^t has all 2-adic weight needed modulo M_K,
    and the last step pins the residue independently of m. *)
Lemma pinning_regime :
  forall t K r,
    K <= t ->
    let a := a_of t in
    let modN := M K in
    r mod modN = 0 ->
    (exists m, (a * m) mod modN = r mod modN).
Proof.
  intros t K r Hle a modN Hrmod.
  exists 0%nat.
  unfold modN, M in *.
  rewrite Nat.mul_0_r.
  rewrite Nat.Div0.mod_0_l by (apply pow2_nonzero).
  symmetry; exact Hrmod.
Qed.
