From Coq Require Import Arith.Arith.        (* basic nat arithmetic lemmas *)
From Coq Require Import Arith.PeanoNat.    (* Nat.gcd and gcd lemmas *)
From Coq Require Import Lia.               (* lia tactic *)
Require Import Coq.Numbers.Natural.Abstract.NGcd.  (* generic gcd/Bezout framework *)
Require Import  Coq.Numbers.NatInt.NZGcd.



Module Sec18_Residue_targeting_via_a_last_row_congruence.

(* ---------------------------------------------------------------------- *)
(* Section 18: Residue targeting via a last-row congruence                *)
(* ---------------------------------------------------------------------- *)

(**
We work purely arithmetically in [nat], following the notation of
Section 18 of the LaTeX file.

- The outer modulus is    [M_K = 3 * 2^K].
- A last-row step taken from column [p] has coefficient

      a^{(p)} = 6 * 2^{alpha + 6p} = 3 * 2^{alpha+1+6p}.

- For a target residue (called [r^{(p)}] in the paper), the last-row
  congruence is

      a^{(p)} * m ≡ r^{(p)} (mod M_K).

The main lemma says that this congruence is solvable iff

      g^{(p)} := 3 * 2^{min(alpha+1+6p, K)}

divides the target residue.  Subsequent corollaries specialize to the
pinning regime and to target mapping across moduli.
 *)

Section LastRowCongruence.

  Variables alpha p K : nat.

  (** The outer modulus [M_K = 3 * 2^K]. *)
  Definition M_K : nat := 3 * 2 ^ K.
  

  (** The last-row coefficient
        a^{(p)} = 6 * 2^{alpha+6p} = 3 * 2^{alpha+1+6p}.
   *)
  Definition a_p : nat :=
    6 * 2 ^ (alpha + 6 * p).

  (* congruence modulo n *)
  Definition cong (n a b : nat) : Prop :=
    a mod n = b mod n.

  Notation "a ≡ b [ n ]" := (cong n a b)
    (at level 70, no associativity).
  

  (** The “gcd factor”
        g^{(p)} = 3 * 2^{min(alpha+1+6p, K)}.
      In the paper this is written as g^{(p)} := gcd(a^{(p)}, M_K),
      and then evaluated to this closed-form expression.
   *)
  Definition g_p' : nat :=
    3 * 2 ^ Nat.min (alpha + 1 + 6 * p) K.

  Definition g_p : nat := Nat.gcd a_p M_K.

  (** Congruence modulo [M_K], written using [Nat.modulo]. *)
  Definition congr_mod_MK (x y : nat) : Prop :=
    x mod M_K = y mod M_K.

  Notation "x ≡ y [ M_K ]" := (congr_mod_MK x y)
    (at level 70, no associativity).

  (* ------------------------------------------------------------------ *)
  (* Lemma 18.x : Last-row congruence targeting                         *)
  (* ------------------------------------------------------------------ *)

  Lemma cong_mod_equiv :
    forall a b n,
    n <> 0 ->
    cong n a b ->
    exists k, a = b + n * k \/ b = a + n * k.
  Proof.
    intros a b n H Hcong.
    unfold cong in H.
    (* use the standard decomposition a = q*n + r, b = q'*n + r with r = a mod n = b mod n *)
    remember (a / n) as qa.
    remember (b / n) as qb.
    remember (a mod n) as r.
    assert (Ha0 : a = a / n * n + a mod n).
    { 
      replace (a = a / n * n) with (a = (a / n) * n) by reflexivity.
      rewrite Nat.mul_comm with (n := a / n) (m := n).      
      apply (Nat.div_mod a n). (* here you may need a hypothesis n <> 0; if so, use it instead of [] *)
      lia. (* or whatever you use to discharge n <> 0 *)
    }

    (* Now turn that into the form with qa and r *)
    assert (Ha : a = qa * n + r).
    {
      (* replace a / n by qa and a mod n by r in Ha0 *)
      rewrite <- Heqqa in Ha0.
      rewrite <- Heqr  in Ha0.  
      (* now Ha0 is exactly a = qa * n + r *)
      exact Ha0.
    }
    (* standard div/mod decomposition for b *)
    assert (Hb0 : b = b / n * n + b mod n).
    { 
      replace (b = b / n * n) with (b = (b / n) * n) by reflexivity.
      rewrite Nat.mul_comm with (n := b / n) (m := n).
      apply Nat.div_mod; assumption. }

    (* express b using qb and r, like we did for a *)
    assert (Hb : b = qb * n + r).
    {
      (* turn b / n into qb *)
      rewrite <- Heqqb in Hb0.

      (* now show that b mod n = r, using congruence and Heqr *)
      assert (Hbr : b mod n = r).
      {
        (* Hcong : a mod n = b mod n, Heqr : r = a mod n *)
        (* goal: b mod n = r *)
        rewrite Heqr.              (* goal becomes: b mod n = a mod n *)
        symmetry; exact Hcong.     (* since a mod n = b mod n *)
      }

      rewrite Hbr in Hb0.
      exact Hb0.
    }

    (* now compare qa and qb to get one of a = b + n*k or b = a + n*k *)
    destruct (Nat.leb_spec qa qb) as [Hle | Hgt].
    - (* qa <= qb *)
      exists (qb - qa).
      right.
      rewrite Ha, Hb.
      ring_simplify.
      replace (qb - qa) with (Nat.sub qb qa) by lia.
      (* standard Nat algebra to rearrange *)
      assert (Hqb : qb = qa + (qb - qa)) by lia.
      rewrite Hqb at 1.
      rewrite Nat.mul_add_distr_r.
      rewrite Nat.mul_comm with (n := qa) (m := n).
      rewrite Nat.mul_comm with (n := qb - qa) (m := n).
      reflexivity.     
    - (* qa > qb *)
      exists (qa - qb).
      left.
      rewrite Ha, Hb.
      ring_simplify.
      replace (qa - qb) with (Nat.sub qa qb) by lia.
      lia.
  Qed.

  Lemma Sg_eq_1_from_prod (g k : nat) :
    S g * k = 1 -> S g = 1.
  Proof.
    intros H.
    destruct k as [|k'].
    - (* k = 0: impossible *)
      exfalso.                    (* goal: False *)
      rewrite Nat.mul_0_r in H.   (* H: 0 = 1 *)
      discriminate H.
    - (* k = S k' >= 1 *)
      assert (Hle : S g <= S g * S k').
      {
        rewrite <- Nat.mul_1_r with (n := S g).
        rewrite Nat.mul_1_r at 2.
        apply Nat.mul_le_mono_nonneg_l; lia.
      }
      rewrite H in Hle.
      lia.
  Qed.

  Lemma mul_eq_1_l (g k : nat) :
    1 = g * k -> g = 1.
  Proof.
    intros H.
    destruct g as [| g'].
    - (* g = 0: 1 = 0 * k is impossible *)
      simpl in H. discriminate H.
    - (* g = S g' *)
      symmetry in H.                (* now H : S g' * k = 1 *)
      apply Sg_eq_1_from_prod in H. (* H : S g' = 1 *)
      exact H.                      (* goal is S g' = 1 *)
  Qed.

  Lemma gcd_factor_coprime :
    forall ap,
      M_K <> 0 ->
      let d := Nat.gcd ap M_K in
      forall a0 n0,
        ap = a0 * d ->
        M_K = n0 * d ->
        Nat.gcd a0 n0 = 1.
  Proof.
    intros ap HMK a0 n0 Ha0 Hn0.    
    (* d is Nat.gcd ap M_K by definition *)
    set (g := Nat.gcd a0 n0).
    (* g divides a0 and n0 *)
    assert (Hg_a0 : Nat.divide g a0).
    { subst g. apply Nat.gcd_divide_l. }
    assert (Hg_n0 : Nat.divide g n0).
    { subst g. apply Nat.gcd_divide_r. }
    assert (Hdgg : Nat.divide (g * g) ap).
    {
      unfold Nat.divide.
      destruct Hg_n0 as [z Hz].
      destruct Hg_a0 as [k Hk].         (* Hk : a0 = g * k *)
      exists (z * k).
      rewrite Hn0.                       (* ap = n0 * a0 *)
      rewrite Hz.                        (* ap = (z * g) * a0 *)
      rewrite Hk.                        (* ap = (z * g) * (g * k) *)
      (* Now rearrange to (g * g) * (z * k) *)

      (* ap = (z * g) * (g * k) *)
      repeat rewrite Nat.mul_assoc.      (* ap = z * g * g * k *)
      lia.      
    }

    intros HMKfact.  (* HMKfact : M_K = Ha0 * a0 *)
    set (h := Nat.gcd n0 Ha0).
    assert (Hh_n0  : Nat.divide h n0).
    { subst h; apply Nat.gcd_divide_l. }

    assert (Hh_Ha0 : Nat.divide h Ha0).
    { subst h; apply Nat.gcd_divide_r. }
    (* h * a0 divides ap *)
    assert (Hd_ap : Nat.divide (h * a0) ap).
    {
      unfold Nat.divide.
      destruct Hh_n0 as [k Hk].            (* n0 = h * k *)
      exists k.
      rewrite Hn0.                         (* ap = n0 * a0 *)
      rewrite Hk.                          (* ap = (h * k) * a0 *)
      repeat rewrite Nat.mul_assoc.
      reflexivity.
    }

    (* h * a0 divides M_K *)
    assert (Hd_MK : Nat.divide (h * a0) M_K).
    {
      unfold Nat.divide.
      destruct Hh_Ha0 as [k Hk].           (* Ha0 = h * k *)
      exists k.
      rewrite HMKfact.                     (* M_K = Ha0 * a0 *)
      rewrite Hk.                          (* M_K = (h * k) * a0 *)
      repeat rewrite Nat.mul_assoc.
      reflexivity.
    }
    (* 1. a0 <> 0 *)
    assert (Ha0_div_MK : Nat.divide a0 M_K).
    { subst a0; apply Nat.gcd_divide_r. }
    assert (Ha0_nonzero : a0 <> 0).
    {
      intro Ha0_zero.
      destruct Ha0_div_MK as [k Hk].    (* Hk : M_K = a0 * k *)
      rewrite Ha0_zero in Hk.           (* M_K = 0 * k *)
      replace (k * 0) with (0 * k) in Hk by lia.
      rewrite Nat.mul_0_l in Hk.        (* M_K = 0 *)
      apply HMK.                        (* use HMK : M_K <> 0 *)
      rewrite Hk.                       (* turn M_K <> 0 into 0 <> 0 *)
      reflexivity.                      (* contradiction *)
    }

    (* 2. (h * a0) divides a0 *)
    assert (Hh_a0 : Nat.divide (h * a0) a0).
    {
      subst a0.  (* now a0 is Nat.gcd ap M_K *)
      (* goal: Nat.divide (h * Nat.gcd ap M_K) (Nat.gcd ap M_K) *)
      eapply Nat.gcd_greatest; eauto.      
      (*   Hd_ap : Nat.divide (h * Nat.gcd ap M_K) ap
          Hd_MK : Nat.divide (h * Nat.gcd ap M_K) M_K
        so gcd_divide fits perfectly *)
    }

    destruct Hh_a0 as [k0 Hk0].  (* a0 = (h * a0) * k0 *)

    rewrite Nat.mul_assoc in Hk0.
    rewrite <- Nat.mul_assoc in Hk0.
    rewrite <- Nat.mul_1_l with (n := a0) in Hk0.
    rewrite Nat.mul_1_l in Hk0.       (* left side: 1 * a0 -> a0 *)    
    (* Now: Hk0 : a0 = k0 * (h * a0) *)
    repeat rewrite Nat.mul_assoc in Hk0.        
    (* Hk0 : a0 = (k0 * h) * a0 *)
    rewrite Nat.mul_comm with (n := (k0 * h)) (m := a0) in Hk0.        
    (* 1. Build the nicer equation: a0 * 1 = a0 * (k0 * h) *)
    assert (Hk0' : a0 * 1 = a0 * (k0 * h)).
    {
      (* goal is now: a0 * 1 = a0 * (k0 * h) *)
      rewrite Nat.mul_1_r.  (* a0 * 1 -> a0, goal becomes a0 = a0 * (k0 * h) *)
      exact Hk0.            (* solved by the original equality *)
    }
    clear Hk0.
    rename Hk0' into Hk0.
    (* Now: Hk0 : a0 * 1 = a0 * (k0 * h) *)

    (* 2. Cancel a0 on both sides *)
    apply Nat.mul_cancel_l in Hk0; [ | exact Ha0_nonzero ].
    (* Hk0 : 1 = k0 * h *)

    (* 3. Flip and use your mul_eq_1_l lemma *)
    rewrite Nat.mul_comm in Hk0.     (* 1 = h * k0 *)
    apply mul_eq_1_l in Hk0.         (* mul_eq_1_l : 1 = g * k -> g = 1 *)
    exact Hk0.                       (* h = 1 *)
  Qed.


  Lemma Nat_coprime_bezout
    (a0 n0 : nat) :
    a0 <> 0 ->
    n0 <> 0 ->
    Nat.gcd a0 n0 = 1 ->
    exists u v, u * a0 = 1 + v * n0.
  Proof.
    intros Ha0_nz Hn0_nz Hgcd1.
    (* Nat.gcd_bezout gives a disjunction of two Bezout identities *)
    destruct (Nat.gcd_bezout a0 n0) as [Hbez | Hbez].
    - (* Case 1: Bezout a0 n0 (gcd a0 n0) *)
      rewrite Hgcd1 in Hbez.
      (* By definition, Nat.Bezout a b p means:
          exists u v, u * a = p + v * b
        so we can just destruct it. *)
      destruct Hbez as [u [v Huv]].
      (* Huv : u * a0 = 1 + v * n0 *)
      exists u, v; exact Huv.
    - (* Case 2: Bezout n0 a0 (gcd a0 n0) *)
      rewrite Hgcd1 in Hbez.
      (* Use bezout_com to flip the roles.
        The doc you quoted matches this type:
          Nat.bezout_com :
            forall a b,
              a <> 0 -> b <> 0 ->
              Nat.Bezout a b 1 ->
              Nat.Bezout b a 1
      *)
      pose proof (Nat.bezout_comm n0 a0 1 Ha0_nz) as Hbez'.
      (* Hbez' : Nat.Bezout a0 n0 1 *)

      (* Now we have Bezout a0 n0 1 in Hbez' *)
      destruct Hbez' as [u [v Huv]].
      exact Hbez.
      (* Huv : u * a0 = 1 + v * n0 *)
      exists u, v; exact Huv.
  Qed.

Lemma a_p_nonzero :
  a_p <> 0.
Proof.  
  unfold a_p.
  (* use the standard lemma: a * b = 0 -> a = 0 \/ b = 0 *)
  intros H.
  apply Nat.mul_eq_0 in H as [H6 | Hpow].

  - (* 6 = 0 is impossible *)
    discriminate H6.

  - (* 2 ^ (alpha + 6 * p) = 0 is impossible *)
    (* there is a lemma: Nat.pow_nonzero : forall a n, a <> 0 -> a ^ n <> 0 *)
    assert (Hpow' : 2 ^ (alpha + 6 * p) <> 0).
    { apply Nat.pow_nonzero. discriminate. }
    contradiction.
Qed.


  Lemma lem_last_row_p_backward (r : nat) :
    M_K <> 0 ->
    Nat.divide g_p r ->
    exists m, a_p * m ≡ r [M_K].
  Proof.
    intros HMK Hdiv.
    unfold g_p in Hdiv.
    set (d := Nat.gcd a_p M_K) in *.

    (* r is a multiple of d *)
    destruct Hdiv as [r0 Hr0d].        (* Hr0d : r = r0 * d *)

    (* d divides a_p and M_K *)
    assert (Hd_ap : Nat.divide d a_p).
    { subst d; apply Nat.gcd_divide_l. }
    assert (Hd_MK : Nat.divide d M_K).
    { subst d; apply Nat.gcd_divide_r. }

    destruct Hd_ap as [a0 Ha0_raw].    (* a_p = d * a0 *)
    destruct Hd_MK as [n0 Hn0_raw].    (* M_K = d * n0 *)
    assert (Ha0_nz : a0 <> 0).
    {
      intro Ha0z.              (* assume a0 = 0 *)
      subst a0.                (* Ha0_raw becomes: a_p = 0 * d *)
      rewrite Nat.mul_0_l in Ha0_raw.
      (* Now Ha0_raw : a_p = 0 *)
      apply a_p_nonzero.       (* contradiction with a_p <> 0 *)
      exact Ha0_raw.
    }
    assert (Hn0_nz : n0 <> 0).
    {
      intro Hn0z.              (* assume n0 = 0 *)
      subst n0.                (* Hn0_raw becomes: M_K = 0 * d *)
      rewrite Nat.mul_0_l in Hn0_raw.
      (* Now Hn0_raw : M_K = 0 *)

      apply HMK.               (* contradiction with M_K <> 0 *)
      exact Hn0_raw.
    }
    assert (Hgcd1 : Nat.gcd a0 n0 = 1).
    {
      (* this uses your previously proven lemma gcd_factor_coprime *)
      pose proof (gcd_factor_coprime a_p HMK a0 n0 Ha0_raw Hn0_raw) as H.
      exact H.
    }
    assert (Hbez_ex : exists u v, u * a0 = 1 + v * n0).
    {
      apply Nat_coprime_bezout; [ exact Ha0_nz | exact Hn0_nz | exact Hgcd1 ].
    }
    destruct Hbez_ex as [u [v Hbez]].
    (* Hbez : u * a0 = 1 + v * n0 *)    
    (* Our candidate solution: m = u * r0 *)
    exists (u * r0).
    unfold congr_mod_MK.
    (* 1. Expand r, a_p, M_K using the factorizations *)
    rewrite Ha0_raw.        (* a_p = a0 * d *)
    rewrite Hr0d.           (* r  = r0 * d *)
    rewrite Hn0_raw.        (* M_K = n0 * d *)

    (* Now goal: ((a0 * d) * (u * r0)) mod (n0 * d) = (r0 * d) mod (n0 * d) *)
    replace (a0 * d * (u * r0)) with ((d * u) * a0  * r0) by lia.
    replace (d * u * a0 * r0)
      with (d * (u * a0) * r0)
      by (repeat rewrite Nat.mul_assoc; reflexivity).

    (* Now use Bézout: u * a0 = 1 + v * n0 *)
    rewrite Hbez.
    (* Show modulus nonzero *)
    assert (Hnd : n0 * d <> 0).
    {
      intro H.
      apply HMK.
      rewrite Hn0_raw.
      exact H.
    }
    replace (d * (1 + v * n0) * r0)
      with ((1 + v * n0) * (r0 * d)) by lia.
    rewrite Nat.mul_add_distr_r.
      
    (* (1 * (r0 * d) + (v * n0) * (r0 * d)) mod (n0 * d) *)

    rewrite Nat.mul_1_l.

    rewrite Nat.Div0.add_mod by exact Hnd.

    replace ((v * n0) * (r0 * d))
      with ((v * r0) * (n0 * d)) by lia.    

    rewrite Nat.Div0.mod_mul by exact Hnd.
    rewrite Nat.add_0_r.
    rewrite Nat.Div0.mod_mod by exact Hnd.
    reflexivity.
  Qed.

  Lemma lem_last_row_p_forward (r : nat) :
    M_K <> 0 ->
    (exists m, a_p * m ≡ r [M_K]) ->
    Nat.divide g_p r.
  Proof.
    intros HMK [m Hcong].
    unfold congr_mod_MK in Hcong.
    (* We'll work with d = g_p for a bit *)
    set (d := g_p).

    (* d divides a_p and M_K, by definition of g_p *)
    assert (Hd_ap : Nat.divide d a_p).
    { subst d. unfold g_p. apply Nat.gcd_divide_l. }
    assert (Hd_MK : Nat.divide d M_K).
    { subst d. unfold g_p. apply Nat.gcd_divide_r. }

    (* Turn the congruence mod M_K into an explicit equation with a multiple of M_K *)
    (* Here we use your generic congruence + cong_mod_equiv *)
    assert (Hcong_cong : cong M_K (a_p * m) r).
    { unfold cong. exact Hcong. }

    destruct (cong_mod_equiv (a_p * m) r M_K HMK Hcong_cong)
      as [k [Hcase1 | Hcase2]].

    - (* Case 1: a_p * m = r + M_K * k *)
      (* d divides a_p * m *)
      assert (Hd_apm : Nat.divide d (a_p * m)).
      {
         unfold Nat.divide in *.
        destruct Hd_ap as [q Hq].   (* q : nat, Hq : a_p = d * q *)
        exists (q * m).
        rewrite Hq.                 (* a_p * m = (d * q) * m *)
        lia.        
      }

      (* d divides M_K * k *)
      assert (Hd_MKk : Nat.divide d (M_K * k)).
      {
        unfold Nat.divide in *.
        destruct Hd_MK as [q Hq].  (* q : nat, Hq : M_K = d * q or q * d depending on your lemma *)
        exists (q * k).
        rewrite Hq.
        (* Now we have (d * q) * k or (q * d) * k; we want d * (q * k) *)
        repeat rewrite Nat.mul_assoc.
        lia.        
      }


      (* Rewrite Hd_apm using the equality a_p * m = r + M_K * k *)
      rewrite Hcase1 in Hd_apm.
      (* Now: d | (r + M_K * k) and d | (M_K * k) ⇒ d | r *)
      assert (Hdr : Nat.divide d r).
      {
        (* Step 1: d divides (r + M_K * k) - (M_K * k) *)
        assert (Hdr' : Nat.divide d ((r + M_K * k) - (M_K * k))).
        {
          (* divide_sub_r p m n: p|m -> p|n -> n <= m -> p|(m - n) *)
          apply (Nat.divide_sub_r d (r + M_K * k) (M_K * k));
            try assumption.
          (* side condition: M_K * k <= r + M_K * k *)          
        }

        (* Step 2: (r + M_K * k) - (M_K * k) = r *)
        replace ((r + M_K * k) - (M_K * k)) with r in Hdr'
          by (lia).

        exact Hdr'.
      }

      subst d. exact Hdr.

    - (* Case 2: r = a_p * m + M_K * k *)
      (* d divides a_p * m *)
      (* d divides a_p * m *)
      assert (Hd_apm : Nat.divide d (a_p * m)).
      {
        unfold Nat.divide in *.
        destruct Hd_ap as [qa Hqa].     (* qa : nat, Hqa : a_p = d * qa (or qa * d) *)
        exists (qa * m).
        rewrite Hqa.
        (* (d * qa) * m = d * (qa * m) *)
        repeat rewrite Nat.mul_assoc.
        lia.                     (* add a mul_comm if your Hqa is qa * d *)
      }

      (* d divides M_K * k *)
      assert (Hd_MKk : Nat.divide d (M_K * k)).
      {
        unfold Nat.divide in *.
        destruct Hd_MK as [qM HqM].      (* qM : nat, HqM : M_K = d * qM (or qM * d) *)
        exists (qM * k).
        rewrite HqM.
        (* (d * qM) * k = d * (qM * k) *)
        repeat rewrite Nat.mul_assoc.
        lia.                     (* again, mul_comm if needed *)
      }


      (* d divides their sum: a_p*m + M_K*k = r *)
      assert (Hdr : Nat.divide d (a_p * m + M_K * k)).
      { apply Nat.divide_add_r; assumption. }
      rewrite <- Hcase2 in Hdr.
      subst d. exact Hdr.
  Qed.

  
  (**
    Lemma [Last-row congruence targeting] (lem:last-row-p).

    In the notation above, fix [alpha], [p], [K] and let [r] play
    the role of the paper’s [r^{(p)}].

    The paper states:

      "The congruence

           a^{(p)} m ≡ r^{(p)} (mod M_K)

       is solvable iff g^{(p)} := gcd(a^{(p)}, M_K)
       = 3 * 2^{min(alpha+1+6p, K)} divides r^{(p)}."

    We encode this directly over [nat] using [Nat.divide].
   *)
  Lemma lem_last_row_p (r : nat) :
    M_K <> 0 ->
    (exists m, a_p * m ≡ r [M_K]) <->
    Nat.divide g_p r.
  Proof.    
    split.
    - apply lem_last_row_p_forward. exact H.
    - apply lem_last_row_p_backward. exact H.
  Qed.

  Lemma pow_ge_1 : forall m n : nat, 1 <= m -> 1 <= m ^ n.
  Proof.
    intros m n H_m.
    induction n as [| n' IHn'].
    - (* Base case: n = 0 *)
      simpl. (* m ^ 0 = 1 *)
      apply le_n. (* Proves 1 <= 1 *)
    - (* Induction step: n = S n' *)
      simpl. (* m ^ (S n') = m * (m ^ n') *)
      (* Goal: 1 <= m * m ^ n' *)
      assert( H_mn' : 1 <= m ^ n').
      {exact IHn'. }
      (* Use standard library lemmas for arithmetic *)
      replace 1 with (1 * 1) by lia.
      apply Nat.mul_le_mono. exact H_m.
      exact H_mn'.
  Qed.
      

  (* ------------------------------------------------------------------ *)
  (* Corollary 18.x : Pinning regime as a special case (cor:pinning)    *)
  (* ------------------------------------------------------------------ *)

  (**
    Corollary [Pinning regime as a special case] (cor:pinning).

    Quoting the paper (in nat-ified form):

      "In the setting of the last-row congruence lemma, if
       alpha+1+6p >= K, then for M_K = 3*2^K one has

           x' ≡ 6*k^{(p)} + δ   (mod M_K)

       independently of m. In particular, once routing admissibility
       is guaranteed, any last step with alpha+1+6p >= K pins the final
       residue at modulus M_K."

    Here we model a single last-row step as

         x' = 6 * (2^{alpha+6p} * m + k) + delta

    and show that, in the pinning regime alpha+1+6p >= K, the
    result is congruent to the "constant part" [6*k+delta],
    independently of [m], modulo [M_K].
   *)

   Corollary cor_pinning (k delta : nat) :
    alpha + 1 + 6 * p >= K ->
    forall m,
      let x' := 6 * (2 ^ (alpha + 6 * p) * m + k) + delta in
      x' ≡ (6 * k + delta) [M_K].
  Proof.
    intros Hexp m.
    unfold congr_mod_MK.
    (* expand the let-binding for x' *)

    (* For readability: *)
    set (A := 2 ^ (alpha + 6 * p)).

    (* Goal is now:
        (6 * (A * m + k) + delta) mod M_K
        = (6 * k + delta) mod M_K
    *)

    (* Expand the product and regroup *)
    rewrite Nat.mul_add_distr_l.      (* 6*(A*m + k) = 6*(A*m) + 6*k *)
    (* We want to see LHS as [6*(A*m)] + [6*k+delta] *)
    rewrite <- Nat.add_assoc.
    rewrite (Nat.add_comm (6 * k) delta).
    rewrite Nat.add_assoc.
    (* Now LHS is (6 * (A * m) + (6 * k + delta)) mod M_K *)

    (* It suffices to show 6 * (A * m) ≡ 0 [M_K] *)
    assert (Hdiv : exists t : nat, 6 * (A * m) = M_K * t).
    {
      (* Use the exponent condition alpha + 1 + 6 * p >= K *)
      assert (Hex : exists t, alpha + 1 + 6 * p = K + t).
      { exists (alpha + 1 + 6 * p - K). lia. }
      destruct Hex as [t Ht].

      unfold A.
      unfold M_K.
      (* Show: 6 * (2^(alpha+6p) * m) = 3 * 2^K * (2^t * m) *)
      (* Left-hand side: 6 * 2^(alpha+6p) * m
        = 3 * 2 * 2^(alpha+6p) * m
        = 3 * 2^(alpha+6p+1) * m
        = 3 * 2^(alpha+1+6p) * m
      *)
      exists (2 ^ t * m).
      (* Turn both sides into 3 * 2^(...) * m and use Ht *)
      assert (Hleft :
                6 * (2 ^ (alpha + 6 * p) * m)
              = 3 * 2 ^ (alpha + 1 + 6 * p) * m).
      {
        (* 6*(X*m) = (3*2)*(2^(alpha+6p)*m) = 3*2^(alpha+1+6p)*m *)
        rewrite <- Nat.mul_assoc.
        (* 6 = 3 * 2 *)
        (* 3 * 2 * (2^(...) * m) *)
        repeat rewrite Nat.mul_assoc.
        (* 3 * (2 * 2^(...)) * m = 3 * 2^(...+1) * m *)
        rewrite <- Nat.mul_assoc.
        assert (Hleft :
          6 * (2 ^ (alpha + 6 * p) * m)
        = 3 * 2 ^ (alpha + 1 + 6 * p) * m).
          {
            set (e := alpha + 6 * p).
            assert (He : alpha + 1 + 6 * p = e + 1) by (subst e; lia).
            rewrite He.
            change 6 with (3 * 2).

            (* LHS: 6 * (2^e * m) → 3*(2*(2^e*m)) *)
            rewrite Nat.mul_assoc.

            (* RHS: 3*2^(e+1)*m → 3*(2^e*2*m) *)
            replace (e + 1) with (S e) by lia.       
            rewrite (Nat.pow_succ_r' 2 e).   (* 2^(e+1) = 2^e * 2 *)
            repeat rewrite Nat.mul_assoc.
            reflexivity.            
          }
        exact Hleft.        
      }
      rewrite Hleft.
      (* Goal is now: 3 * 2 ^ (alpha + 1 + 6 * p) * m = 3 * 2 ^ K * (2 ^ t * m) *)

      rewrite Ht.
      (* 3 * 2 ^ (K + t) * m = 3 * 2 ^ K * (2 ^ t * m) *)

      rewrite Nat.pow_add_r.
      (* 3 * (2 ^ K * 2 ^ t) * m = 3 * 2 ^ K * (2 ^ t * m) *)

      (* Now just reassociate and commute multiplications *)
      repeat rewrite Nat.mul_assoc.
      reflexivity.      
    }

    destruct Hdiv as [q Hq].

    (* Now use mod arithmetic: (M_K * q) mod M_K = 0 *)
    assert (HMK_nz : M_K <> 0).
    {
      unfold M_K.
      intro H.
      apply Nat.mul_eq_0 in H as [H3 | Hpow].
      - discriminate H3.
      - (* 2^K = 0 impossible *)
        (* 2^K >= 1 always, so can't be 0 *)
        assert (Hpos : 2 ^ K >= 1).
        { apply pow_ge_1; lia. }
        lia.
    }

    rewrite Hq.
    (* We want to show:
        (M_K * q + delta + 6 * k) mod M_K
      = (delta + 6 * k) mod M_K
    *)

    (* 1. Regroup the sum so we clearly see (M_K * q) + (delta + 6*k) *)
    replace (M_K * q + delta + 6 * k)
      with (M_K * q + (delta + 6 * k))
      by lia.

    (* 2. Use the addition-mod lemma to pull mod inside *)
    rewrite Nat.Div0.add_mod by exact HMK_nz.
    (* Now LHS is:
      ((M_K * q) mod M_K + (delta + 6 * k) mod M_K) mod M_K
    *)

    (* 3. Kill (M_K * q) mod M_K using mod_mul *)
    replace (M_K * q) with (q * M_K) by lia.
    rewrite (Nat.Div0.mod_mul q M_K) by exact HMK_nz.
    (* becomes:
      (0 + (delta + 6 * k) mod M_K) mod M_K
    *)

    rewrite Nat.add_0_l.

    (* 4. Collapse nested mod (optional but nice) *)
    rewrite Nat.Div0.mod_mod by exact HMK_nz.

    reflexivity.    
  Qed.

  (* ------------------------------------------------------------------ *)
  (* Corollary 18.x : Refined last-step mapping across moduli           *)
  (*                       (cor:last-row-map)                           *)
  (* ------------------------------------------------------------------ *)  


  Lemma gcd_1_r (n : nat) : Nat.gcd n 1 = 1.
  Proof.
    (* Use gcd_unique with p := 1, m := 1 *)
    apply (Nat.gcd_unique n 1 1).
    - (* 1 | n *)
      unfold Nat.divide.
      exists n. lia.
    - (* 1 | 1 *)
      unfold Nat.divide.
      exists 1. lia.
    - (* maximality: any q dividing n and 1 also divides 1 *)
      intros q Hqn Hq1.
      exact Hq1.
  Qed.



  (**
    Corollary [Refined last-step mapping across moduli]
    (cor:last-row-map).

    In the paper, after fixing a starting modulus [M_K] and a target
    modulus [M_{K'}] with [K' >= K], and a last token

        x' = 6 * (2^{alpha+6p} * u + k^{(p)}) + delta,

    one refines the starting class so that the input router and [u]
    land in a class that satisfies the congruence, and hence
    map to the desired target residue class at level [M_{K'}].

    A core number-theoretic ingredient is simply:

      Given a target residue [r] and modulus [M_{K'}], as soon as
      [g_p | r], there exists [u] such that

           a_p * u ≡ r (mod M_{K'}).

    We state that here in a pure arithmetic form (with [K'] playing
    the role of the target exponent).
   *)
  
  Corollary cor_last_row_map (K' r : nat) :
    let g_p' := 3 * 2 ^ Nat.min (alpha + 1 + 6 * p) K' in
    let M_K' := 3 * 2 ^ K' in
    Nat.divide g_p' r ->
    exists u,
      (6 * 2 ^ (alpha + 6 * p) * u) mod M_K' = r mod M_K'.
  Proof.
    intros g_p' M_K' Hdiv.
    (* abbreviations *)
    set (e := alpha + 1 + 6 * p).
    set (ap := 6 * 2 ^ (alpha + 6 * p)).   (* same as a_p, but explicit *)
    assert (Hap_form : ap = 3 * 2 ^ e).
    {
      subst ap e.
      (* 6 * 2^(alpha+6p) = 3 * 2^(alpha+1+6p) *)
      change 6 with (3 * 2).
      (* 3*2*2^(alpha+6p) = 3*2^(alpha+1+6p) *)
      repeat rewrite Nat.mul_assoc.      
      (* 2 * 2^(alpha+6p) = 2^(alpha+1+6p) *)
      assert (H : 3 * 2 * 2 ^ (alpha + 3 * 2 * p)
                = 3 * 2 ^ (alpha + 1 + 3 * 2 * p)).
      {
        set (e := alpha + 3 * 2 * p).
        replace (alpha + 1 + 3 * 2 * p) with (S e) by (subst e; lia).
        rewrite (Nat.pow_succ_r' 2 e).        (* 2^(S e) = 2^e * 2 *)
        (* goal: 3 * 2 * 2^e = 3 * (2^e * 2) *)
        repeat rewrite Nat.mul_assoc.
        f_equal.        
      }
      exact H.
    }    
    (* M_K' is already 3 * 2^K' by definition *)
    assert (HMK'_nz : M_K' <> 0).
    {
      subst M_K'.
      intro H.
      apply Nat.mul_eq_0 in H as [H3 | Hpow]; [discriminate H3|].
      (* 2^K' = 0 impossible because 2^K' >= 1 *)
      assert (Hpos : 2 ^ K' >= 1).
      { apply pow_ge_1; lia. }
      lia.
    }
    (* Write the divisibility hypothesis as r = r0 * g_p' *)
    destruct Hdiv as [r0 Hr0].
    subst g_p'.
    (* Now we want: exists u, ap * u ≡ r [M_K'] *)
    (* Strategy: divide ap and M_K' by d := 3 * 2^(min e K'), prove coprime, use Bézout. *)
    set (d := 3 * 2 ^ Nat.min e K').
    (* Express ap and M_K' as a0 * d and n0 * d *)
    destruct (Nat.le_ge_cases e K') as [HeK | HKe].
    - (* e <= K' *)
      set (a0 := 1 : nat).
      set (n0 := 2 ^ (K' - e) : nat).
      (* prove ap = a0 * d, M_K' = n0 * d, gcd a0 n0 = 1, then Bezout, etc. *)
      assert (Hd_eq : d = 3 * 2 ^ e).
      {
        subst d.
        simpl.
        rewrite Nat.min_l by exact HeK.
        reflexivity.
      }
      assert (Ha0 : ap = a0 * d).
      {
        subst a0 d.
        rewrite Hap_form.
        rewrite Nat.min_l by exact HeK.  (* for d definition *)
        simpl.                           (* 1 * (3 * 2^e) = 3 * 2^e *)
        lia.        
      }
      assert (Hn0 : M_K' = n0 * d).
      {
        subst M_K' n0 d.
        (* M_K' = 3 * 2^K' ; d = 3 * 2^e ; n0 = 2^(K'-e) *)
        rewrite Nat.min_l by exact HeK.
        repeat rewrite Nat.mul_assoc.
        replace (2 ^ (K' - e) * 3 * 2 ^ e) with ((2 ^ (K' - e) * 2 ^ e) * 3)
          by (lia).
        rewrite <- (Nat.pow_add_r 2 (K' - e) e).
        replace (K' - e + e) with K' by lia.
        lia.        
      }
      assert (Hgcd1 : Nat.gcd a0 n0 = 1).
      {
        subst a0 n0.
        simpl.        
        reflexivity.
      }
      assert (Ha0_nz : a0 <> 0).
      {
        subst a0; discriminate.
      }
      assert (Hn0_nz : n0 <> 0).
      {
        subst n0.
        intro H.
        (* 2^(K'-e) >= 1, so cannot be 0 *)
        assert (Hpos : 2 ^ (K' - e) >= 1).
        { apply pow_ge_1; lia. }
        lia.
      }
      assert (Hbez_ex : exists u v, u * a0 = 1 + v * n0).
      {
        apply Nat_coprime_bezout; [exact Ha0_nz | exact Hn0_nz | exact Hgcd1].
      }
      destruct Hbez_ex as [u0 [v Hbez]].
      (* Hbez : u0 * a0 = 1 + v * n0 *)
      exists (u0 * r0).
      unfold M_K'.
      (* Unfold ap via Ha0, M_K' via Hn0, r via Hr0 *)
      rewrite Ha0.      
      rewrite Hr0.
      (* ap * (u0 * r0) = (a0*d)*(u0*r0) = (a0*u0)*(r0*d) *)
      repeat rewrite Nat.mul_assoc.
      replace (a0 * d * (u0 * r0)) with ((a0 * u0) * (r0 * d))
        by (lia).
      (* a0 * u0 = 1 + v * n0 *)
      assert (Hbez' : a0 * u0 = 1 + v * n0).
      { rewrite Nat.mul_comm in Hbez; exact Hbez. }
      replace (a0 * d * u0 * r0) with ((a0 * u0) * (r0 * d))
        by (lia).
      rewrite Hbez'.
      change (3 * 2 ^ K') with M_K'.
      rewrite Hn0.
      change (alpha + 1 + 6 * p) with e.
      assert (Hdmin : 3 * 2 ^ Nat.min e K' = d).
      {
        subst d.
        reflexivity.
      }
      replace (r0 * 3 * 2 ^ Nat.min e K') with (3 * 2 ^ Nat.min e K' * r0) by lia.
      replace (3 * 2 ^ Nat.min e K' * r0)
        with (d * r0)
        by (rewrite Hdmin; reflexivity).
      replace (d * r0) with (r0 * d)  by lia.
      (* LHS is now ((1 + v * n0) * (r0 * d)) mod (n0 * d) *)
      assert (Hnd : n0 * d <> 0).
      {
        intro H.
        apply HMK'_nz.
        rewrite Hn0.
        exact H.
      }
      (* Distribute (1 + v*n0) over (r0*d) *)
      rewrite Nat.mul_add_distr_r.      
      rewrite Nat.mul_1_l.
      (* Split the sum modulo *)
      rewrite Nat.Div0.add_mod by exact Hnd.
      (* Reshape (v*n0)*(r0*d) into something*(n0*d) *)
      replace ((v * n0) * (r0 * d))
        with ((v * r0) * (n0 * d))
        by (lia).
      (* Kill that term with mod_mul *)
      rewrite Nat.Div0.mod_mul by exact Hnd.
      rewrite Nat.add_0_r.
      (* Collapse nested mod on (r0*d) *)
      rewrite Nat.Div0.mod_mod by exact Hnd.
      (* RHS is (r0*d) mod (n0*d), which matches r mod M_K' after the rewrites *)
      reflexivity.
    - (* K' <= e *)
      set (a0 := 2 ^ (e - K') : nat).
      set (n0 := 1 : nat).
      (* same pattern in this branch *)
      assert (Hd_eq : d = 3 * 2 ^ K').
      {
        subst d.
        rewrite Nat.min_r by exact HKe.
        reflexivity.
      }
      assert (Hr0d : r = r0 * d).
      {
        subst d.
        subst e.
        (* Hr0 : r = r0 * (3 * 2 ^ Nat.min (alpha + 1 + 6 * p) K') *)
        (* but e = alpha + 1 + 6 * p *)
        subst r.
        reflexivity.        
      }
      assert (Hn0 : M_K' = n0 * d).
      {
        subst M_K' n0 d.
        (* M_K' = 3 * 2^K', d = 3 * 2^K' *)
        rewrite Nat.min_r by exact HKe.
        lia.        
      }
      assert (Ha0 : ap = a0 * d).
      {
        subst ap a0 d.
        rewrite Hap_form.
        rewrite Nat.min_r by exact HKe.
        (* Need: 3 * 2 ^ e = 2 ^ (e - K') * (3 * 2 ^ K') *)
        repeat rewrite Nat.mul_assoc.
        replace (2 ^ (e - K') * 3 * 2 ^ K') with ((2 ^ (e - K') * 2 ^ K') * 3)
          by (lia).
        rewrite <- Nat.pow_add_r.
        assert (He : e = (e - K') + K') by lia.
        rewrite <- He.
        lia.        
      }
      assert (Hgcd1 : Nat.gcd a0 n0 = 1).
      {
        subst a0 n0.
        simpl.         
        rewrite gcd_1_r.
        reflexivity.
      }
      assert (Hn0_nz : n0 <> 0).
      {
        subst n0; discriminate.
      }
      assert (Ha0_nz : a0 <> 0).
      {
        subst a0.
        intro H.
        assert (Hpos : 2 ^ (e - K') >= 1).
        { apply pow_ge_1; lia. }
        lia.
      }
      assert (Hbez_ex : exists u v, u * a0 = 1 + v * n0).
      {
        apply Nat_coprime_bezout; [exact Ha0_nz | exact Hn0_nz | exact Hgcd1].
      }
      destruct Hbez_ex as [u0 [v Hbez]].
      exists (u0 * r0).
      unfold M_K'.
      (* rewrite ap, M_K', r using factorisations *)
      rewrite Ha0.      
      rewrite Hr0d.
      (* ap * (u0 * r0) = (a0*d)*(u0*r0) = (a0*u0)*(r0*d) *)
      repeat rewrite Nat.mul_assoc.
      replace (a0 * d * (u0 * r0)) with ((a0 * u0) * (r0 * d))
        by (lia).
      (* a0 * u0 = 1 + v * n0 *)
      assert (Hbez' : a0 * u0 = 1 + v * n0).
      {
        (* Hbez : u0 * a0 = 1 + v * n0 *)
        rewrite Nat.mul_comm in Hbez.
        exact Hbez.
      }
      replace (a0 * d * u0 * r0) with ((a0 * u0) * (r0 * d)) by lia.
      rewrite Hbez'.
      (* LHS is now ((1 + v * n0) * (r0 * d)) mod (n0 * d) *)
      assert (Hnd : n0 * d <> 0).
      {
        intro H.
        apply HMK'_nz.
        rewrite Hn0.
        exact H.
      }
      rewrite Nat.mul_add_distr_r.         (* (1 + v*n0)*(r0*d) = 1*(r0*d) + (v*n0)*(r0*d) *)
      rewrite Nat.mul_1_l.
      rewrite Nat.Div0.add_mod by exact Hnd.      
      (* reshape (v*n0)*(r0*d) into something * (n0*d) *)
      repeat replace (v * r0 * (n0 * d))
        with ((v * r0) * (n0 * d))
        by (lia).
      (* 0. Give a name to the modulus *)
      set (M := 3 * 2 ^ K') in *.
      (* 1. Rewrite using n0=1 and d=... if you haven’t already *)
      subst n0.
      (* Now Hnd : 1 * d <> 0, so Hnd : d <> 0. And M = d in this branch. *)
      (* 2. Reshape the second term so we can use mod_mul *)
      replace (v * 1 * (r0 * d)) with ((v * r0) * d)
        by (lia).
      (* Goal is now:
        ((r0 * d) mod M + ((v * r0) * d) mod M) mod M = (r0 * d) mod M
      *)
      (* 3. Use mod_mul to kill ((v*r0)*d) mod M *)
      (* but first show M = d so Hnd matches the modulus *)
      assert (Hd_nz : d <> 0).
      {
        intro Hd0.
        apply Hnd.
        rewrite Hd0.      (* 1 * 0 <> 0 *)
        simpl.            (* 1 * 0 simplifies to 0 *)
        reflexivity.
      }
      assert (HMd : M = d).
      { subst M d e; rewrite Nat.min_r by exact HKe; reflexivity. }
      rewrite HMd in *.
      rewrite Nat.Div0.mod_mul by ( (* need d <> 0 *)
        (* Hnd is now d <> 0 after subst n0 *)
        exact Hd_nz
      ).
      (* Now LHS is: ((r0 * d) mod d + 0) mod d *)      
      rewrite Nat.add_0_l.
      (* 4. Now we DO have a nested mod: ((r0*d) mod d) mod d *)
      rewrite Nat.Div0.mod_mod by exact Hd_nz.      
      rewrite Nat.Div0.mod_mul by exact Hd_nz.
      reflexivity.
  Qed.

End LastRowCongruence.  

End Sec18_Residue_targeting_via_a_last_row_congruence.