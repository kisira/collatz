From Coq Require Import Arith.Arith Arith.PeanoNat Bool.Bool Lia.
From Coq Require Import Arith.PeanoNat Arith.Arith micromega.Lia.
Module Notation_indices_and_moves.


Definition tag (x : nat) : nat := (x - 1) / 2.

(* 1) If x is odd, then (3x+1) ≡ 4 (mod 6). *)

Lemma three_x_plus_one_mod6 :
  forall x, x mod 2 = 1 -> (3 * x + 1) mod 6 = 4.
Proof.
  intros x Hodd.
  (* Write x = 2*q + 1 (since x mod 2 = 1) *)
  set (q := x / 2).
  assert (Hdm : x = 2 * q + x mod 2).
  { unfold q. apply Nat.div_mod. lia. }
  rewrite Hodd in Hdm.                       (* so x = 2*q + 1 *)
  rewrite Hdm.
  (* Compute 3*(2*q+1)+1 = 6*q + 4 *)
  rewrite Nat.mul_add_distr_l, Nat.mul_1_r.
  rewrite Nat.mul_assoc.
  (* Reduce modulo 6: (6*q + 4) mod 6 = 4 *)
  rewrite Nat.add_comm.
  (* make 3*2 literally 6 *)
  change (3 * 2) with 6.
  (* massage 1 + (6*q + 3) → 6*q + 4 *)
  replace (1 + (6 * q + 3)) with (q * 6 + 4) by lia.
  (* put the multiple-of-6 first so mod_add applies directly *)
  rewrite Nat.add_comm.  
  (* (a + b*c) mod c = a mod c *)
  rewrite (Nat.Div0.mod_add 4 q 6) by lia.
  (* 4 < 6, so 4 mod 6 = 4 *)
  now rewrite Nat.mod_small by lia.
Qed.

Lemma mod_1_plus_3 :
  (1 mod 6) + ((3 mod 6) mod 6) mod 6 = 4.
Proof.
  (* Reduce inner mods using Nat.mod_small with explicit proofs *)
  rewrite (Nat.mod_small 3 6); [ | lia ].
  replace (1 mod 6 + (3 mod 6)) with (4 mod 6).
  - rewrite Nat.mod_small by lia.    (* 4 mod 6 = 4 *)
    rewrite Nat.mod_small.    (* 1 mod 6 = 1 *)
    rewrite (Nat.mod_small 3 6).
    lia.    (* (3 mod 6) = 3 *)    
    lia.
    rewrite Nat.mod_small by lia.
    lia.
  - rewrite Nat.mod_small by lia.    (* 1 mod 6 = 1 *)
    rewrite Nat.mod_small by lia.    (* (3 mod 6) = 3 *)
    replace (1 + 3) with 4 by lia.
    reflexivity.  
Qed.

Lemma crt_tag_mod6 :
  forall x, x mod 2 = 1 -> (3 * x + 1) mod 6 = 4.
Proof.
  intros x Hodd.
  (* Write x = 2*q + 1 using the division algorithm at modulus 2 *)
  set (q := x / 2).
  assert (Hdm : x = 2 * q + x mod 2) by (apply Nat.div_mod; lia).
  rewrite Hodd in Hdm.
  (* Compute 3*(2*q+1)+1 = 6*q+4 *)
  
  (* Expand 3 * (2 * q + 1) + 1 = 6 * q + 3 + 1 = 6 * q + 4 *)
  replace (3 * (2 * q + 1) + 1) with (6 * q + 4) by lia.
  (* Reduce (6*q + 4) mod 6 *)
  (* Split the sum modulo 6, then kill the multiple of 6 *)
  rewrite Nat.Div0.add_mod by lia.
  rewrite Hdm.
  change (3 * 2) with 6.
  (* massage 1 + (6*q + 3) → 6*q + 4 *)
  replace ((6 * q + 3) + 1) with (4 + q * 6) by lia.
  rewrite Nat.add_comm.
  rewrite Nat.mul_add_distr_l.                 (* 3*(2*q+1) = 3*(2*q) + 3 *)
  rewrite Nat.mul_comm with (n:=3) (m:=(2*q)) by lia.  
  pose proof (Nat.Div0.mod_mul (6 * q) 6) as Hmodmul.
  pose proof (mod_1_plus_3) as Hmod1plus3. 
  (* reassociate (2*q)*3 -> 2*(q*3) *)
  rewrite <- Nat.mul_assoc.
  (* commute q*3 -> 3*q, so we can fold 2*3=6 *)
  rewrite (Nat.mul_comm q 3).
  rewrite Nat.mul_assoc.                 (* 2 * (3 * q) = (2*3) * q *)
  change (2 * 3) with 6.
  (* also simplify 3*1 *)
  rewrite Nat.mul_1_r.
  (* split the inner mod by addition *)
  rewrite (Nat.Div0.add_mod (6 * q) 3 6) by lia.
  (* (6*q) mod 6 = 0; commute to (q*6) if needed *)
  rewrite Nat.mul_comm in *.
  rewrite (Nat.Div0.mod_mul q 6) by lia.
  (* clean up *)
  rewrite Nat.add_0_l.
  (* 3 < 6, so 3 mod 6 = 3 *)
  rewrite (Nat.mod_small 3 6) by lia.
  (* now we have (1 mod 6 + 3) mod 6 *)
  rewrite (Nat.mod_small 1 6) by lia.
  (* 1+3 < 6, so (1+3) mod 6 = 4 *)
  change ((1 + 3) mod 6 = 4).
  reflexivity.  
Qed.

(* 2) If x is odd, then with t = (x-1)/2 we have:
      (i)  x = 2*t + 1
      (ii) 3*x + 1 = 6*t + 4
   This shows t is an integer “tag”, and pinpoints the remainder 4 mod 6. *)
Lemma crt_tag_decompose :
  forall x, x mod 2 = 1 ->
    let t := (x - 1) / 2 in
      x = t * 2 + 1 /\ x * 3 + 1 = t * 6 + 4.
Proof.
  intros x Hodd t.
  (* Write x = 2*q + (x mod 2), then use x mod 2 = 1 *)
  set (q := x / 2).  
  assert (Hdm : x = 2 * q + x mod 2) by (apply Nat.div_mod; lia).
  rewrite Hodd in Hdm.                        (* now x = 2*q + 1 *)
  replace (2 * q + 1 - 1) with (2 * q) by lia.
  (* (2*q)/2 = q since 2 <> 0 *)
  replace ((q * 2) / 2) with q. 
  (* show (2*q + 1)/2 = q *)
  assert (H : (q * 2 + 1) / 2 = q).
  { rewrite Nat.div_add_l by lia. simpl. lia. }  
  (* Show t = q, since t = (x-1)/2 and x = 2*q+1 *)
  assert (Htq : t = q).
  { unfold t, q.
    rewrite Hdm.
    replace (q * 2 + 1 - 1) with (q * 2) by lia.
  (* (2*q)/2 = q since 2 <> 0 *)  
  (* show (2*q + 1)/2 = q *)
  assert (H2 : (q * 2 + 1) / 2 = q).
  { (* Use the division algorithm uniqueness: 2*q + 1 = 2*q + 1 with 0 <= 1 < 2 *)
    rewrite Nat.div_add_l by lia. simpl. lia.
    (* The side condition is just 0 <= 1 < 2, handled by lia. *)
  }
  (* simplify the left: (2*q + 1 - 1) = 2*q *)
  replace (2 * q + 1 - 1) with (q * 2) by lia.
  (* (2*q)/2 = q since 2 <> 0 *)
  replace ((q * 2) / 2) with q by (rewrite Nat.div_mul by lia; reflexivity).
  (* show (2*q + 1)/2 = q *)
  replace (2 * q + 1) with (q * 2 + 1) by lia.
  rewrite H2.
  reflexivity.  }
  rewrite Htq.
  rewrite Hdm.
  split.
  - lia.
  - replace (2 * q + 1) with (q * 2 + 1) by lia.
    lia.
  - symmetry.                    (* goal: (q*2)/2 = q *)
    now rewrite Nat.div_mul by discriminate.  (* 2 <> 0 *)
Qed.

(* 3) “Bijection” statements *)

(* Every odd x is of the form 2*t+1. *)
Lemma odd_has_tag :
  forall x, x mod 2 = 1 -> exists t, x = 2 * t + 1.
Proof.
  intros x Hodd.
  set (q := x / 2).
  assert (Hdm : x = 2 * q + x mod 2).
  { apply (Nat.div_mod x 2). lia. }
  rewrite Hodd in Hdm.  (* x = 2*q + 1 *)
  unfold tag.
  (* show (x - 1) / 2 = q *)
  assert (Htq : (x - 1) / 2 = q).
  { rewrite Hdm. replace (2 * q + 1 - 1) with (q * 2) by lia.    
    now rewrite Nat.div_mul by lia. }  
  exists q. exact Hdm.  
Qed.

(* And conversely 2*t+1 is odd. *)
Lemma two_t_plus_one_is_odd :
  forall t, (t * 2 + 1) mod 2 = 1.
Proof.
  intro t.
  rewrite Nat.add_comm.
  rewrite Nat.Div0.add_mod by lia.
  rewrite (Nat.Div0.mod_mul t) by lia.
  rewrite Nat.add_0_r.
  apply Nat.mod_small.
  lia.
Qed.

(* A single packaged statement mirroring the paper’s phrasing. *)
Lemma lem_crt_tag_nat :
  forall x : nat,
    Nat.odd x = true ->
    (3 * x + 1) mod 6 = 4.
Proof.
  intros x Hodd.
  (* Use the standard spec: odd x ↔ ∃k, x = 2k+1 *)
  destruct (proj1 (Nat.odd_spec x) Hodd) as [k Hx].  (* x = 2*k + 1 *)
  rewrite Hx.
  (* Compute 3*(2k+1)+1 = 6k+4 *)
  replace (3 * (2 * k + 1) + 1) with (4 + k * 6) by lia.
  (* Reduce modulo 6: (4 + 6*k) mod 6 = 4 mod 6 *)
  rewrite (Nat.Div0.mod_add 4 k 6) by lia.
  now rewrite Nat.mod_small by lia.
Qed.

(* Key helper: division by 2 of an odd "double+1" is the original q *)
Lemma div2_of_odd_double (q : nat) : (2*q + 1) / 2 = q.
Proof.
  (* Use the “unique quotient” characterization: if a = b*q + r with r<b, then a/b = q *)
  symmetry.
  apply (Nat.div_unique (2*q + 1) (2) (q) (1)).
  - lia.     (* 2*q + 1 = 2*q + 1 *)
  - lia.     (* remainder 1 < divisor 2 *)
Qed.

(* A second tiny helper we’ll use for 6q+4 mod 6 *)
Lemma mod_mul_self (m n : nat) : (n*m) mod m = 0.
Proof. rewrite Nat.Div0.mod_mul; lia. Qed.

(* A handy fact: (2*k) is divisible by 2, and 1 < 2. *)
Lemma mod2_of_odd_succ (k : nat) : (k*2 + 1) mod 2 = 1.
Proof.
  rewrite (Nat.Div0.add_mod (k*2) 1 2).
  - (* (2*k) mod 2 = 0 *)
    rewrite (Nat.Div0.mod_mul k 2) by lia.
    (* 1 mod 2 = 1 and (0 + 1) mod 2 = 1 *)
    rewrite Nat.mod_small.
    now rewrite Nat.add_0_l, Nat.mod_small by lia.
    rewrite Nat.add_0_l, Nat.mod_small by lia.
    lia.  
Qed.

Lemma div_odd_succ_eq (k : nat) : (k * 2 + 1) / 2 = k.
Proof.
  (* Division algorithm at modulus 2 *)
  pose proof (Nat.div_mod (k*2 + 1) 2) as Hdm.
  specialize (Hdm ltac:(lia)).
  (* 2*k + 1 = 2 * ((2*k+1)/2) + ((2*k+1) mod 2) *)
  rewrite (mod2_of_odd_succ k) in Hdm.
  (* Now both sides are ... + 1; cancel and compare the even parts *)
  replace (k * 2 + 1) with (k * 2 + 1) in Hdm by reflexivity.
  assert (2 * ((k * 2 + 1) / 2) = k * 2) by lia.
  now apply (Nat.mul_cancel_l _ _ 2); lia.
Qed.

(* Helper: (2*k + 1) is 1 mod 2 *)
Lemma mod2_of_two_k_plus_one k : (k * 2 + 1) mod 2 = 1.
Proof.
  (* (2*k + 1) mod 2 = ((2*k) mod 2 + 1 mod 2) mod 2 *)
  rewrite (Nat.Div0.add_mod (k*2) 1 2) by lia.
  (* (2*k) mod 2 = 0 *)
  rewrite (Nat.Div0.mod_mul k 2) by lia.
  simpl. reflexivity.   
Qed.

Lemma odd_mod2_is_1 (x : nat) :
  Nat.odd x = true -> x mod 2 = 1.
Proof.
  intro Hodd.
  (* Turn the boolean fact into a propositional oddness witness: x = 2*q + 1 *)
  apply Nat.odd_spec in Hodd.
  destruct Hodd as [q Hx].                (* Hx : x = 2*q + 1 *)
  subst x.
  replace (2 * q + 1) with (q * 2 + 1) by lia.
  (* Compute (2*q + 1) mod 2 *)
  rewrite (Nat.Div0.add_mod (q*2) 1 2) by lia.
  rewrite (Nat.Div0.mod_mul q 2) by lia.  (* (2*q) mod 2 = 0 *)
  rewrite Nat.mod_small.           (* 1 mod 2 = 1 *)
  - reflexivity.
  - simpl. lia.
Qed.

Lemma crt_tag_nat_forward_mod2 :
  forall x,
    x mod 2 = 1 ->
    let t := x / 2 in
      (3 * x + 1) mod 6 = 4
    /\ x = 2 * t + 1
    /\ 3 * x + 1 = 6 * t + 4.
Proof.
  intros x Hodd t.
  (* Division algorithm at 2: x = 2*q + (x mod 2) with q = x/2 *)
  set (q := x / 2).
  assert (Hdm : x = 2 * q + x mod 2) by (apply (Nat.div_mod x 2); lia).
  (* Using x mod 2 = 1 *)
  rewrite Hodd in Hdm.
  (* Since t := x/2, we have t = q by definition *)
  assert (Htq : t = q) by (subst t; reflexivity).
  subst t.

  (* 1) Mod-6 residue of 3x+1 *)
  assert (H1 : (3 * x + 1) mod 6 = 4).
  { rewrite Hdm.
    (* 3*(2*q+1)+1 = 6*q + 4 *)
    replace (3 * (2 * q + 1) + 1) with (6 * q + 4) by lia.
    (* reduce (6*q + 4) mod 6 *)
    rewrite (Nat.Div0.add_mod (6 * q) 4 6) by lia.
    (* (6*q) mod 6 = 0 *)
    rewrite Nat.mul_comm.
    rewrite (Nat.Div0.mod_mul q 6) by lia.
    simpl.
    reflexivity.
     }
  split; [exact H1|].
  (* 2) x = 2*q + 1 *)
  split.
  - exact Hdm.
  (* 3) 3x+1 = 6*q + 4 *)
  - rewrite Hdm.
    replace (3 * (2 * q + 1) + 1) with (6 * q + 4) by lia.
    replace (2 * q + 1) with (q * 2 + 1) by lia.
    pose proof (div_odd_succ_eq q) as Hdiv.
    rewrite Hdiv.
    reflexivity.
Qed.

Lemma crt_tag_nat_forward :
  forall x,
    Nat.odd x = true ->
    let t := x / 2 in
      (3 * x + 1) mod 6 = 4
    /\ x = 2 * t + 1
    /\ 3 * x + 1 = 6 * t + 4.
Proof.
  intros x Hodd t.
  apply crt_tag_nat_forward_mod2.
  (* turn odd into x mod 2 = 1 *)
  (* Goal: x mod 2 = 1, with Hodd : Nat.odd x = true in context *)
  destruct (Nat.odd_spec x) as [Heven].
  - (* x is odd: x = 2*k+1 *)
    destruct Heven as [k Hx].
    assumption. 
    rewrite Hx.
    replace (2 * k + 1) with (k * 2 + 1) by lia.
    pose proof (mod2_of_two_k_plus_one k) as Hodd'.
    exact Hodd'.    
Qed.

(* Helper: if x ≡ 1 (mod 2) then x is odd *)
Lemma odd_of_mod2_1 (x : nat) :
  x mod 2 = 1 -> Nat.odd x = true.
Proof.
  (* We use the standard boolean characterization: odd x is true <-> exists k, x = 2k+1 *)
  (* Coq’s library provides Nat.odd_spec in the forward direction; for the reverse,
     build the witness from the division algorithm at modulus 2. *)
  intro Hmod.
  (* Division algorithm at modulus 2: x = 2*q + r, r = x mod 2 *)
  pose (q := x / 2).
  assert (Hx : x = 2*q + x mod 2) by (apply (Nat.div_mod x 2); lia).
  rewrite Hmod in Hx. (* now x = 2*q + 1 *)
  (* odd_spec: if x = 2*k+1, then Nat.odd x = true *)
  (* There is a lemma [Nat.odd_spec] that gives the forward direction, but to avoid
     depending on it, we can compute odd on the concrete “2*q+1”: *)
  (* Compute odd (2*q+1) via [Nat.odd_succ] and the fact odd(2*q)=false *)
  (* However, we can also finish by evaluating mod-2 definitionally: *)
  (* Use boolean equality: odd x = negb (even x), and even x iff x mod 2 = 0.
     Since x mod 2 = 1, odd x must be true. *)
  (* These are the standard facts: *)
  rewrite <- (Nat.negb_even x).                 (* odd x = negb (even x) *)
  (* even x = true <-> x mod 2 = 0, so even x must be false *)
  apply negb_true_iff.
  (* Show even x = false by showing x mod 2 ≠ 0 *)
  destruct (Nat.even x) eqn:Hev; [|reflexivity].
  apply Nat.even_spec in Hev.
  destruct Hev as [k Heq].
  (* If x = 2*k then x mod 2 = 0, contradicting x mod 2 = 1 *)
  rewrite Heq in Hmod.
  lia.  
Qed.

Lemma mod_sum_lt_2 : forall t, 1 mod 2 + (t * 2) mod 2 < 2.
Proof.
  intro t.
  (* 1 mod 2 = 1 *)
  assert (H1 : 1 mod 2 = 1) by (compute; reflexivity).
  rewrite H1.
  (* (2*t) mod 2 = 0 because 2 divides 2*t *)
  rewrite (Nat.Div0.mod_mul t 2) by lia.
  (* goal is 1 + 0 < 2 *)
  lia.
Qed.


(* Your lemma: purely in nat, no ssreflect *)
Lemma crt_tag_nat_backward :
  forall t, Nat.odd (2 * t + 1) = true.
Proof.
  intro t.
  (* Show (2*t+1) ≡ 1 (mod 2) *)
  assert (Hmod : (2 * t + 1) mod 2 = 1).
  { (* (2*t+1) mod 2 = (1 + 2*t) mod 2 = (1 mod 2 + (2*t) mod 2) mod 2 = (1 + 0) mod 2 = 1 *)
    rewrite Nat.add_comm.
    rewrite (Nat.Div0.add_mod 1 (2*t) 2) by lia.
    rewrite Nat.mod_small.                 (* 1 mod 2 = 1 *)
    rewrite Nat.mul_comm.                         (* make it (t*2) to use mod_mul *)
    rewrite (Nat.Div0.mod_mul t 2) by lia.        (* (t*2) mod 2 = 0 *)
    replace (1 mod 2 + 0) with (0 + 1 mod 2) by lia.
    rewrite Nat.add_0_l.    
    now rewrite Nat.mod_small by lia.
    replace (2 * t) with (t * 2) by lia.
    apply (mod_sum_lt_2 t).    
  }
  (* Convert remainder-1 to odd=true *)
  now apply odd_of_mod2_1.
Qed.

Lemma tag_goal (x : nat) :
  2 * (x / 2) + 1 = 2 * ((2 * (x / 2) + 1) / 2) + 1.
Proof.
  set (q := x / 2).
  replace (2 * q) with (q * 2) by lia.
  rewrite (div_odd_succ_eq q).  (* ((2q+1)/2) = q *)
  replace (2 * q) with (q * 2) by lia.
  reflexivity.
Qed.

(* For any q, (2q+1)/2 = q *)
Lemma div2_of_odd : forall q : nat, (2*q + 1) / 2 = q.
Proof.
  intro q.
  (* Use the “division uniqueness” lemma: if a = b*q + r with r<b, then a/b = q *)  
  symmetry.
  eapply Nat.div_unique with (b:=2) (q:=q) (r:=1).
  - lia.                                 (* r = 1 < 2 *)
  - reflexivity.                          (* 2*q + 1 = 2*q + 1 *)
Qed.

Lemma tag_is_div2 :
  forall x, Nat.odd x = true -> x = 2 * (x / 2) + 1.
Proof.
  intros x Hodd.
  (* Division algorithm at modulus 2 *)
  rewrite (Nat.div_mod x 2) by lia.
  (* Replace the remainder by 1 since x is odd *)
  rewrite (odd_mod2_is_1 x Hodd).  
  replace ((2 * (x / 2) + 1) / 2) with (x / 2) by (symmetry; apply div2_of_odd).
  (* Now x = 2*(x/2) + 1 *)  
  reflexivity.
Qed.


(* corollary [Family and indices from the tag] (label: cor:tag-indices) *)
(* ---------- Part 1: family from tag:  x mod 6 = 2*(t mod 3) + 1 ---------- *)

Lemma cor_tag_family_nat :
  forall x, x mod 2 = 1 ->
    let t := (x - 1) / 2 in
      x mod 6 = 2 * (t mod 3) + 1.
Proof.
  intros x Hodd t.  
  pose proof (crt_tag_decompose x Hodd) as H.
  cbv zeta in H.                 (* removes the inner “let t := …” *)
  destruct H as [Hx Hlin].       (* now you have x = 2*t+1 and 3*x+1 = 6*t+4 *)
  rewrite Hx.
  (* write t = 3*q + r with r = t mod 3, r < 3 *)
  set (q := t / 3).
  set (r := t mod 3).
  assert (Ht : t = 3 * q + r).
  { unfold q, r. apply (Nat.div_mod t 3). lia. }
  (* 1) Turn (x-1)/2 into t using Hx *)
  assert (Ht_div : (x - 1) / 2 = t).
  { rewrite Hx.    
    replace ((x - 1) / 2 * 2 + 1 - 1) with (x - 1) by lia.
    reflexivity.
  }
  (* Use it in the goal *)
  rewrite Ht_div.

  (* 2) Now the goal is ((2*t + 1) mod 6 = 2*r + 1).  Decompose t = 3*q + r *)
  symmetry in Ht.
  replace t with (3*q + r) by exact Ht.
  replace ((3*q + r) * 2 + 1) with (q * 6 + (2*r + 1)) by lia.

  (* 3) Kill the 6*q part mod 6, then reduce the small remainder *)
  rewrite Nat.add_comm.
  (* Goal: (2 * r + 1 + 6 * q) mod 6 = 2 * r + 1 *)

  (* 1) Use add_mod to split the sum *)
  rewrite (Nat.Div0.add_mod (2 * r + 1) (q * 6) 6) by lia.
  (* LHS is now: ((2*r+1) mod 6 + (6*q) mod 6) mod 6 *)

  (* 2) Kill the multiple of 6 *)
  rewrite Nat.mul_comm.                       (* make it q*6 if needed *)
  rewrite (Nat.Div0.mod_mul q 6) by lia.      (* (q*6) mod 6 = 0 *)

  (* 3) Clean the sum *)
  rewrite Nat.add_0_r.                        (* ((2*r+1) mod 6 + 0) mod 6 = (2*r+1) mod 6 *)

  (* 4) Finish by bounding 2*r+1 < 6 so the mod disappears *)
  assert (Hrlt : 2 * r + 1 < 6).
  { (* since r = t mod 3, we have r < 3, hence 2*r+1 <= 5 *)
    pose proof (Nat.mod_upper_bound t 3 ltac:(lia)) as Hr.
    (* Hr : r < 3 *)
    lia.
  }
  replace (2 * r + 1) with (r * 2 + 1) in Hrlt by lia. 
   (* First show the smallness bound 2*r+1 < 6 *)
  assert (Hsmall : r * 2 + 1 < 6) by lia.
  (* Reduce the inner mod using the bound *)
  rewrite Nat.mod_small.
  (* Reduce the outer mod using the same bound *)
  rewrite Nat.mod_small by exact Hsmall.
  reflexivity.
  (* a mod b < b when b > 0 *)
  apply Nat.mod_upper_bound.
  lia.  (* 0 < 6 *)  
Qed.

(* ---------- Part 2: m-index equality:  x/18 = t/9 ---------- *)

Lemma div_double_succ (a : nat) : (2 * a + 1) / 2 = a.
Proof.
  (* Use the uniqueness characterization of division *)
  symmetry.
  eapply (Nat.div_unique (2 * a + 1) (2) (a) (1)).
  - lia.                         (* 1 < 2 *)
  - reflexivity.                  (* 2*a+1 = 2*a + 1 *)
Qed.

Lemma cor_tag_m_index_nat :
  forall x, x mod 2 = 1 ->
    let t := (x - 1) / 2 in
      x / 18 = t / 9.
Proof.
  intros x Hodd t.

  (* 1) Decompose x at modulus 2; since x mod 2 = 1 we get x = 2*(x/2)+1. *)
  assert (Hx_decomp : x = 2 * (x / 2) + 1).
  { rewrite (Nat.div_mod x 2) at 1 by lia.
    rewrite Hodd. lia. }

  (* 2) Show t = x/2 from the definition t := (x-1)/2. *)
  assert (Ht_eq_q2 : t = x / 2).
  { unfold t. rewrite Hx_decomp.
    (* (2*(x/2)+1 - 1)/2 = (2*(x/2))/2 = x/2 *)
    replace (2 * (x / 2) + 1 - 1) with ((x / 2) * 2) by lia.
    rewrite Nat.div_mul; [|lia]. 
    set (q := x / 2).
    (* Goal becomes q = (2*q + 1) / 2 *)
    change (q = (2 * q + 1) / 2).
    (* Show (2*q + 1) / 2 = q via the division algorithm with remainder 1 *)    
    apply (Nat.div_unique (2 * q + 1) (2) (q) (1)).
    - lia.            (* 1 < 2 *)
    - reflexivity.    (* a = b*q + r *)
  }

  (* 3) Work with q := t/9 and r := t mod 9 (0 <= r < 9). *)
  set (q := t / 9).
  set (r := t mod 9).
  assert (Ht_decomp : t = 9 * q + r).
  { unfold q, r. apply Nat.div_mod. lia. }

  (* 4) Rewrite x in terms of q and r: x = 2t+1 = 18q + (2r+1). *)
  assert (Hx_qr : x = 18 * q + (2 * r + 1)).
  { rewrite Hx_decomp.
    (* x = 2*(x/2)+1 *)
    rewrite Hx_decomp.
    (* replace x/2 by t *)
    rewrite <- Ht_eq_q2.
    (* t = 9*q + r *)
    rewrite Ht_decomp.
    (* 2*(9*q + r) + 1 = 18*q + (2*r + 1) *)
    assert (Hdiv : (2 * (9 * q + r) + 1) / 2 = 9 * q + r).
    { rewrite div_double_succ. reflexivity. }

    rewrite Hdiv.
    (* The goal is now purely algebraic *)
    lia.    
  }

  (* from earlier: Ht_decomp : t = 9*q + r, and t := (x-1)/2 *)
  assert (Hx_eq : x = 2*t + 1) by (rewrite Ht_eq_q2; exact Hx_decomp).

  (* remainder bound: 2*r+1 < 18 since r < 9 *)
  assert (Hr_lt9 : r < 9).
  { unfold r; apply Nat.mod_upper_bound; lia. }
  assert (Hs_lt18 : 2*r + 1 < 18) by lia.

  (* conclude the quotient *)
  replace (x / 18) with q.
  - reflexivity.
  - apply (Nat.div_unique (x) (18) (q) (2*r+1));
      [ exact Hs_lt18 | exact Hx_qr ].  
Qed.

(* ---------- Part 3: j-index modulo 3, excluding the r=1 case ---------- *)
(* Assumption: t mod 3 ∈ {0,2} (i.e. NOT 1), then floor(x/6) = floor(t/3),
   so their residues mod 3 coincide. *)

Lemma odd_div_decompose :
  forall x, Nat.odd x = true -> x = 2 * (x / 2) + 1.
Proof.
  intros x Hodd.
  (* Step 1: from Nat.odd x = true, get x = 2*k + 1 *)
  apply Nat.odd_spec in Hodd.
  destruct Hodd as [k Hk].                 (* Hk : x = 2*k + 1 *)

  (* Step 2: show x mod 2 = 1 *)
  assert (Hmod2 : x mod 2 = 1).
  { rewrite Hk.
    (* (2*k + 1) mod 2 = ((2*k) mod 2 + 1 mod 2) mod 2 *)
    rewrite (Nat.Div0.add_mod (2*k) 1 2) by lia.
    (* (2*k) mod 2 = 0 *)
    replace (2 * k) with (k * 2) by lia.
    rewrite (Nat.Div0.mod_mul k 2) by lia.
    (* 1 mod 2 = 1, and then reduce the outer mod 2 *)
    rewrite Nat.mod_small.
    rewrite Nat.add_0_l. reflexivity.
    rewrite Nat.add_0_l. 
    rewrite Nat.mod_small by lia.
    lia.
  }
  (* Step 3: use the division algorithm at modulus 2 *)
  (* x = 2*(x/2) + x mod 2, and x mod 2 = 1 *)
  rewrite (Nat.div_mod x 2) by lia.
  rewrite Hmod2.
  set (q := x / 2).
  (* Show (2*q+1)/2 = q by division uniqueness: remainder 1 < 2 *)
  assert (H : (2 * q + 1) / 2 = q).
  { symmetry. apply (Nat.div_unique (2 * q + 1) 2 q 1); lia. }
  (* Reassemble *)
  symmetry.
  now rewrite H.
Qed.

Lemma odd_div_decompose' (x:nat) :
  x mod 2 = 1 -> x = 2 * (x / 2) + 1.
Proof.
  intro Hodd.
  pose proof (Nat.div_mod x 2) as Hdm.
  specialize (Hdm ltac:(lia)).
  now rewrite Hodd in Hdm.
Qed.

Lemma div_half_of_odd (x:nat) :
  x mod 2 = 1 -> (x - 1) / 2 = x / 2.
Proof.
  intro Hmod.
  (* Use Euclidean division: x = 2*(x/2) + (x mod 2) *)
  pose proof (Nat.div_mod x 2) as Hdecomp; try lia.
  rewrite Hmod in Hdecomp.  (* now: x = 2*(x/2) + 1 *)
  assert (Hsub : x - 1 = 2 * (x / 2)) by lia.
  rewrite Hsub.
  rewrite Nat.mul_comm.  
  apply Nat.div_mul; lia.  (* 2 <> 0 *)
Qed.

Lemma cor_tag_j_index_nat :
  forall x, x mod 2 = 1 ->
    let t := (x - 1) / 2 in
    (t mod 3 = 0 \/ t mod 3 = 2) ->
    (x / 6) mod 3 = (t / 3) mod 3.
Proof.
  intros x Hodd t Htmod.
  (* Relate t and x/2 *)
  assert (Ht_eq : t = x / 2) by (unfold t; now apply div_half_of_odd).
  (* Write t = 3*q + r with r = t mod 3 *)
  set (q := t / 3).
  set (r := t mod 3).
  assert (Ht_div : t = 3*q + r) by (subst q r; apply Nat.div_mod; lia).
  assert (Hr_cases : r = 0 \/ r = 2) by (subst r; exact Htmod).

  (* Use x mod 2 = 1 to get x = 2*t + 1, then substitute t = 3*q + r *)
  pose proof (Nat.div_mod x 2) as Hx2; try lia.
  rewrite Hodd in Hx2.                 (* x = 2*(x/2) + 1 *)
  rewrite <- Ht_eq in Hx2.             (* x = 2*t + 1 *)
  rewrite Ht_div in Hx2.               (* x = 2*(3*q + r) + 1 = 6*q + (2*r + 1) *)

  (* Split the two cases r = 0 or r = 2 *)
  destruct Hr_cases as [Hr0 | Hr2].
  - (* Case r = 0: x = 6*q + 1 *)
    assert (Hx : x = 6*q + 1) by (rewrite Hx2, Hr0; lia).
    (* Compute x/6 using Euclidean division uniqueness *)
    (* First, (6*q + 1) mod 6 = 1 *)
    assert (Hmod6 : (6*q + 1) mod 6 = 1).
    { rewrite Nat.Div0.add_mod by lia.
      rewrite Nat.Div0.mul_mod by lia.
      rewrite Nat.Div0.mod_same by lia.
      rewrite Nat.add_0_l. reflexivity.
    }
    (* Now 6 * ((6*q + 1)/6) + 1 = 6*q + 1 ⇒ (6*q + 1)/6 = q *)
    pose proof (Nat.div_mod (6*q + 1) 6) as Hdiv6; try lia.
    rewrite Hmod6 in Hdiv6.
    replace (6*q + 1) with x in Hdiv6 by exact Hx.
    replace (6*q + 1) with x in Hmod6 by exact Hx.
    assert (x / 6 = q).
    { (* 6*(x/6) + 1 = 6*q + 1 ⇒ 6*(x/6) = 6*q ⇒ x/6 = q *)
      lia. }
    (* Also, t/3 = q by definition of q *)
    assert (t / 3 = q) by (subst q; reflexivity).
    now rewrite H. 

  - (* Case r = 2: x = 6*q + 5 *)
    assert (Hx : x = 6*q + 5) by (rewrite Hx2, Hr2; lia).
    (* (6*q + 5) mod 6 = 5 *)
    assert (Hmod6 : (6*q + 5) mod 6 = 5).
    { rewrite Nat.Div0.add_mod by lia.
      rewrite Nat.Div0.mul_mod by lia.
      rewrite Nat.Div0.mod_same by lia.
      rewrite Nat.add_0_l. reflexivity.
    }
    (* 6 * ((6*q + 5)/6) + 5 = 6*q + 5 ⇒ (6*q + 5)/6 = q *)
    pose proof (Nat.div_mod (6*q + 5) 6) as Hdiv6; try lia.
    rewrite Hmod6 in Hdiv6.
    replace (6*q + 5) with x in Hdiv6 by exact Hx.
    replace (6*q + 5) with x in Hmod6 by exact Hx.
    assert (x / 6 = q) by lia.
    assert (t / 3 = q) by (subst q; reflexivity).
    now rewrite H.
Qed.

(* Final packaged corollary mirroring paper’s phrasing. *)

Corollary cor_tag_indices_plain :
  forall x, x mod 2 = 1 ->
    let t := (x - 1) / 2 in
      x mod 6 = 2 * (t mod 3) + 1
   /\ (x / 18) = t / 9
   /\ ((x / 6) mod 3) = (t / 3) mod 3.
Proof.
  intros x Hodd t.
  (* x = 2*t + 1 *)
  assert (Ht_eq : t = x / 2) by (unfold t; now apply div_half_of_odd).
  pose proof (Nat.div_mod x 2) as Hx2; try lia.
  rewrite Hodd in Hx2.            (* x = 2*(x/2) + 1 *)
  rewrite <- Ht_eq in Hx2.        (* x = 2*t + 1 *)

  (* t = 3*q + r, r = t mod 3, r<3 *)
  set (q := t / 3).
  set (r := t mod 3).
  assert (Ht_div : t = 3*q + r) by (subst q r; apply Nat.div_mod; lia).
  assert (Hr_lt  : r < 3)        by (subst r; apply Nat.mod_upper_bound; lia).

  (* 1) x mod 6 = 2*(t mod 3) + 1 *)
  assert (Hx_repr1 : x = 6*q + (2*r + 1)).
  { rewrite Hx2, Ht_div; lia. }
  assert (H1 : x mod 6 = 2*r + 1).
  { rewrite Hx_repr1.
    rewrite Nat.Div0.add_mod by lia.
    rewrite Nat.Div0.mul_mod by lia.
    rewrite Nat.Div0.mod_same by lia.
    rewrite Nat.add_0_l.
    rewrite Nat.Div0.mod_mod by lia.        (* now goal: (2*r+1) mod 6 = 2*r+1 *)
    apply Nat.mod_small; lia. }
  assert (Hx_mod6 : x mod 6 = 2 * (t mod 3) + 1) by (subst r; exact H1).

  (* 2) x / 18 = t / 9 *)
  set (u := t / 9).
  set (v := t mod 9).
  assert (Ht_div9 : t = 9*u + v) by (subst u v; apply Nat.div_mod; lia).
  assert (Hv_lt   : v < 9)       by (subst v; apply Nat.mod_upper_bound; lia).
  assert (Hx_repr2 : x = 18*u + (2*v + 1)).
  { rewrite Hx2, Ht_div9; lia. }
  assert (Hmod18 : x mod 18 = 2*v + 1).
  { rewrite Hx_repr2.
    rewrite Nat.Div0.add_mod by lia.
    rewrite Nat.Div0.mul_mod by lia.
    rewrite Nat.Div0.mod_same by lia.
    rewrite Nat.add_0_l.
    rewrite Nat.Div0.mod_mod by lia.
    apply Nat.mod_small; lia. }
  pose proof (Nat.div_mod x 18) as Hdiv18; try lia.
  rewrite Hmod18, Hx_repr2 in Hdiv18.
  assert (Hx18 : x / 18 = u).
  { rewrite Hx_repr2.
    replace (18 * u + (2 * v + 1)) with ( u * 18 + (2 * v + 1)) by lia.
    rewrite (Nat.div_add_l  (u) 18 (2*v+1)) by lia.    
    rewrite Nat.div_small; [lia|].   (* (2*v+1)/18 = 0 since < 18 *)
    lia. }
  assert (Ht9  : t / 9  = u) by (subst u; reflexivity).
  assert (H2   : x / 18 = t / 9) by (rewrite Hx18, Ht9; reflexivity).

  (* 3) ((x/6) mod 3) = ((t/3) mod 3) *)
  pose proof (Nat.div_mod x 6) as Hdiv6; try lia.
  rewrite Hx_repr1 in Hdiv6.
  assert (Hmod6_again : x mod 6 = 2*r + 1).
  { exact H1. }
  (* 1) Specialize away the premise *)
  specialize (Hdiv6 ltac:(lia)).
  (* Hdiv6 :
    6*q + (2*r + 1)
  = 6 * ((6*q + (2*r + 1)) / 6) + (6*q + (2*r + 1)) mod 6 *)

  (* 2) Compute the expanded remainder *)
  assert (Hrem :
    (6*q + (2*r + 1)) mod 6 = 2*r + 1).
  { rewrite Nat.Div0.add_mod by lia.
    rewrite Nat.Div0.mul_mod by lia.
    rewrite Nat.Div0.mod_same by lia.
    rewrite Nat.add_0_l.
    (* we need 2*r+1 < 6; you should already have r<3 *)
    assert (Hlt : 2*r + 1 < 6) by lia.
    rewrite Nat.Div0.mod_mod by lia.
    now apply Nat.mod_small. }

  rewrite Hrem in Hdiv6.
  (* Now Hdiv6 is:
    6*q + (2*r + 1) = 6 * ((6*q + (2*r + 1)) / 6) + (2*r + 1) *)

  (* 3) Cancel the common (2*r+1) and conclude the quotient *)
  assert (Hq' : ((6*q + (2*r + 1)) / 6) = q) by lia.

  (* If you want x/6 = q, use your x-representation x = 6*q + (2*r+1) *)
  rewrite <- Hx_repr1 in Hq'.  (* Hx_repr1 : x = 6*q + (2*r+1) *)
  (* So: x/6 = q *)

  assert (Hx6 : x / 6 = q) by lia.
  assert (Ht3 : t / 3 = q) by (subst q; reflexivity).
  assert (H3 : (x / 6) mod 3 = (t / 3) mod 3) by (rewrite Hx6, Ht3; reflexivity).

  (* Bundle results *)
  repeat split; assumption.
Qed.

End Notation_indices_and_moves.
