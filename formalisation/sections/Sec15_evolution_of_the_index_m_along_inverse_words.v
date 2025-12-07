From Coq Require Import Arith.Arith Arith.PeanoNat Lia.
From Coq Require Import Classes.RelationClasses.
From Coq Require Import Lists.List.
Import ListNotations.

Module Sec15_Evolution_of_the_index_m_along_inverse_words.

  Require Import Arith Lia.

(* Paper tie-in (Sec. 15): Each inverse letter (r,p) acts affinely on m:
   m ↦ 2^{alpha(r)+6p} * m + krow(r). Composing the same letter k times
   yields a closed form with a geometric sum of the scale 2^{alpha+6p}. *)

(* Row interface (as in earlier sections) *)
Record Row := {
  alpha : nat;
  krow  : nat;
}.

Definition pow2 (e:nat) := Nat.pow 2 e.

(* Single inverse-letter update on m *)
Definition inv_letter_update (r:Row) (p:nat) (m:nat) : nat :=
  pow2 (alpha r + 6*p) * m + krow r.

(* The accumulated scale for k repeats: 2^{(alpha+6p) * k} *)
Definition pow2A (r:Row) (p k:nat) : nat :=
  pow2 ((alpha r + 6*p) * k).

(* Geometric sum ∑_{t=0}^{k-1} 2^{(alpha+6p)*t}.
   We encode it inductively to match the algebra in the proof. *)
Fixpoint geom_sum (a k:nat) : nat :=
  match k with
  | 0   => 0
  | S t => pow2 (a*t) + geom_sum a t
  end.

  (* Recall: pow2 e := 2 ^ e *)
Lemma geom_sum_step_eq : forall a k,
  pow2 a * geom_sum a k + 1 = pow2 (a*k) + geom_sum a k.
Proof.
  intros a k; induction k as [|k IH]; simpl.
  - (* k = 0 *)
    rewrite Nat.mul_0_r. replace (a*0) with 0 by lia.
    unfold pow2. rewrite Nat.pow_0_r. now rewrite Nat.add_0_r.
  - (* k = S k *)
    (* goal: pow2 a * (pow2 (a*k) + geom_sum a k) + 1
              = pow2 (a * S k) + (pow2 (a*k) + geom_sum a k) *)
    rewrite Nat.mul_add_distr_l.        (* distribute pow2 a *)
    (* x + y + 1 -> x + (y + 1), to expose (pow2 a * geom_sum a k + 1) *)
    rewrite <- Nat.add_assoc.
    (* now rewrite the parenthesized piece using IH *)
    rewrite IH.                         (* … + (pow2 (a*k) + geom_sum a k) *)
    (* turn pow2 a * pow2 (a*k) into pow2 (a*(S k)) *)
    replace (pow2 a * pow2 (a*k))
      with (pow2 (a + a*k))
      by (unfold pow2; rewrite <- Nat.pow_add_r; reflexivity).
    (* a + a*k = a*(S k) *)
    rewrite Nat.mul_succ_r.             (* a*(S k) = a*k + a *)
    replace (a + a*k) with (a*k + a) by lia.
    reflexivity.    
Qed.

Lemma nat_rect_f_fusion (f : nat -> nat) (x : nat) :
  forall n,
    f (nat_rect (fun _ : nat => nat) x (fun _ : nat => f) n)
  =     nat_rect (fun _ : nat => nat) (f x) (fun _ : nat => f) n.
Proof.
  induction n as [|n IH]; cbn.
  - reflexivity.
  - now rewrite IH.
Qed.

Lemma iter_succ_nat (n:nat) (f:nat->nat) (x:nat) :
  Nat.iter (S n) f x = Nat.iter n f (f x).
Proof.  cbn. unfold Nat.iter. apply nat_rect_f_fusion. Qed.

(* Main lemma (Sec. 15, “same letter k times” closed form):
   Nat.iter k (inv_letter_update r p) m
   = 2^{(alpha(r)+6p)k} * m + krow(r) * ∑_{t=0}^{k-1} 2^{(alpha(r)+6p)t}. *)
Lemma inv_iter_same_letter (r:Row) (p:nat) :
  forall k m,
    Nat.iter k (inv_letter_update r p) m
    = pow2A r p k * m + krow r * geom_sum (alpha r + 6*p) k.
Proof.
  intros k m; revert m.
  induction k as [|k IH]; intros m.
  - (* k = 0 *)
    unfold pow2A. rewrite Nat.mul_0_r.
    unfold pow2. rewrite Nat.pow_0_r.
    now rewrite Nat.mul_1_l, Nat.mul_0_r, Nat.add_0_r.
  - (* k = S k *)
    (* expose the S-case of Nat.iter, then match IH *)
    set (F := inv_letter_update r p).
    cbn [Nat.iter].             (* Nat.iter (S k) F m -> Nat.iter k F (F m) *)
    unfold Nat.iter at 1.
    change (nat_rect (fun _ : nat => nat) m (fun _ : nat => F) k)  with (Nat.iter k F m).
    subst F.
    fold (Nat.iter (S k) (inv_letter_update r p) m).
    (* open the S-case *)
    rewrite (iter_succ_nat k (inv_letter_update r p) m).
    (* now rewrite the inner iter with IH *)
    rewrite IH with (m := inv_letter_update r p m).
    set (a := alpha r + 6*p).
    unfold inv_letter_update.
    (* put pow2A at k as 2^{a*k} *)
    replace (pow2A r p k) with (pow2 (a*k)) by (unfold pow2A, a; reflexivity).
    (* distribute: 2^{a*k}*(2^a*m + krow) + krow*sum_k *)
    rewrite Nat.mul_add_distr_l.
    (* first term: (2^{a*k} * 2^a) * m = 2^{a*k+a} * m *)
    rewrite Nat.mul_assoc.
    replace (pow2 (a*k) * pow2 a) with (pow2 (a*k + a))
      by (unfold pow2; rewrite Nat.pow_add_r; reflexivity).
    (* match RHS scale: pow2A at S k is 2^{a*(S k)} = 2^{a*k + a} *)
    replace (pow2A r p (S k)) with (pow2 (a*k + a))
      by (unfold pow2A, a; rewrite Nat.mul_succ_r; reflexivity).
    (* combine the two krow-terms: 2^{a*k}*krow + krow*sum_k = krow*(2^{a*k} + sum_k) *)
    rewrite Nat.mul_comm with (n := pow2 (a*k)) (m := krow r).
    (* 1) Turn the middle pow2 into pow2 a, then combine powers *)
    replace (pow2 (alpha r + 6 * p)) with (pow2 a) by reflexivity.
    replace (pow2 (a * k) * pow2 a * m) with (pow2 (a * k) * (pow2 a * m)) by lia.
    rewrite Nat.mul_assoc.  (* pow2 (a*k) * pow2 a * m = (pow2 (a*k) * pow2 a) * m *)
    replace (pow2 (a * k) * pow2 a)
      with (pow2 (a * k + a))
      by (unfold pow2; rewrite Nat.pow_add_r; reflexivity).
    (* Bring the two krow-terms together and factor them *)
    rewrite <- Nat.add_assoc.
    rewrite (Nat.add_comm (krow r * pow2 (a * k)) (krow r * geom_sum a k)).
    rewrite Nat.add_assoc.
    (* bring the krow-terms together and factor *)
    rewrite <- Nat.add_assoc.
    rewrite (Nat.add_comm (krow r * geom_sum a k) (krow r * pow2 (a*k))).
    rewrite Nat.add_assoc.
    replace (krow r * pow2 (a * k) + krow r * geom_sum a k) with (krow r * (pow2 (a * k) + geom_sum a k)) by lia.   (* krow r * (pow2 (a*k) + geom_sum a k) *)
    (* fold the geometric sum at S k *)
    rewrite Nat.add_comm.             (* pow2 (a*k) + geom_sum a k *)
    replace (pow2 (a*k) + geom_sum a k)
      with (geom_sum a (S k)) by (simpl; reflexivity).
    (* 1) Reassociate and bring the pow2(...)*m term to the front *)
    rewrite Nat.add_assoc.
    rewrite (Nat.add_comm (krow r * geom_sum a k) (pow2 (a * k + a) * m)).
    rewrite <- Nat.add_assoc.
    (* Now: pow2(...)*m + (krow r * geom_sum a k + krow r * pow2 (a*k)) *)
    (* 2) Factor krow r from the last two terms *)
    rewrite <- Nat.mul_add_distr_l.
    (* We have: pow2(...)*m + krow r * (geom_sum a k + pow2 (a*k)) *)
    (* 3) Commute inside the parentheses to match the S-case pattern *)
    rewrite Nat.add_comm.
    (* Now: pow2(...)*m + krow r * (pow2 (a*k) + geom_sum a k) *)
    replace (geom_sum a k + pow2 (a * k))
      with (pow2 (a*k) + geom_sum a k) by lia.
    (* 4) Fold the geometric sum at S k *)
    replace (pow2 (a * k) + geom_sum a k)
      with (geom_sum a (S k)) by (simpl; reflexivity).
    replace (krow r * geom_sum a (S k) + pow2 (a * k + a) * m)
      with (pow2 (a * k + a) * m + krow r * geom_sum a (S k)) by lia.
    reflexivity.
Qed.

(* We keep the table and coverage facts abstract here; they are used by
   existence/uniqueness lemmas rather than by the m–evolution algebra.
   Add your own Parameters/Section if needed. *)
Parameter table : list Row.

(* --- Index-evolution primitives --- *)

Lemma inv_letter_update_mono r p :
  forall m1 m2, m1 <= m2 ->
  inv_letter_update r p m1 <= inv_letter_update r p m2.
Proof.
  intros m1 m2 Hle.
  unfold inv_letter_update.
  apply Nat.add_le_mono_r.
  apply Nat.mul_le_mono_nonneg_l; [apply Nat.le_0_l|assumption].
Qed.

(** Words of inverse letters: we model a word as a list of (r,p) pairs. *)
Definition Letter := (Row * nat)%type.

Fixpoint inv_word_update (w:list Letter) (m:nat) : nat :=
  match w with
  | nil => m
  | (r,p)::ws => inv_word_update ws (inv_letter_update r p m)
  end.

(** Affine composition along a word.  We accumulate the product of scales
    and the translated offsets. *)
Fixpoint word_scale (w:list Letter) : nat :=
  match w with
  | nil => 1
  | (r,p)::ws => pow2 (alpha r + 6*p) * word_scale ws
  end.

Fixpoint word_offset (w:list Letter) : nat :=
  match w with
  | nil => 0
  | (r,p)::ws => krow r * word_scale ws + word_offset ws
  end.

(* Use the cons rules (prove once; they’re reflexive if your Fixpoints match) *)
Lemma word_scale_cons r p ws :
  word_scale ((r, p) :: ws) = pow2 (alpha r + 6*p) * word_scale ws.
Proof. reflexivity. Qed.

Lemma word_offset_cons r p ws :
  word_offset ((r, p) :: ws) = krow r * word_scale ws + word_offset ws.
Proof. reflexivity. Qed.


Lemma inv_word_affine_goal :
  forall (ws:list Letter) m,
    inv_word_update ws m = word_scale ws * m + word_offset ws.
Proof.
  induction ws as [| [r p] ws IH]; intros m.
  - simpl. lia.
  - 
    set (A := pow2 (alpha r + 6*p)).
    unfold inv_letter_update.
    unfold inv_word_update.
    rewrite IH.
    unfold inv_letter_update.
    (* LHS: word_scale ws * (A*m + krow r) + word_offset ws *)
    rewrite Nat.mul_add_distr_l.            (* = word_scale ws*A*m + word_scale ws*krow + offset *)
    rewrite Nat.mul_assoc.                  (* = (word_scale ws*A)*m + word_scale ws*krow + offset *)    
    rewrite <- Nat.mul_assoc.               (* align (A*word_scale ws)*m on RHS shape *)    
    repeat rewrite <-A.
    repeat rewrite A.
     change (pow2 (alpha r + 6 * p)) with (A).
    (* RHS after [simpl] is: (A * word_scale ws) * m + (krow r + A * word_offset ws) *) 
    replace (word_scale ws * (A * m))
      with ((word_scale ws * A) * m) by (rewrite Nat.mul_assoc; reflexivity).
    rewrite (Nat.mul_comm (word_scale ws) A).
    rewrite <- Nat.mul_assoc.    
    (* (A * word_scale ws) * m *)
    rewrite (Nat.mul_comm (word_scale ws) (krow r)).     (* word_scale ws * krow r -> krow r * word_scale ws *)
    (* Make the RHS explicit via the cons equations *)
    symmetry.
    match goal with
    | |- context [ word_scale ((r,p)::ws) ] => idtac "found word_scale-cons"
    | _ => idtac "not found"
    end.    
    match goal with
    | |- context [ word_offset ((r,p)::ws) ] => idtac "found word_offset-cons"
    | _ => idtac "not found"
    end.
    pose proof (word_scale_cons r p ws)  as Hsc.
    pose proof (word_offset_cons r p ws) as Hof.

    (* Rewrite the exact products/sums, not just the head:
      This avoids matching problems even if there’s extra structure around them. *)
    replace (word_scale ((r,p)::ws) * m)
      with ((pow2 (alpha r + 6*p) * word_scale ws) * m)
      by (rewrite Hsc; reflexivity).

    replace (word_offset ((r,p)::ws))
      with (krow r * word_scale ws + word_offset ws)
      by (rewrite Hof; reflexivity).    
    setoid_rewrite (word_scale_cons r p ws).
    setoid_rewrite (word_offset_cons r p ws).
    (* Turn the first product into A * word_scale ws * m *)
    replace (pow2 (alpha r + 6 * p) * word_scale ws * m)
      with (A * word_scale ws * m) by (subst A; reflexivity).

    (* Match the RHS parenthesization A * (word_scale ws * m) *)
    rewrite <- Nat.mul_assoc.
    lia.
Qed.

Lemma inv_word_update_cons_comp (r:Row) (p:nat) (ws:list Letter) (m:nat) :
  inv_word_update ((r,p)::ws) m
  = inv_word_update ws (inv_letter_update r p m).
Proof. reflexivity. Qed.

Lemma inv_word_affine
  (ws:list Letter) :
  forall m, inv_word_update ws m = word_scale ws * m + word_offset ws.
Proof.
  induction ws as [|[r p] ws IH]; intro m.
  - (* empty word *)
    simpl; lia.
  - (* cons *)
    (* use the definitional cons for inv_word_update *)
    set (A := pow2 (alpha r + 6*p)).
    setoid_rewrite (word_scale_cons r p ws).
    setoid_rewrite (word_offset_cons r p ws).
    rewrite inv_word_update_cons_comp.    
    specialize (IH (inv_letter_update r p m)).
    rewrite IH.              (* => word_scale ws * inv_letter_update r p m + word_offset ws *)

    (* Expand the single-letter update *)
    unfold inv_letter_update.  (* = A * m + krow r *)

    (* Distribute and align products *)
    rewrite Nat.mul_add_distr_l.   (* word_scale ws*A*m + word_scale ws*krow r + word_offset ws *)
    rewrite Nat.mul_assoc.         (* (word_scale ws*A)*m + ... *)
    repeat rewrite <-A.
    repeat rewrite A.
    change (pow2 (alpha r + 6 * p)) with (A).
    rewrite (Nat.mul_comm (word_scale ws) A).
    rewrite <- Nat.mul_assoc.      (* A*word_scale ws*m + ... *)
    rewrite (Nat.mul_comm (word_scale ws) (krow r)).
    lia.
Qed.

Lemma inv_letter_update_affine (r:Row) (p m:nat) :
  inv_letter_update r p m
  = pow2 (alpha r + 6*p) * m + krow r.
Proof. reflexivity. Qed.

Lemma inv_word_affine_cons
  (r:Row) (p:nat) (ws:list Letter)
  (Htail : forall z, inv_word_update ws z = word_scale ws * z + word_offset ws)
  (m:nat) :
  inv_word_update ((r,p)::ws) m
  = pow2 (alpha r + 6*p) * word_scale ws * m
    + (krow r * word_scale ws + word_offset ws).
Proof.  
  remember (pow2 (alpha r + 6*p)) as A eqn:HeqA.
  (* HeqA : A = pow2 (alpha r + 6*p) *)
  (* Now `rewrite <- HeqA` turns `pow2 (alpha r + 6*p)` into `A`. *)
  rewrite inv_word_update_cons_comp.
  specialize (Htail (inv_letter_update r p m)).
  rewrite Htail.
  unfold inv_letter_update; rewrite <- HeqA by reflexivity.
  rewrite Nat.mul_add_distr_l.
  rewrite Nat.mul_assoc.
  rewrite (Nat.mul_comm (word_scale ws) A), <- Nat.mul_assoc.
  rewrite (Nat.mul_comm (word_scale ws) (krow r)).
  lia.  
Qed.

Lemma inv_word_update_cons_scaled
  (r:Row) (p:nat) (ws:list Letter)
  (Htail : forall z, inv_word_update ws z = word_scale ws * z + word_offset ws)
  (m:nat) :
  inv_word_update ((r,p)::ws) m
  = word_scale ws * inv_letter_update r p m + word_offset ws.
Proof.
  rewrite inv_word_update_cons_comp.
  specialize (Htail (inv_letter_update r p m)).
  exact Htail.
Qed.

(** Monotonicity of the word action in m. *)
Lemma inv_word_mono w :
  forall m1 m2, m1 <= m2 ->
  inv_word_update w m1 <= inv_word_update w m2.
Proof.
  induction w as [|[r p] ws IH]; intros m1 m2 Hle; simpl.
  - exact Hle.
  - eapply IH. apply inv_letter_update_mono; assumption.
Qed.

Lemma pow2_ge_1 (e:nat) : 1 <= pow2 e.
Proof.
  induction e as [|e IHe]; unfold pow2 in *.
  - (* e = 0 *) rewrite Nat.pow_0_r; lia.
  - (* e = S e *) rewrite Nat.pow_succ_r' by lia.  (* 2^(S e) = 2^e * 2 *)
    lia.    
Qed.

Lemma mul_ge_1 (a b : nat) :
  1 <= a -> 1 <= b -> 1 <= a * b.
Proof.
  intros Ha Hb.
  (* From 1 <= a and b > 0, we get 1*b <= a*b *)
  assert (bpos : 0 < b) by lia.
  assert (Hstep : 1 * b <= a * b).
  { apply Nat.mul_le_mono_pos_r; [exact bpos | exact Ha]. }
  (* Since 1 <= b, transitivity gives 1 <= a*b *)
  eapply Nat.le_trans; [exact Hb |].
  lia.  
Qed.

Lemma word_scale_ge_1 (ws:list Letter) : 1 <= word_scale ws.
Proof.
  induction ws as [|[r p] ws IH].
  - simpl; lia.                       (* word_scale [] = 1 *)
  - (* word_scale ((r,p)::ws) = pow2(..)*word_scale ws >= 1*1 *)
    pose proof (pow2_ge_1 (alpha r + 6*p)) as Hpow.
    setoid_rewrite (word_scale_cons r p ws).
    set (A := pow2 (alpha r + 6 * p)).
    set (B := word_scale ws).
    assert (Apos : 0 < pow2 (alpha r + 6 * p)) by lia.
    assert (Bpos : 0 < word_scale ws) by lia.
    apply (mul_ge_1 (pow2 (alpha r + 6*p)) (word_scale ws)); assumption.    
Qed.

(** Nonnegativity / growth lower bound: since all scales are >= 1,
    m does not decrease under inverse updates. *)
Lemma word_scale_ge1 w : 1 <= word_scale w.
Proof.
  induction w as [|[r p] ws IH]; [|]. 
  - unfold word_scale; lia.
  - repeat rewrite word_scale_cons.
    pose proof (Nat.pow_nonzero 2 (alpha r + 6*p)) as Hpow.
    pose proof (IH) as Hs.
    set (A := pow2 (alpha r + 6*p)).
    set (B := word_scale ws).
    assert (HA : 1 <= A) by (subst A; apply pow2_ge_1).
    assert (HB : 1 <= B) by (subst B; apply word_scale_ge_1).
    assert (HposA : 0 < A) by lia.
    assert (Hpos1 : 0 < 1) by lia.
    apply (mul_ge_1 (A) (B)); assumption.        
Qed.

Lemma succ_le_scaled (s k : nat) :
  1 <= s -> S k <= s * S k.
Proof.
  intro Hs.
  assert (Sk_pos : 0 < S k) by lia.
  replace (S k) with (1 * S k) by lia.
  replace (s * (1 * S k)) with (s * S k) by lia.
  apply Nat.mul_le_mono_pos_r; [lia| exact Hs].  
Qed.

Lemma le_self_le_scaled_plus (s m o : nat) :
  1 <= s -> m <= s * m + o.
Proof.
  intros Hs.
  destruct m as [|k].
  - simpl; lia.                      (* 0 ≤ o *)
  - (* k = S k *)
    assert (H : S k <= s * S k).
    { apply succ_le_scaled; assumption. }
    lia.
Qed.

Lemma inv_word_lower_bound w m :
  m <= inv_word_update w m.
Proof.
  rewrite inv_word_affine.
  pose proof (word_scale_ge1 w) as Hs.
  apply le_self_le_scaled_plus; exact Hs.  
Qed.

(** Stability modulo 3 for the index part contributed by j (if needed).
    You can specialize this to your document’s exact invariant statement. *)
Lemma inv_letter_mod3 r p m :
  (inv_letter_update r p m) mod 3
  = (pow2 (alpha r + 6*p) * m + krow r) mod 3.
Proof. reflexivity. Qed.

(* A convenient statement connecting “inverse word” with the forward
   Collatz step count e along the same word, when each letter’s alpha
   contributes additively. Adjust if your Sec. 15 uses a slightly
   different convention for e-accumulation. *)
Fixpoint word_exponent (w:list Letter) : nat :=
  match w with
  | nil => 0
  | (r,p)::ws => (alpha r + 6*p) + word_exponent ws
  end.

Lemma cons_scale_pow2_sum_param
  (r:Row) (p:nat) (ws:list Letter)
  (Hws : word_scale ws = pow2 (word_exponent ws)) :
  pow2 (alpha r + 6 * p) * word_scale ws
  = pow2 (alpha r + 6 * p + word_exponent ws).
Proof.
  rewrite Hws.
  unfold pow2; rewrite Nat.pow_add_r.
  rewrite <- Nat.mul_assoc.
  rewrite <- Nat.pow_add_r.        (* 2^(alpha r + 6*p) * 2^(word_exponent ws) *)  
  rewrite <- Nat.pow_add_r.        (* 2^((alpha r + 6*p) + word_exponent ws) *)
  rewrite Nat.add_assoc.
  reflexivity.
Qed.

Lemma word_exponent_cons r p ws :
  word_exponent ((r, p) :: ws) = (alpha r + 6*p) + word_exponent ws.
Proof. reflexivity. Qed.

Lemma word_scale_is_pow2_of_sum w :
  word_scale w = pow2 (word_exponent w).
Proof.
  induction w as [|[r p] ws IH]; [reflexivity|].
  setoid_rewrite (word_scale_cons r p ws).
  setoid_rewrite (word_exponent_cons r p ws).
  apply cons_scale_pow2_sum_param.
  exact IH.  
Qed.

(** Telescoping form for two concatenated words. *)
Lemma inv_word_concat (u v : list Letter) (m:nat) :
  inv_word_update (u ++ v) m
  = inv_word_update v (inv_word_update u m).
Proof.
  revert m.
  induction u as [|[r p] u IH]; intro m; simpl.
  - reflexivity.
  - (* goal: inv_word_update (u ++ v) (inv_letter_update r p m)
           = inv_word_update v (inv_word_update u (inv_letter_update r p m)) *)
    specialize (IH (inv_letter_update r p m)).
    exact IH.
Qed.

Lemma word_scale_concat u v :
  word_scale (u ++ v) = word_scale u * word_scale v.
Proof.
  induction u as [|[r p] u IHu]; simpl; [lia|].
  rewrite IHu. lia.
Qed.

Lemma word_offset_concat (u v:list Letter) :
  word_offset (u ++ v) = word_offset v + word_scale v * word_offset u.
Proof.
  induction u as [|[r p] u IHu]; simpl.  
  - lia.                      (* 0 = o_v + S_v * 0 *)
  - (* (r,p)::u ++ v = (r,p)::(u++v) *)
    rewrite IHu.              (* o_(u++v) = o_v + S_v * o_u *)
    rewrite word_scale_concat.
    (* LHS: k_r * S_(u++v) + (o_v + S_v*o_u)
            = k_r * (S_v * S_u) + o_v + S_v*o_u
       RHS: o_v + S_v * (k_r * S_u + o_u)
            = o_v + S_v*k_r*S_u + S_v*o_u
       These are equal by associativity/commutativity/distributivity in nat. *)
    lia.
Qed.

(** Main “evolution of m” along an inverse word: affine result. *)
Lemma m_after_inverse_word w m :
  inv_word_update w m = pow2 (word_exponent w) * m + word_offset w.
Proof.
  rewrite inv_word_affine, word_scale_is_pow2_of_sum. reflexivity.
Qed.

(* --- Hooks to the paper text (LaTeX mapping) ---------------------------

In the LaTeX, this corresponds to Sec. 15’s claim that the index m evolves
affinely along inverse words (each letter (r,p) contributes scale
2^{alpha(r)+6p} and offset krow(r)), and that concatenation of words
yields the usual affine composition laws:

  A(u ++ v) = A(u) A(v),
  B(u ++ v) = B(u) + A(u) B(v).

These are exactly Lemmas [word_scale_concat], [word_offset_concat], and
[m_after_inverse_word].

You can cite them where you discuss “inverse word semantics” and the
transport of the m–coordinate along a word.

----------------------------------------------------------------------- *)

End Sec15_Evolution_of_the_index_m_along_inverse_words.
