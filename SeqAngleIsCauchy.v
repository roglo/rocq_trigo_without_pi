(** * SeqAngleIsCauchy

    Let α be an angle and n a natural number.

    The present module proves that the sequence defined by
    αᵢ = ⌊2^i / n⌋·(α / 2^i) is Cauchy.
    We will see later that its limit α' satisfies n·α' = α,
    and can therefore be interpreted as α / n.
*)

Set Nested Proofs Allowed.
Require Import Stdlib.Arith.Arith.
Require Import RingLike.Utf8.

Require Import RingLike.Core.
Require Import RingLike.RealLike.
Require Import RingLike.Misc.

Require Import AngleDef Angle TrigoWithoutPiExt.
Require Import Order.
Require Import AngleDiv2.
Require Import AngleDiv2Add.
Require Import AngleAddLeMonoL.
Require Import Distance.

Section a.

Context {T : Type}.
Context {ro : ring_like_op T}.
Context {rp : ring_like_prop T}.
Context {rl : real_like_prop T}.
Context {ac : angle_ctx T}.

Definition seq_angle_to_div_nat α (n i : nat) := (2 ^ i / n * (α /₂^i))%A.

Theorem angle_le_pow2_log2 :
  ∀ n α1 α2,
  n ≠ 0
  → angle_mul_nat_div_2π n α1 = 0
  → (n * α1 ≤ α2
  → α1 ≤ α2 /₂^Nat.log2 n)%A.
Proof.
intros * Hnz Haov Hn.
apply Nat.neq_0_lt_0 in Hnz.
rewrite <- (angle_div_2_pow_mul_2_pow (Nat.log2 n) α1).
rewrite <- angle_div_2_pow_mul. 2: {
  apply (angle_mul_nat_not_overflow_le_l _ n); [ | easy ].
  now apply Nat.log2_spec.
}
apply angle_div_2_pow_le.
apply (angle_le_trans _ (n * α1)); [ | easy ].
apply angle_mul_le_mono_r; [ easy | ].
now apply Nat.log2_spec.
Qed.

Theorem seq_angle_to_div_nat_not_overflow :
  ∀ α n i,
  2 ^ i / n ≤ 2 ^ i
  → angle_mul_nat_div_2π n (seq_angle_to_div_nat α n i) = 0.
Proof.
intros * Hin.
apply Nat.eq_dne.
intros H.
progress unfold seq_angle_to_div_nat in H.
destruct (Nat.eq_dec n 0) as [Hnz| Hnz]; [ now subst n | ].
apply angle_mul_nat_div_2π_true_assoc in H.
apply H; clear H.
apply (angle_mul_nat_not_overflow_le_l _ (2 ^ i)). 2: {
  apply angle_mul_nat_div_2π_pow_div.
}
now apply Nat.Div0.mul_div_le.
Qed.

Theorem seq_angle_to_div_nat_div_2_le_straight_div_pow2_log2 :
  ∀ n i α, (seq_angle_to_div_nat α n i /₂ ≤ π /₂^Nat.log2 n)%A.
Proof.
intros.
progress unfold seq_angle_to_div_nat.
destruct (Nat.eq_dec n 0) as [Hnz| Hnz]. {
  subst n; cbn.
  rewrite angle_0_div_2.
  apply angle_nonneg.
}
assert (Hin : 2 ^ i / n ≤ 2 ^ i). {
  apply Nat.Div0.div_le_upper_bound.
  now apply Nat.le_mul_l.
}
rewrite <- angle_mul_nat_div_2. 2: {
  apply (angle_mul_nat_not_overflow_le_l _ (2 ^ i)); [ easy | ].
  apply angle_mul_nat_div_2π_pow_div.
}
rewrite <- angle_div_2_pow_succ_r_1.
apply angle_le_pow2_log2; [ easy | | ]. {
  apply Nat.eq_dne.
  intros H.
  apply angle_mul_nat_div_2π_true_assoc in H.
  apply H; clear H.
  apply (angle_mul_nat_not_overflow_le_l _ (2 ^ i)). {
    now apply Nat.Div0.mul_div_le.
  }
  rewrite angle_div_2_pow_succ_r_2.
  apply angle_mul_nat_div_2π_pow_div.
}
rewrite angle_div_2_pow_succ_r_1.
rewrite angle_mul_nat_div_2. 2: {
  apply (angle_mul_nat_not_overflow_le_l _ (2 ^ i)); [ easy | ].
  apply angle_mul_nat_div_2π_pow_div.
}
rewrite angle_mul_nat_div_2; [ apply angle_div_2_le_straight | ].
specialize (seq_angle_to_div_nat_not_overflow α n i Hin) as H1.
progress unfold seq_angle_to_div_nat in H1.
now destruct (Nat.eq_dec n 0).
Qed.

Theorem angle_le_pow2_pred :
  ∀ n α1 α2,
  n ≠ 0
  → (α1 /₂ ≤ α2 /₂^n)%A
  → (α1 ≤ α2 /₂^(n-1))%A.
Proof.
intros * Hnz H12.
destruct n; [ easy | clear Hnz ].
rewrite Nat_sub_succ_1.
specialize (angle_mul_le_mono_l _ _ H12 2) as H1.
rewrite angle_div_2_pow_succ_r_1 in H1.
do 2 rewrite angle_div_2_mul_2 in H1.
apply H1.
rewrite <- (Nat.mul_1_r 2).
rewrite Nat.mul_1_r; cbn.
rewrite angle_add_overflow_0_r.
rewrite angle_add_0_r.
apply Nat_eq_b2n_0.
apply angle_add_overflow_div_2_div_2.
Qed.

Theorem seq_angle_to_div_nat_le_straight_div_pow2_log2_pred :
  ∀ n i α,
  n ≠ 1
  → (seq_angle_to_div_nat α n i ≤ π /₂^(Nat.log2 n - 1))%A.
Proof.
intros * Hn1.
destruct (Nat.eq_dec n 0) as [Hnz| Hnz]. {
  subst n.
  apply angle_nonneg.
}
specialize seq_angle_to_div_nat_div_2_le_straight_div_pow2_log2 as H1.
specialize (H1 n i α).
apply angle_le_pow2_pred; [ | easy ].
intros H.
apply Nat.log2_null in H.
destruct n; [ easy | ].
apply Nat.succ_le_mono in H.
apply Nat.le_0_r in H.
now subst n.
Qed.

Theorem angle_div_pow2_1 : ∀ α, (α /₂^1 = α /₂)%A.
Proof. easy. Qed.

Theorem angle_div_2_pow_le_compat_l :
  ∀ a b α, b ≤ a → (α /₂^a ≤ α /₂^b)%A.
Proof.
intros * Hab.
revert b Hab.
induction a; intros. {
  apply Nat.le_0_r in Hab; subst b.
  apply angle_le_refl.
}
destruct b; cbn. {
  eapply angle_le_trans; [ | apply angle_div_2_le ].
  apply angle_div_2_le_compat.
  apply angle_div_2_pow_le_diag.
}
apply Nat.succ_le_mono in Hab.
apply angle_div_2_le_compat.
now apply IHa.
Qed.

Theorem rngl_cos_lt_angle_eucl_dist_lt :
  ∀ a α1 α2,
  (0 ≤ a)%L
  → (1 - a² / 2 < rngl_cos (α2 - α1))%L
  ↔ (angle_eucl_dist α1 α2 < a)%L.
Proof.
destruct_ac.
destruct (Nat.eq_dec (rngl_characteristic T) 1) as [Hc1| Hc1]. {
  specialize (rngl_characteristic_1 Hos Hc1) as H1.
  intros * Ha.
  rewrite (H1 (_ - _))%L, (H1 (rngl_cos _)).
  rewrite (H1 (angle_eucl_dist _ _)), (H1 a).
  easy.
}
intros * Hza.
rewrite angle_eucl_dist_is_sqrt.
rewrite <- (rngl_abs_nonneg_eq Hop Hor √_). 2: {
  apply rl_sqrt_nonneg.
  apply (rngl_mul_nonneg_nonneg Hos Hor). {
    apply (rngl_0_le_2 Hos Hto).
  }
  apply (rngl_le_0_sub Hop Hor).
  apply rngl_cos_bound.
}
rewrite <- (rngl_abs_nonneg_eq Hop Hor a) at 2; [ | easy ].
split. {
  intros Hc.
  apply (rngl_squ_lt_abs_lt Hop Hiq Hto).
  rewrite rngl_squ_sqrt. 2: {
    apply (rngl_mul_nonneg_nonneg Hos Hor). {
      apply (rngl_0_le_2 Hos Hto).
    }
    apply (rngl_le_0_sub Hop Hor).
    apply rngl_cos_bound.
  }
  rewrite (rngl_mul_comm Hic).
  apply (rngl_lt_div_r Hop Hiv Hto). {
    apply (rngl_0_lt_2 Hos Hc1 Hto).
  }
  apply (rngl_lt_sub_lt_add_l Hop Hor).
  now apply (rngl_lt_sub_lt_add_r Hop Hor).
} {
  intros Ha.
  apply (rngl_abs_lt_squ_lt Hop Hiq Hto) in Ha. 2: {
    apply (rngl_mul_comm Hic).
  }
  rewrite rngl_squ_sqrt in Ha. 2: {
    apply (rngl_mul_nonneg_nonneg Hos Hor). {
      apply (rngl_0_le_2 Hos Hto).
    }
    apply (rngl_le_0_sub Hop Hor).
    apply rngl_cos_bound.
  }
  rewrite (rngl_mul_comm Hic) in Ha.
  apply (rngl_lt_div_r Hop Hiv Hto) in Ha. 2: {
    apply (rngl_0_lt_2 Hos Hc1 Hto).
  }
  apply (rngl_lt_sub_lt_add_l Hop Hor) in Ha.
  now apply (rngl_lt_sub_lt_add_r Hop Hor) in Ha.
}
Qed.

Theorem rngl_cos_le_angle_eucl_dist_le :
  ∀ a α1 α2,
  (0 ≤ a)%L
  → (1 - a² / 2 ≤ rngl_cos (α2 - α1))%L
  ↔ (angle_eucl_dist α1 α2 ≤ a)%L.
Proof.
destruct_ac.
destruct (Nat.eq_dec (rngl_characteristic T) 1) as [Hc1| Hc1]. {
  specialize (rngl_characteristic_1 Hos Hc1) as H1.
  intros.
  rewrite (H1 (_ - _))%L.
  rewrite (H1 (rngl_cos _)).
  rewrite (H1 (angle_eucl_dist _ _)).
  rewrite (H1 a).
  easy.
}
intros * Hza.
split; intros H12. {
  apply (rngl_lt_eq_cases Hor) in H12.
  apply (rngl_lt_eq_cases Hor).
  destruct H12 as [H12| H12]. {
    now left; apply rngl_cos_lt_angle_eucl_dist_lt.
  }
  right.
  rewrite angle_eucl_dist_is_sqrt.
  rewrite <- H12.
  rewrite (rngl_sub_sub_distr Hop).
  rewrite (rngl_sub_diag Hos).
  rewrite rngl_add_0_l.
  rewrite (rngl_mul_div_assoc Hiv).
  rewrite (rngl_mul_comm Hic).
  rewrite (rngl_mul_div Hi1). 2: {
    apply (rngl_2_neq_0 Hos Hc1 Hto).
  }
  rewrite (rl_sqrt_squ Hop Hto).
  now apply (rngl_abs_nonneg_eq Hop Hor).
} {
  apply (rngl_lt_eq_cases Hor) in H12.
  apply (rngl_lt_eq_cases Hor).
  destruct H12 as [H12| H12]. {
    now left; apply rngl_cos_lt_angle_eucl_dist_lt.
  }
  right.
  rewrite angle_eucl_dist_is_sqrt in H12.
  rewrite <- H12.
  rewrite rngl_squ_sqrt. 2: {
    apply (rngl_mul_nonneg_nonneg Hos Hor). {
      apply (rngl_0_le_2 Hos Hto).
    }
    apply (rngl_le_0_sub Hop Hor).
    apply rngl_cos_bound.
  }
  rewrite (rngl_mul_comm Hic).
  rewrite (rngl_mul_div Hi1). 2: {
    apply (rngl_2_neq_0 Hos Hc1 Hto).
  }
  rewrite (rngl_sub_sub_distr Hop).
  rewrite (rngl_sub_diag Hos).
  apply rngl_add_0_l.
}
Qed.

Theorem seq_angle_to_div_nat_sub :
  ∀ n α p q,
  p ≤ q
  → (seq_angle_to_div_nat α n q - seq_angle_to_div_nat α n p)%A =
    (2 ^ p mod n * 2 ^ (q - p) / n * (α /₂^q))%A.
Proof.
intros * Hpq.
progress unfold seq_angle_to_div_nat.
specialize (Nat.div_mod (2 ^ p) n) as Hx.
destruct (Nat.eq_dec n 0) as [Hnz| Hnz]. {
  subst n; cbn.
  apply angle_sub_0_r.
}
specialize (Hx Hnz).
replace q with (p + (q - p)) by flia Hpq.
rewrite Nat.pow_add_r.
remember (2 ^ p mod n) as c eqn:Hc.
remember (2 ^ p / n) as b eqn:Hb.
rewrite Hx.
rewrite Nat.mul_add_distr_r.
rewrite <- Nat.mul_assoc.
rewrite (Nat.mul_comm n).
rewrite Nat.div_add_l; [ | easy ].
rewrite angle_mul_add_distr_r.
rewrite angle_add_sub_swap.
rewrite angle_div_2_pow_add_r at 1.
rewrite <- angle_mul_nat_assoc.
rewrite angle_div_2_pow_mul_2_pow.
rewrite angle_sub_diag.
rewrite angle_add_0_l.
now replace (p + (q - p)) with q by flia Hpq.
Qed.

Theorem pow2_mod_mul_div :
  ∀ n p q,
  p ≤ q
  → 2 ^ p mod n * 2 ^ (q - p) / n =
    2 ^ q * (2 ^ p mod n) / (2 ^ p * n).
Proof.
intros * Hpq.
destruct (Nat.eq_dec n 0) as [Hnz| Hnz]. {
  now subst n; cbn; rewrite Nat.mul_0_r.
}
rewrite Nat.pow_sub_r; [ | easy | easy ].
rewrite <- Nat.Lcm0.divide_div_mul_exact. 2: {
  exists (2 ^ (q - p)).
  rewrite <- Nat.pow_add_r.
  now rewrite Nat.sub_add.
}
rewrite Nat.mul_comm.
apply Nat.Div0.div_div.
Qed.

Theorem angle_add_overflow_mul_div_pow2 :
  ∀ n i α,
  n < 2 ^ i
  → angle_add_overflow (α /₂^i) (n * (α /₂^i)) = false.
Proof.
destruct_ac.
intros * Hni.
revert α n Hni.
induction i; intros. {
  cbn in Hni.
  apply Nat.succ_le_mono in Hni.
  apply Nat.le_0_r in Hni; subst n.
  apply angle_add_overflow_0_r.
}
destruct (le_dec (S n) (2 ^ i)) as [Hsni| Hsni]. {
  rewrite angle_div_2_pow_succ_r_2.
  now apply IHi.
}
apply Nat.nle_gt in Hsni.
apply -> Nat.le_succ_l in Hni.
apply -> Nat.lt_succ_r in Hsni.
assert (H1 : n = 2 ^ i + n mod 2 ^ i). {
  specialize (Nat.div_mod n (2 ^ i)) as H1.
  assert (H : 2 ^ i ≠ 0) by now apply Nat.pow_nonzero.
  specialize (H1 H); clear H.
  rewrite (Nat_div_less_small 1) in H1; [ now rewrite Nat.mul_1_r in H1 | ].
  now rewrite Nat.mul_1_l.
}
rewrite H1.
rewrite angle_mul_add_distr_r.
rewrite angle_div_2_pow_succ_r_2 at 2.
rewrite angle_div_2_pow_mul_2_pow.
rewrite angle_div_2_pow_succ_r_1.
rewrite angle_mul_nat_div_2. 2: {
  apply (angle_mul_nat_not_overflow_le_l _ (2 ^ i)).
  apply Nat.lt_le_incl, Nat.mod_upper_bound.
  now apply Nat.pow_nonzero.
  apply angle_mul_nat_div_2π_pow_div.
}
apply angle_add_not_overflow_move_add. 2: {
  rewrite <- angle_div_2_add_not_overflow. 2: {
    apply IHi.
    apply Nat.mod_upper_bound.
    now apply Nat.pow_nonzero.
  }
  apply angle_add_overflow_div_2_div_2.
}
apply angle_add_overflow_div_2_div_2.
Qed.

Theorem angle_mul_nat_div_2π_div_pow2 :
  ∀ n i α,
  n ≤ 2 ^ i
  → angle_mul_nat_div_2π n (α /₂^i) = 0.
Proof.
intros * Hni.
revert i α Hni.
induction n; intros; [ easy | cbn ].
apply Nat.eq_add_0.
split. {
  apply IHn.
  apply (Nat.le_trans _ (S n)); [ | easy ].
  apply Nat.le_succ_diag_r.
}
apply Nat_eq_b2n_0.
now apply angle_add_overflow_mul_div_pow2.
Qed.

Theorem angle_mul_div_pow2_le_straight :
  ∀ n i α,
  2 * n ≤ 2 ^ i
  → (n * (α /₂^i) ≤ π)%A.
Proof.
destruct_ac.
intros * Hni.
revert α.
induction i; intros. {
  cbn in Hni.
  rewrite Nat.add_0_r in Hni.
  destruct n; [ apply angle_nonneg | ].
  cbn in Hni.
  apply Nat.succ_le_mono in Hni.
  rewrite <- Nat.add_succ_comm in Hni; cbn in Hni.
  easy.
}
destruct (le_dec (2 * n) (2 ^ i)) as [Hni1| Hni1]. {
  rewrite angle_div_2_pow_succ_r_2.
  now apply IHi.
}
apply Nat.nle_gt in Hni1.
clear IHi.
rewrite Nat.pow_succ_r' in Hni.
apply Nat.mul_le_mono_pos_l in Hni; [ | easy ].
rewrite angle_div_2_pow_succ_r_1.
rewrite angle_mul_nat_div_2. 2: {
  now apply angle_mul_nat_div_2π_div_pow2.
}
apply angle_div_2_le_straight.
Qed.

Theorem angle_mul_div_pow2_le_right :
  ∀ n i α, 4 * n ≤ 2 ^ i → (n * (α /₂^i) ≤ π/₂)%A.
Proof.
destruct_ac.
intros * Hni.
destruct i. {
  destruct n; [ apply angle_nonneg | ].
  cbn in Hni; flia Hni.
}
rewrite angle_div_2_pow_succ_r_1.
rewrite <- angle_straight_div_2.
rewrite Nat.pow_succ_r' in Hni.
replace 4 with (2 * 2) in Hni by easy.
rewrite <- Nat.mul_assoc in Hni.
apply Nat.mul_le_mono_pos_l in Hni; [ | easy ].
rewrite angle_mul_nat_div_2. 2: {
  apply angle_mul_nat_div_2π_div_pow2.
  apply (Nat.le_trans _ (2 * n)); [ | easy ].
  now apply Nat.le_mul_l.
}
apply angle_div_2_le_compat.
now apply angle_mul_div_pow2_le_straight.
Qed.

Theorem exists_nat_such_that_rngl_cos_close_to_1 :
  rngl_is_archimedean T = true →
  ∀ α ε, (0 < ε)%L →
  ∃ N, ∀ p, N ≤ p → (1 - ε² / 2 < rngl_cos (α /₂^p))%L.
Proof.
destruct_ac.
intros Har.
destruct (Nat.eq_dec (rngl_characteristic T) 1) as [Hc1| Hc1]. {
  specialize (rngl_characteristic_1 Hos Hc1) as H1.
  intros * Hε.
  rewrite (H1 ε) in Hε.
  now apply rngl_lt_irrefl in Hε.
}
intros * Hε.
specialize rngl_cos_angle_div_2_pow_tending_to_1 as H1.
specialize (H1 Har α).
progress unfold is_limit_when_seq_tends_to_inf in H1.
cbn in H1.
progress unfold rngl_dist in H1.
specialize (H1 (ε² / 2))%L.
assert (Hε2 : (0 < ε² / 2)%L). {
  apply (rngl_div_pos Hop Hiv Hto). 2: {
    apply (rngl_0_lt_2 Hos Hc1 Hto).
  }
  apply rngl_le_neq.
  split; [ apply (rngl_squ_nonneg Hos Hto) | ].
  apply not_eq_sym.
  intros H.
  apply (eq_rngl_squ_0 Hos) in H. 2: {
    rewrite Bool.orb_true_iff; right.
    rewrite Hi1; cbn.
    apply (rngl_has_eq_dec_or_is_ordered_r Hor).
  }
  now subst ε; apply rngl_lt_irrefl in Hε.
}
specialize (H1 Hε2); clear Hε2.
destruct H1 as (N, HN).
exists N.
intros p Hp.
specialize (HN p Hp).
rewrite (rngl_abs_sub_comm Hop Hto) in HN.
rewrite (rngl_abs_nonneg_eq Hop Hor) in HN. 2: {
  apply (rngl_le_0_sub Hop Hor), rngl_cos_bound.
}
apply (rngl_lt_sub_lt_add_r Hop Hor) in HN.
apply (rngl_lt_sub_lt_add_l Hop Hor) in HN.
easy.
Qed.

Theorem seq_angle_to_div_nat_is_Cauchy :
  rngl_is_archimedean T = true →
  ∀ n α,
  is_Cauchy_sequence angle_eucl_dist (seq_angle_to_div_nat α n).
Proof.
intros Har *.
destruct_ac.
destruct (Nat.eq_dec (rngl_characteristic T) 1) as [Hc1| Hc1]. {
  specialize (rngl_characteristic_1 Hos Hc1) as H1.
  intros * ε Hε.
  rewrite (H1 ε) in Hε.
  now apply rngl_lt_irrefl in Hε.
}
destruct (angle_eq_dec α 0) as [Htz| Htz]. {
  subst α.
  enough (H : is_Cauchy_sequence angle_eucl_dist (λ _, 0%A)). {
    intros ε Hε.
    specialize (H ε Hε).
    destruct H as (N, HN).
    exists N.
    intros p q Hp Hq.
    (* lemma to do seq_angle_to_div_nat_0_l *)
    progress unfold seq_angle_to_div_nat.
    do 2 rewrite angle_0_div_2_pow.
    do 2 rewrite angle_mul_0_r.
    cbn.
    now rewrite angle_eucl_dist_diag.
  }
  (* lemma to do const_seq_is_Cauchy *)
  exists 0.
  intros p q _ _.
  cbn.
  now rewrite angle_eucl_dist_diag.
}
intros * ε Hε.
destruct (Nat.eq_dec n 0) as [Hnz| Hnz]. {
  subst n.
  exists 0.
  intros * _ _.
  cbn.
  now rewrite angle_eucl_dist_diag.
}
destruct (Nat.eq_dec n 1) as [Hn1| Hn1]. {
  subst n.
  exists 0.
  intros * _ _.
  progress unfold seq_angle_to_div_nat.
  do 2 rewrite Nat.div_1_r.
  do 2 rewrite angle_div_2_pow_mul_2_pow.
  cbn.
  now rewrite angle_eucl_dist_diag.
}
assert (Hss : ∀ i, (seq_angle_to_div_nat α n i ≤ π)%A). {
  intros i.
  specialize seq_angle_to_div_nat_le_straight_div_pow2_log2_pred as H1.
  specialize (H1 n i α Hn1).
  eapply angle_le_trans; [ apply H1 | ].
  apply angle_div_2_pow_le_diag.
}
assert (Hsr : n ≤ 3 ∨ ∀ i, (seq_angle_to_div_nat α n i ≤ π/₂)%A). {
  destruct (le_dec n 3) as [Hn3| Hn3]; [ now left | right ].
  apply Nat.nle_gt in Hn3.
  intros i.
  specialize seq_angle_to_div_nat_le_straight_div_pow2_log2_pred as H1.
  specialize (H1 n i α Hn1).
  eapply angle_le_trans; [ apply H1 | ].
  rewrite <- angle_straight_div_2.
  rewrite <- angle_div_pow2_1.
  apply angle_div_2_pow_le_compat_l.
  apply Nat.le_add_le_sub_l; cbn.
  apply Nat.log2_le_pow2; cbn; flia Hn3.
}
assert (He1 : (1 - ε² / 2 < 1)%L). {
  apply (rngl_lt_sub_lt_add_r Hop Hor).
  apply (rngl_lt_sub_lt_add_l Hop Hor).
  rewrite (rngl_sub_diag Hos).
  apply (rngl_div_pos Hop Hiv Hto). 2: {
    apply (rngl_0_lt_2 Hos Hc1 Hto).
  }
  now apply (rngl_mul_pos_pos Hop Hiq Hor).
}
enough (H :
  ∃ N, ∀ p q,
  N ≤ p
  → N ≤ q
  → (1 - ε² / 2 <
      rngl_cos
        (seq_angle_to_div_nat α n p - seq_angle_to_div_nat α n q))%L). {
  destruct H as (N, HN).
  exists N.
  intros p q Hp Hq.
  apply rngl_lt_le_incl in Hε.
  apply rngl_cos_lt_angle_eucl_dist_lt; [ easy | ].
  apply (HN _ _ Hq Hp).
}
enough (H :
  ∃ N, ∀ p q,
  N ≤ p < q
  → (1 - ε² / 2 <
      rngl_cos
        (seq_angle_to_div_nat α n p - seq_angle_to_div_nat α n q))%L). {
  destruct H as (N, HN).
  exists N.
  intros p q Hp Hq.
  destruct (Nat.eq_dec q p) as [Hqp| Hqp]. {
    subst q.
    now rewrite angle_sub_diag; cbn.
  }
  apply rngl_lt_le_incl in Hε.
  destruct (lt_dec p q) as [Hpq| Hpq]; [ now apply HN | ].
  apply Nat.nlt_ge in Hpq.
  rewrite rngl_cos_sub_comm.
  apply HN.
  split; [ easy | ].
  flia Hpq Hqp.
}
enough (H :
  ∃ N, ∀ p q,
  N ≤ p < q
  → (1 - ε² / 2 < rngl_cos (2 ^ p mod n * 2 ^ (q - p) / n * (α /₂^q)))%L). {
  destruct H as (N, HN).
  exists N.
  intros * Hpq.
  rewrite rngl_cos_sub_comm.
  rewrite seq_angle_to_div_nat_sub; [ | flia Hpq ].
  now apply HN.
}
destruct (rngl_ltb_dec (1 - ε² / 2)%L 0) as [Hez| Hze]. {
  apply (rngl_ltb_lt Heo) in Hez.
  exists 2.
  intros * Hpq.
  apply (rngl_lt_le_trans Hor _ 0); [ easy | ].
  rewrite pow2_mod_mul_div; [ | flia Hpq ].
  apply rngl_le_0_cos; left.
  apply angle_mul_div_pow2_le_right.
  apply (Nat.le_trans _ (4 * (2 ^ q * n / (2 ^ p * n)))). {
    apply Nat.mul_le_mono_l.
    apply Nat.Div0.div_le_mono.
    apply Nat.mul_le_mono_l.
    now apply Nat.lt_le_incl, Nat.mod_upper_bound.
  }
  rewrite Nat.Div0.div_mul_cancel_r; [ | easy ].
  destruct q; [ flia Hpq | ].
  destruct q; [ flia Hpq | ].
  do 2 rewrite Nat.pow_succ_r'.
  rewrite Nat.mul_assoc.
  apply Nat.mul_le_mono_l.
  apply Nat.Div0.div_le_upper_bound.
  apply Nat.mul_le_mono_r.
  destruct p; [ easy | ].
  destruct p; [ flia Hpq | ].
  do 2 rewrite Nat.pow_succ_r'.
  rewrite Nat.mul_assoc.
  apply Nat.le_mul_r.
  now apply Nat.pow_nonzero.
}
apply (rngl_ltb_ge_iff Hto) in Hze.
move Hze after He1.
enough (H :
  ∃ N, ∀ p q,
  N ≤ p < q
  → (1 - ε² / 2 < rngl_cos (2 ^ (q - p) * (α /₂^q)))%L). {
  destruct H as (N, HN).
  exists (N + 1).
  intros * Hpq.
  assert (Hpq' : N ≤ p < q) by flia Hpq.
  eapply (rngl_lt_le_trans Hor); [ now apply HN | ].
  apply rngl_cos_decr.
  split. {
    apply angle_mul_le_mono_r. {
      apply (angle_mul_nat_div_2π_le_r _ (α /₂^(q - p))). 2: {
        apply angle_mul_nat_div_2π_pow_div.
      }
      apply angle_div_2_pow_le_compat_l.
      apply Nat.le_sub_l.
    }
    apply Nat.Div0.div_le_upper_bound.
    apply Nat.mul_le_mono_r.
    apply Nat.lt_le_incl.
    now apply Nat.mod_upper_bound.
  }
  apply angle_mul_div_pow2_le_straight.
  destruct p; [ flia Hpq | ].
  rewrite <- Nat.pow_succ_r'.
  apply Nat.pow_le_mono_r; [ easy | ].
  rewrite <- Nat.sub_succ_l; [ | flia Hpq ].
  cbn.
  apply Nat.le_sub_l.
}
enough (H :
  ∃ N, ∀ p,
  N ≤ p
  → (1 - ε² / 2 < rngl_cos (α /₂^p))%L). {
  destruct H as (N, HN).
  exists (N + 1).
  intros * Hpq.
  replace q with (p + (q - p)) at 1 by flia Hpq.
  rewrite angle_div_2_pow_add_r.
  rewrite angle_div_2_pow_mul_2_pow.
  apply HN; flia Hpq.
}
now apply (exists_nat_such_that_rngl_cos_close_to_1 Har).
Qed.

End a.
