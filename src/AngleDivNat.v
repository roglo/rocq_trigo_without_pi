Set Nested Proofs Allowed.
Require Import Stdlib.Arith.Arith.
Require Init.

Require Import RingLike.Utf8.
Require Import RingLike.Core.
Require Import RingLike.RealLike.
Require Import RingLike.Misc.

Require Import AngleDef Angle TrigoWithoutPiExt.
Require Import Order.
Require Import AngleDiv2.
Require Import AngleDiv2Add.
Require Import AngleAddLeMonoL.
Require Import AngleTypeIsComplete.
Require Import Distance.
Require Import SeqAngleIsCauchy.
Require Import TacChangeAngle.
Require Import AngleAddOverflowEquiv.
Require Import AngleAddOverflowLe.

Section a.

Context {T : Type}.
Context {ro : ring_like_op T}.
Context {rp : ring_like_prop T}.
Context {rl : real_like_prop T}.
Context {ac : angle_ctx T}.

Definition angle_div_nat α n α' :=
  angle_lim (seq_angle_to_div_nat α n) α'.

Theorem angle_lim_eq_compat :
  ∀ a b f g α,
  (∀ i, f (i + a) = g (i + b))
  → angle_lim f α
  → angle_lim g α.
Proof.
intros * Hfg Hf.
eapply is_limit_when_seq_tends_to_inf_eq_compat; [ apply Hfg | easy ].
Qed.

Theorem angle_lim_opp :
  ∀ f α, angle_lim f α → angle_lim (λ i, (- f i)%A) (- α).
Proof.
intros * Hft.
intros ε Hε.
specialize (Hft ε Hε).
destruct Hft as (N, HN).
exists N.
intros n Hn.
cbn.
rewrite angle_eucl_dist_opp_opp.
now apply HN.
Qed.

Theorem angle_lim_move_0_r :
  ∀ f α, angle_lim f α ↔ angle_lim (λ i, (f i - α)%A) 0%A.
Proof.
intros.
split; intros Hlim. {
  intros ε Hε.
  specialize (Hlim ε Hε).
  destruct Hlim as (N, HN).
  exists N.
  intros n Hn.
  specialize (HN n Hn).
  cbn in HN.
  now rewrite angle_eucl_dist_move_0_r in HN.
} {
  intros ε Hε.
  specialize (Hlim ε Hε).
  destruct Hlim as (N, HN).
  exists N.
  intros n Hn.
  specialize (HN n Hn).
  cbn.
  now rewrite angle_eucl_dist_move_0_r.
}
Qed.

Theorem angle_eucl_dist_2_mul_sqrt_sub_sqrt :
  ∀ α1 α2,
  (α2 ≤ α1)%A
  → (0 ≤ rngl_sin α1)%L
  → (0 ≤ rngl_sin α2)%L
  → angle_eucl_dist α1 α2 =
    (2 *
     (√((1 - rngl_cos α1) / 2) * √((1 + rngl_cos α2) / 2) -
      √((1 + rngl_cos α1) / 2) * √((1 - rngl_cos α2) / 2)))%L.
Proof.
destruct_ac.
destruct (Nat.eq_dec (rngl_characteristic T) 1) as [Hc1| Hc1]. {
  specialize (rngl_characteristic_1 Hos Hc1) as H1.
  intros.
  rewrite (H1 (_ * _))%L.
  apply H1.
}
intros * Ht21 Hzs1 Hzs2.
apply rngl_leb_le in Hzs1, Hzs2.
assert (H2r : √2 ≠ 0%L). {
  intros H.
  apply (f_equal rngl_squ) in H.
  rewrite rngl_squ_sqrt in H. 2: {
    apply (rngl_0_le_2 Hos Hto).
  }
  rewrite (rngl_squ_0 Hos) in H.
  now apply (rngl_2_neq_0 Hos Hc1 Hto) in H.
}
rewrite (rl_sqrt_div Hop Hiv Hto); cycle 1. {
  apply (rngl_le_0_sub Hop Hor).
  apply rngl_cos_bound.
} {
  apply (rngl_0_lt_2 Hos Hc1 Hto).
}
rewrite (rl_sqrt_div Hop Hiv Hto); cycle 1. {
  apply (rngl_le_opp_l Hop Hor).
  apply rngl_cos_bound.
} {
  apply (rngl_0_lt_2 Hos Hc1 Hto).
}
rewrite (rl_sqrt_div Hop Hiv Hto); cycle 1. {
  apply (rngl_le_opp_l Hop Hor).
  apply rngl_cos_bound.
} {
  apply (rngl_0_lt_2 Hos Hc1 Hto).
}
rewrite (rl_sqrt_div Hop Hiv Hto); cycle 1. {
  apply (rngl_le_0_sub Hop Hor).
  apply rngl_cos_bound.
} {
  apply (rngl_0_lt_2 Hos Hc1 Hto).
}
do 2 rewrite (rngl_div_mul_mul_div Hic Hiv).
do 2 rewrite (rngl_mul_div_assoc Hiv).
rewrite (rngl_div_div Hos Hiv); [ | easy | easy ].
rewrite (rngl_div_div Hos Hiv); [ | easy | easy ].
rewrite fold_rngl_squ.
rewrite rngl_squ_sqrt. 2: {
  apply (rngl_0_le_2 Hos Hto).
}
rewrite (rngl_mul_sub_distr_l Hop).
do 2 rewrite (rngl_mul_comm Hic 2).
rewrite (rngl_div_mul Hiv). 2: {
  apply (rngl_2_neq_0 Hos Hc1 Hto).
}
rewrite (rngl_div_mul Hiv). 2: {
  apply (rngl_2_neq_0 Hos Hc1 Hto).
}
rewrite <- rl_sqrt_mul; cycle 1. {
  apply (rngl_le_0_sub Hop Hor).
  apply rngl_cos_bound.
} {
  apply (rngl_le_opp_l Hop Hor).
  apply rngl_cos_bound.
}
rewrite <- rl_sqrt_mul; cycle 1. {
  apply (rngl_le_opp_l Hop Hor).
  apply rngl_cos_bound.
} {
  apply (rngl_le_0_sub Hop Hor).
  apply rngl_cos_bound.
}
change_angle_add_r α1 π.
rewrite rngl_cos_sub_straight_r.
rewrite (rngl_sub_opp_r Hop).
rewrite (rngl_add_opp_r Hop).
rewrite angle_eucl_dist_is_sqrt.
rewrite angle_sub_sub_distr.
rewrite rngl_cos_add_straight_r.
rewrite (rngl_sub_opp_r Hop).
rewrite (rngl_mul_comm Hic).
progress unfold angle_sub.
apply rngl_leb_le in Hzs1, Hzs2.
rewrite rngl_sin_nonneg_sin_nonneg_add_1_cos_add_sub. 2: {
  rewrite rngl_sin_sub_straight_r in Hzs1.
  apply rngl_leb_le in Hzs1, Hzs2.
  cbn.
  congruence.
}
rewrite (rl_sqrt_squ Hop Hto).
cbn.
rewrite (rngl_mul_comm Hic).
rewrite (rngl_mul_comm Hic (_ - _)).
apply (rngl_abs_nonneg_eq Hop Hor).
apply (rngl_le_0_sub Hop Hor).
progress unfold angle_leb in Ht21.
apply rngl_leb_le in Hzs1, Hzs2.
rewrite Hzs1, Hzs2 in Ht21.
rewrite rngl_cos_sub_straight_r in Ht21.
apply rngl_leb_le in Ht21.
rewrite (rngl_mul_comm Hic).
apply (rl_sqrt_le_rl_sqrt Hop Hiq Hto). {
  apply (rngl_mul_nonneg_nonneg Hos Hor).
  apply (rngl_le_0_sub Hop Hor), rngl_cos_bound.
  apply (rngl_le_0_sub Hop Hor), rngl_cos_bound.
}
apply (rngl_mul_le_compat_nonneg Hor). {
  split. {
    apply (rngl_le_0_sub Hop Hor), rngl_cos_bound.
  }
  rewrite <- (rngl_add_opp_r Hop).
  apply (rngl_add_le_mono_l Hos Hor).
  apply (rngl_opp_le_compat Hop Hor).
  now rewrite (rngl_opp_involutive Hop).
} {
  split. {
    apply (rngl_le_0_sub Hop Hor), rngl_cos_bound.
  }
  rewrite <- (rngl_add_opp_r Hop).
  now apply (rngl_add_le_mono_l Hos Hor).
}
Qed.

Theorem angle_eucl_dist_2_mul_sqrt_add_sqrt :
  ∀ α1 α2,
  (rngl_sin α1 < 0)%L
  → (0 ≤ rngl_sin α2)%L
  → angle_eucl_dist α1 α2 =
    (2 *
     (√((1 - rngl_cos α1) / 2) * √((1 + rngl_cos α2) / 2) +
      √((1 + rngl_cos α1) / 2) * √((1 - rngl_cos α2) / 2)))%L.
Proof.
destruct_ac.
destruct (Nat.eq_dec (rngl_characteristic T) 1) as [Hc1| Hc1]. {
  specialize (rngl_characteristic_1 Hos Hc1) as H1.
  intros.
  rewrite (H1 (_ * _))%L.
  apply H1.
}
intros * Hs1z Hzs2.
apply (rngl_leb_gt_iff Hto) in Hs1z.
apply rngl_leb_le in Hzs2.
assert (H2r : √2 ≠ 0%L). {
  intros H.
  apply (f_equal rngl_squ) in H.
  rewrite rngl_squ_sqrt in H. 2: {
    apply (rngl_0_le_2 Hos Hto).
  }
  rewrite (rngl_squ_0 Hos) in H.
  now apply (rngl_2_neq_0 Hos Hc1 Hto) in H.
}
rewrite (rl_sqrt_div Hop Hiv Hto); cycle 1. {
  apply (rngl_le_0_sub Hop Hor).
  apply rngl_cos_bound.
} {
  apply (rngl_0_lt_2 Hos Hc1 Hto).
}
rewrite (rl_sqrt_div Hop Hiv Hto); cycle 1. {
  apply (rngl_le_opp_l Hop Hor).
  apply rngl_cos_bound.
} {
  apply (rngl_0_lt_2 Hos Hc1 Hto).
}
rewrite (rl_sqrt_div Hop Hiv Hto); cycle 1. {
  apply (rngl_le_opp_l Hop Hor).
  apply rngl_cos_bound.
} {
  apply (rngl_0_lt_2 Hos Hc1 Hto).
}
rewrite (rl_sqrt_div Hop Hiv Hto); cycle 1. {
  apply (rngl_le_0_sub Hop Hor).
  apply rngl_cos_bound.
} {
  apply (rngl_0_lt_2 Hos Hc1 Hto).
}
do 2 rewrite (rngl_div_mul_mul_div Hic Hiv).
do 2 rewrite (rngl_mul_div_assoc Hiv).
rewrite (rngl_div_div Hos Hiv); [ | easy | easy ].
rewrite (rngl_div_div Hos Hiv); [ | easy | easy ].
rewrite fold_rngl_squ.
rewrite rngl_squ_sqrt. 2: {
  apply (rngl_0_le_2 Hos Hto).
}
rewrite rngl_mul_add_distr_l.
do 2 rewrite (rngl_mul_comm Hic 2).
rewrite (rngl_div_mul Hiv). 2: {
  apply (rngl_2_neq_0 Hos Hc1 Hto).
}
rewrite (rngl_div_mul Hiv). 2: {
  apply (rngl_2_neq_0 Hos Hc1 Hto).
}
rewrite <- rl_sqrt_mul; cycle 1. {
  apply (rngl_le_0_sub Hop Hor).
  apply rngl_cos_bound.
} {
  apply (rngl_le_opp_l Hop Hor).
  apply rngl_cos_bound.
}
rewrite <- rl_sqrt_mul; cycle 1. {
  apply (rngl_le_opp_l Hop Hor).
  apply rngl_cos_bound.
} {
  apply (rngl_le_0_sub Hop Hor).
  apply rngl_cos_bound.
}
change_angle_add_r α1 π.
rewrite rngl_cos_sub_straight_r.
rewrite (rngl_sub_opp_r Hop).
rewrite (rngl_add_opp_r Hop).
rewrite angle_eucl_dist_is_sqrt.
rewrite angle_sub_sub_distr.
rewrite rngl_cos_add_straight_r.
rewrite (rngl_sub_opp_r Hop).
rewrite (rngl_mul_comm Hic).
rewrite rngl_sin_nonneg_sin_nonneg_add_1_cos_add_add. 2: {
  rewrite rngl_sin_sub_straight_r in Hs1z.
  rewrite (rngl_leb_0_opp Hop Hto) in Hs1z.
  apply (rngl_leb_gt_iff Hto) in Hs1z.
  apply rngl_lt_le_incl in Hs1z.
  apply rngl_leb_le in Hs1z.
  congruence.
}
rewrite (rl_sqrt_squ Hop Hto).
rewrite (rngl_mul_comm Hic).
rewrite (rngl_mul_comm Hic (_ - _)).
apply (rngl_abs_nonneg_eq Hop Hor).
apply (rngl_le_0_add Hos Hor).
apply rl_sqrt_nonneg.
apply (rngl_mul_nonneg_nonneg Hos Hor).
apply (rngl_le_opp_l Hop Hor), rngl_cos_bound.
apply (rngl_le_opp_l Hop Hor), rngl_cos_bound.
apply rl_sqrt_nonneg.
apply (rngl_mul_nonneg_nonneg Hos Hor).
apply (rngl_le_0_sub Hop Hor), rngl_cos_bound.
apply (rngl_le_0_sub Hop Hor), rngl_cos_bound.
Qed.

Theorem le_angle_eucl_dist_eq_2_mul_sin_sub_div_2 :
  ∀ α1 α2,
  (α2 ≤ α1)%A
  → angle_eucl_dist α1 α2 = (2 * rngl_sin (α1 /₂ - α2 /₂))%L.
Proof.
destruct_ac.
intros * Ht21.
rewrite rngl_sin_sub.
cbn.
progress unfold rngl_signp.
remember (rngl_cos α1) as c1 eqn:Hco1.
remember (rngl_cos α2) as c2 eqn:Hco2.
remember (rngl_sin α1) as s1 eqn:Hsi1.
remember (rngl_sin α2) as s2 eqn:Hsi2.
move c2 before c1; move s1 before c2; move s2 before s1.
remember (0 ≤? s1)%L as zs1 eqn:Hzs1.
remember (0 ≤? s2)%L as zs2 eqn:Hzs2.
symmetry in Hzs1, Hzs2.
subst c1 c2 s1 s2.
destruct zs1. {
  rewrite rngl_mul_1_l.
  destruct zs2. {
    rewrite rngl_mul_1_l.
    apply rngl_leb_le in Hzs1, Hzs2.
    now apply angle_eucl_dist_2_mul_sqrt_sub_sqrt.
  }
  exfalso.
  progress unfold angle_leb in Ht21.
  now rewrite Hzs1, Hzs2 in Ht21.
} {
  destruct zs2. {
    do 2 rewrite (rngl_mul_opp_l Hop).
    do 2 rewrite rngl_mul_1_l.
    rewrite (rngl_sub_opp_r Hop).
    apply (rngl_leb_gt_iff Hto) in Hzs1.
    apply rngl_leb_le in Hzs2.
    now apply angle_eucl_dist_2_mul_sqrt_add_sqrt.
  }
  apply (rngl_leb_gt_iff Hto) in Hzs1, Hzs2.
  change_angle_add_r α1 π.
  change_angle_add_r α2 π.
  progress sin_cos_add_sub_straight_hyp T Hzs1.
  progress sin_cos_add_sub_straight_hyp T Hzs2.
  progress sin_cos_add_sub_straight_goal T.
  rewrite angle_eucl_dist_move_0_r.
  rewrite angle_sub_sub_distr.
  rewrite angle_sub_sub_swap.
  rewrite angle_sub_add.
  rewrite <- angle_eucl_dist_move_0_r.
  do 2 rewrite (rngl_sub_opp_r Hop).
  do 3 rewrite (rngl_mul_opp_l Hop).
  do 2 rewrite rngl_mul_1_l.
  rewrite (rngl_mul_opp_r Hop).
  rewrite (rngl_sub_opp_r Hop).
  rewrite (rngl_add_opp_l Hop).
  generalize Hzs1; intros H1.
  generalize Hzs2; intros H2.
  apply rngl_lt_le_incl in H1, H2.
  apply angle_eucl_dist_2_mul_sqrt_sub_sqrt; [ | easy | easy ].
  (* lemma *)
  progress unfold angle_leb in Ht21.
  do 2 rewrite rngl_sin_sub_straight_r in Ht21.
  do 2 rewrite rngl_cos_sub_straight_r in Ht21.
  progress unfold angle_leb.
  apply rngl_leb_le in H1, H2.
  rewrite H1, H2.
  apply (rngl_opp_neg_pos Hop Hor) in Hzs1, Hzs2.
  apply (rngl_leb_gt_iff Hto) in Hzs1, Hzs2.
  rewrite Hzs1, Hzs2 in Ht21.
  apply rngl_leb_le in Ht21.
  apply rngl_leb_le.
  now apply (rngl_opp_le_compat Hop Hor) in Ht21.
}
Qed.

Theorem angle_eucl_dist_is_2_mul_sin_sub_div_2 :
  ∀ α1 α2,
  angle_eucl_dist α1 α2 = (2 * rngl_sin ((α1 - α2) /₂))%L.
Proof.
destruct_ac.
intros.
rewrite angle_div_2_sub.
remember (α2 ≤? α1)%A as t21 eqn:Ht21.
symmetry in Ht21.
destruct t21. {
  now apply le_angle_eucl_dist_eq_2_mul_sin_sub_div_2.
} {
  rewrite rngl_sin_add_straight_r.
  rewrite rngl_sin_sub_anticomm.
  rewrite (rngl_opp_involutive Hop).
  rewrite angle_eucl_dist_symmetry.
  apply angle_leb_gt in Ht21.
  apply angle_lt_le_incl in Ht21.
  now apply le_angle_eucl_dist_eq_2_mul_sin_sub_div_2.
}
Qed.

Theorem angle_eucl_dist_eq_angle_eucl_dist :
  ∀ α1 α2 α3 α4,
  angle_eucl_dist α1 α2 = angle_eucl_dist α3 α4 ↔
  (α1 + α4 = α2 + α3 ∨ α1 + α3 = α2 + α4)%A.
Proof.
destruct_ac.
destruct (Nat.eq_dec (rngl_characteristic T) 1) as [Hc1| Hc1]. {
  specialize (rngl_characteristic_1_angle_0 Hc1) as H1.
  intros.
  rewrite angle_eucl_dist_move_0_r.
  rewrite (angle_eucl_dist_move_0_r α3).
  rewrite (H1 (α1 - α2))%A.
  rewrite (H1 (α3 - α4))%A.
  rewrite (H1 (α1 + α4))%A.
  rewrite (H1 (α2 + α3))%A.
  rewrite (H1 (α1 + α3))%A.
  rewrite (H1 (α2 + α4))%A.
  rewrite angle_eucl_dist_diag.
  split; intros; [ now left | easy ].
}
intros.
split; intros H12. {
  do 2 rewrite angle_eucl_dist_is_2_mul_sin_sub_div_2 in H12.
  apply (f_equal (rngl_mul 2⁻¹)) in H12.
  do 2 rewrite rngl_mul_assoc in H12.
  rewrite (rngl_mul_inv_diag_l Hiv) in H12. 2: {
    apply (rngl_2_neq_0 Hos Hc1 Hto).
  }
  do 2 rewrite rngl_mul_1_l in H12.
  apply rngl_sin_eq in H12.
  destruct H12 as [H12| H12]. {
    left.
    apply (f_equal (λ a, angle_mul_nat a 2)) in H12.
    do 2 rewrite angle_div_2_mul_2 in H12.
    apply -> angle_sub_move_r in H12.
    rewrite H12.
    rewrite angle_add_add_swap.
    rewrite angle_sub_add.
    apply angle_add_comm.
  }
  right.
  apply (f_equal (λ a, angle_mul_nat a 2)) in H12.
  rewrite angle_mul_sub_distr_l in H12.
  (* lemma *)
  rewrite (angle_mul_2_l π) in H12.
  rewrite angle_straight_add_straight in H12.
  rewrite angle_sub_0_l in H12.
  do 2 rewrite angle_div_2_mul_2 in H12.
  rewrite angle_opp_sub_distr in H12.
  apply -> angle_sub_move_r in H12.
  rewrite H12.
  rewrite angle_add_add_swap.
  rewrite angle_sub_add.
  apply angle_add_comm.
}
rewrite angle_eucl_dist_move_0_r.
rewrite (angle_eucl_dist_move_0_r α3).
destruct H12 as [H12| H12]. {
  apply angle_add_move_r in H12.
  subst α1.
  rewrite angle_sub_sub_swap.
  rewrite angle_add_sub_swap.
  rewrite angle_sub_diag.
  now rewrite angle_add_0_l.
}
apply angle_add_move_r in H12.
subst α1.
rewrite angle_sub_sub_swap.
rewrite angle_add_sub_swap.
rewrite angle_sub_diag.
rewrite angle_add_0_l.
rewrite <- angle_eucl_dist_opp_opp.
rewrite angle_opp_sub_distr.
now rewrite angle_opp_0.
Qed.

Theorem rngl_cos_le_iff_angle_eucl_le :
  ∀ α1 α2 α3 α4,
  (rngl_cos (α1 - α2) ≤ rngl_cos (α3 - α4)
   ↔ angle_eucl_dist α3 α4 ≤ angle_eucl_dist α1 α2)%L.
Proof.
destruct_ac.
destruct (Nat.eq_dec (rngl_characteristic T) 1) as [Hc1| Hc1]. {
  specialize (rngl_characteristic_1 Hos Hc1) as H1.
  intros.
  do 2 rewrite (H1 (angle_eucl_dist _ _)).
  do 2 rewrite (H1 (rngl_cos _)).
  easy.
}
intros.
rewrite <- (rngl_abs_nonneg_eq Hop Hor (angle_eucl_dist _ _)). 2: {
  apply (dist_nonneg Hop Hiv Hto angle_eucl_dist_is_dist).
}
rewrite <- (rngl_abs_nonneg_eq Hop Hor (angle_eucl_dist α1 _)). 2: {
  apply (dist_nonneg Hop Hiv Hto angle_eucl_dist_is_dist).
}
rewrite angle_eucl_dist_move_0_r.
rewrite (angle_eucl_dist_move_0_r α1).
do 2 rewrite rngl_cos_angle_eucl_dist_0_r.
split; intros H1. {
  apply (rngl_sub_le_mono_l Hop Hor) in H1.
  apply (rngl_div_le_mono_pos_r Hop Hiv Hto) in H1. 2: {
    apply (rngl_0_lt_2 Hos Hc1 Hto).
  }
  now apply (rngl_squ_le_abs_le Hop Hiq Hto) in H1.
} {
  apply (rngl_sub_le_mono_l Hop Hor).
  apply (rngl_div_le_mono_pos_r Hop Hiv Hto). {
    apply (rngl_0_lt_2 Hos Hc1 Hto).
  }
  now apply (rngl_abs_le_squ_le Hop Hto).
}
Qed.

Theorem rngl_cos_lt_iff_angle_eucl_lt :
  ∀ α1 α2 α3 α4,
  (rngl_cos (α1 - α2) < rngl_cos (α3 - α4)
   ↔ angle_eucl_dist α3 α4 < angle_eucl_dist α1 α2)%L.
Proof.
destruct_ac.
intros.
split; intros Htt. {
  apply rngl_le_neq.
  split. {
    apply rngl_lt_le_incl in Htt.
    now apply rngl_cos_le_iff_angle_eucl_le.
  }
  intros H.
  rewrite angle_eucl_dist_move_0_r in H.
  rewrite (angle_eucl_dist_move_0_r α1) in H.
  apply angle_eucl_dist_eq_angle_eucl_dist in H.
  do 2 rewrite angle_add_0_l in H.
  rewrite angle_add_0_r in H.
  destruct H as [H| H]. {
    rewrite H in Htt.
    now apply rngl_lt_irrefl in Htt.
  }
  apply angle_add_move_0_r in H.
  rewrite H in Htt.
  now apply rngl_lt_irrefl in Htt.
} {
  apply rngl_le_neq.
  split. {
    apply rngl_lt_le_incl in Htt.
    now apply rngl_cos_le_iff_angle_eucl_le.
  }
  intros H.
  rewrite angle_eucl_dist_move_0_r in Htt.
  rewrite (angle_eucl_dist_move_0_r α1) in Htt.
  apply rngl_cos_eq in H.
  destruct H; rewrite H in Htt. {
    now apply rngl_lt_irrefl in Htt.
  }
  rewrite <- angle_eucl_dist_opp_opp in Htt.
  rewrite angle_opp_0 in Htt.
  now apply rngl_lt_irrefl in Htt.
}
Qed.

Theorem angle_le_angle_eucl_dist_le :
  ∀ α1 α2,
  (α1 ≤ π)%A
  → (α2 ≤ π)%A
  → (α1 ≤ α2)%A ↔ (angle_eucl_dist α1 0 ≤ angle_eucl_dist α2 0)%L.
Proof.
intros * Ht1 Ht2.
progress unfold angle_leb.
apply rngl_sin_nonneg_angle_le_straight in Ht1, Ht2.
apply rngl_leb_le in Ht1, Ht2.
rewrite Ht1, Ht2.
split; intros H12. {
  apply rngl_leb_le in H12.
  apply rngl_cos_le_iff_angle_eucl_le.
  now do 2 rewrite angle_sub_0_r.
} {
  apply rngl_leb_le.
  apply rngl_cos_le_iff_angle_eucl_le in H12.
  now do 2 rewrite angle_sub_0_r in H12.
}
Qed.

Theorem fold_angle_div_nat :
  ∀ n α α',
  is_limit_when_seq_tends_to_inf angle_eucl_dist
    (seq_angle_to_div_nat n α) α' =
  angle_div_nat n α α'.
Proof. easy. Qed.

Theorem angle_mul_nat_div_2π_iff :
  ∀ n α k,
  angle_mul_nat_div_2π n α = k
  ↔ (∀ i, i < n → angle_mul_nat_div_2π i α ≤ k) ∧
    (if Nat.eq_dec n 0 then k = 0
     else if Nat.eq_dec k 0 then
       ∀ i, i < n → angle_add_overflow α (i * α) = false
     else
       ∃ i, i < n ∧ angle_mul_nat_div_2π i α = k - 1 ∧
       angle_add_overflow α (i * α) = true ∧
       ∀ j, i < j < n → angle_add_overflow α (j * α) = false).
Proof.
intros.
revert k.
induction n; intros; [ easy | ].
cbn - [ angle_mul_nat_div_2π ].
split; intros H1. {
  split. {
    intros i Hi.
    cbn in H1.
    remember (angle_add_overflow α (n * α)) as ov eqn:Hov.
    symmetry in Hov.
    destruct ov. {
      cbn in H1.
      apply Nat.add_sub_eq_r in H1.
      symmetry in H1.
      generalize H1; intros H2.
      apply IHn in H2.
      destruct H2 as (H2, _).
      destruct (Nat.eq_dec i n) as [Hin| Hin]. {
        subst i; rewrite H1; flia.
      }
      apply (Nat.le_trans _ (k - 1)); [ | flia ].
      apply H2.
      flia Hi Hin.
    }
    rewrite Nat.add_0_r in H1.
    generalize H1; intros H2.
    apply IHn in H2.
    destruct H2 as (H2, H3).
    destruct (Nat.eq_dec i n) as [Hin| Hin]. {
      subst i; rewrite H1; flia.
    }
    apply H2.
    flia Hi Hin.
  }
  cbn.
  destruct (Nat.eq_dec k 0) as [Hkz| Hkz]. {
    subst k.
    intros i Hi.
    cbn in Hkz.
    apply Nat.eq_add_0 in Hkz.
    destruct Hkz as (H1, H2).
    apply Nat_eq_b2n_0 in H2.
    generalize H1; intros H3.
    apply IHn in H3.
    cbn in H3.
    destruct H3 as (H3, H4).
    destruct (Nat.eq_dec n 0) as [Hnz| Hnz]. {
      subst n.
      apply Nat.lt_1_r in Hi; subst i; cbn.
      apply angle_add_overflow_0_r.
    }
    destruct (Nat.eq_dec i n) as [Hin| Hin]; [ now subst i | ].
    apply H4.
    flia Hi Hin.
  }
  cbn in H1.
  generalize H1; intros H2.
  apply Nat.add_sub_eq_r in H2.
  symmetry in H2.
  apply IHn in H2.
  destruct H2 as (H2, H3).
  destruct (Nat.eq_dec n 0) as [Hnz| Hnz]. {
    subst n.
    cbn in H3.
    now rewrite angle_add_overflow_0_r, Nat.sub_0_r in H3.
  }
  rewrite <- H1, Nat.add_sub in H3.
  destruct (Nat.eq_dec (angle_mul_nat_div_2π n α) 0) as [Hmz| Hmz]. {
    rewrite Hmz in H1.
    cbn in H1.
    destruct k; [ easy | clear Hkz ].
    destruct k. {
      apply Nat_eq_b2n_1 in H1.
      exists n.
      split; [ easy | ].
      split; [ easy | ].
      split; [ easy | ].
      intros j Hj; flia Hj.
    }
    now destruct (angle_add_overflow α (n * α)).
  }
  destruct H3 as (i & Hin & Haa & Hov & H3).
  remember (angle_add_overflow α (n * α)) as ov eqn:Hovn.
  symmetry in Hovn.
  destruct ov. {
    cbn in H1.
    exists n.
    split; [ easy | ].
    split; [ now rewrite <- H1, Nat.add_sub | ].
    split; [ easy | ].
    intros j Hj; flia Hj.
  }
  rewrite Nat.add_0_r in H1.
  exists i.
  split; [ flia Hin | ].
  split; [ now rewrite Haa; f_equal | ].
  split; [ easy | ].
  intros j Hj.
  destruct (Nat.eq_dec j n) as [Hjn| Hjn]; [ now subst j | ].
  apply H3.
  flia Hj Hjn.
}
destruct H1 as (H1, H2).
cbn.
remember (angle_add_overflow α (n * α)) as ov eqn:Hovn.
symmetry in Hovn.
destruct ov. {
  cbn.
  destruct (Nat.eq_dec k 0) as [Hkz| Hkz]; [ now rewrite H2 in Hovn | ].
  destruct H2 as (i & Hin & H2 & H3 & H4).
  destruct (Nat.eq_dec i n) as [Hien| Hien]. {
    subst i.
    clear H4 Hin.
    rewrite H2.
    now apply Nat.sub_add, Nat.neq_0_lt_0.
  }
  rewrite H4 in Hovn; [ easy | ].
  flia Hin Hien.
}
rewrite Nat.add_0_r.
destruct (Nat.eq_dec k 0) as [Hkz| Hkz]. {
  subst k.
  specialize (H1 _ (Nat.lt_succ_diag_r _)).
  now apply Nat.le_0_r in H1.
}
destruct H2 as (i & Hin & H2 & H3 & H4).
destruct (Nat.eq_dec i n) as [Hien| Hien]. {
  subst i.
  now rewrite H3 in Hovn.
}
apply IHn.
split. {
  intros j Hj.
  apply H1; flia Hj.
}
destruct (Nat.eq_dec n 0) as [Hnz| Hnz]. {
  subst n.
  now apply Nat.lt_1_r in Hin.
}
destruct (Nat.eq_dec k 0) as [Hkez| Hkez]; [ easy | ].
clear Hkez.
exists i.
split; [ flia Hin Hien | ].
split; [ easy | ].
split; [ easy | ].
intros j Hj.
apply H4.
split; [ easy | ].
flia Hj.
Qed.

Theorem angle_div_nat_prop :
  rngl_characteristic T = 0 →
  rngl_is_archimedean T = true →
  is_complete T rngl_dist →
  ∀ α n α',
  angle_div_nat α n α'
  → (n = 0 ∧ α' = 0%A) ∨ (n * α')%A = α.
Proof.
destruct_ac.
intros Hcz Har Hco.
intros * Hdn.
destruct (Nat.eq_dec n 0) as [Hnz| Hnz]. {
  left; split; [ easy | subst n ].
  progress unfold angle_div_nat in Hdn.
  progress unfold seq_angle_to_div_nat in Hdn.
  cbn in Hdn.
  now apply angle_lim_const in Hdn.
}
right.
destruct (Nat.eq_dec n 1) as [Hn1| Hn1]. {
  subst n; rewrite angle_mul_1_l.
  progress unfold angle_div_nat in Hdn.
  progress unfold seq_angle_to_div_nat in Hdn.
  eapply (angle_lim_eq_compat 0 0) in Hdn. 2: {
    intros i.
    rewrite Nat.add_0_r.
    rewrite Nat.div_1_r.
    rewrite angle_div_2_pow_mul_2_pow.
    easy.
  }
  now apply angle_lim_const in Hdn.
}
progress unfold angle_div_nat in Hdn.
rename Hdn into Hlim.
specialize (angle_lim_mul n _ _ Hlim) as H1.
enough (H2 : angle_lim (λ i, (n * seq_angle_to_div_nat α n i)%A) α). {
  specialize (limit_unique Hop Hiv Hto angle_eucl_dist_is_dist) as H3.
  now apply (H3 _ (n * α')%A) in H2.
}
clear α' Hlim H1.
destruct (angle_eq_dec α 0) as [Htz| Htz]. {
  subst α.
  eapply (angle_lim_eq_compat 0 0). {
    intros i.
    rewrite Nat.add_0_r; symmetry.
    progress unfold seq_angle_to_div_nat.
    rewrite angle_0_div_2_pow.
    do 2 rewrite angle_mul_0_r.
    easy.
  }
  intros ε Hε.
  exists 0.
  intros m _.
  cbn.
  now rewrite angle_eucl_dist_diag.
}
destruct (Nat.eq_dec (rngl_characteristic T) 1) as [Hc1| Hc1]. {
  specialize (rngl_characteristic_1 Hos Hc1) as H2.
  intros ε Hε.
  rewrite (H2 ε) in Hε.
  now apply rngl_lt_irrefl in Hε.
}
move Hc1 before Hcz.
move Hii before Hco.
progress unfold seq_angle_to_div_nat.
destruct (Nat.eq_dec n 0) as [H| H]; [ easy | clear H ].
eapply (angle_lim_eq_compat 0 0). {
  intros i.
  rewrite Nat.add_0_r; symmetry.
  rewrite angle_mul_nat_assoc.
  specialize (Nat.div_mod (2 ^ i) n Hnz) as H1.
  symmetry in H1.
  apply Nat.add_sub_eq_r in H1.
  rewrite <- H1.
  rewrite angle_mul_sub_distr_r; [ | now apply Nat.Div0.mod_le ].
  rewrite angle_div_2_pow_mul_2_pow.
  easy.
}
apply angle_lim_move_0_r.
eapply (angle_lim_eq_compat 0 0). {
  intros i.
  rewrite Nat.add_0_r; symmetry.
  rewrite angle_sub_sub_swap.
  rewrite angle_sub_diag.
  rewrite angle_sub_0_l.
  easy.
}
rewrite <- angle_opp_0.
apply angle_lim_opp.
enough (H : angle_lim (λ i, (n * (α /₂^i))%A) 0). {
  intros ε Hε.
  specialize (H ε Hε).
  destruct H as (N, HN).
  exists (Nat.max N (Nat.log2_up (2 * n))).
  intros m Hm.
  specialize (HN m).
  assert (H : N ≤ m). {
    eapply Nat.le_trans; [ | apply Hm ].
    apply Nat.le_max_l.
  }
  specialize (HN H); clear H.
  eapply (rngl_le_lt_trans Hor); [ | apply HN ].
  assert (Hnm : Nat.log2_up (2 * n) ≤ m). {
    eapply Nat.le_trans; [ | apply Hm ].
    apply Nat.le_max_r.
  }
  apply (Nat.pow_le_mono_r 2) in Hnm; [ | easy ].
  apply angle_le_angle_eucl_dist_le. {
    eapply angle_le_trans. {
      apply angle_mul_le_mono_r. 2: {
        apply Nat.lt_le_incl.
        apply Nat.mod_upper_bound.
        apply Hnz.
      }
      apply angle_mul_nat_div_2π_div_pow2.
      eapply Nat.le_trans; [ | apply Hnm ].
      apply (Nat.le_trans _ (2 * n)). {
        flia Hnz Hn1.
      }
      apply Nat.log2_log2_up_spec.
      apply Nat.neq_0_lt_0.
      flia Hnz Hn1.
    }
    apply angle_mul_div_pow2_le_straight.
    eapply Nat.le_trans; [ | apply Hnm ].
    apply Nat.log2_log2_up_spec.
    apply Nat.neq_0_lt_0.
    flia Hnz Hn1.
  } {
    apply angle_mul_div_pow2_le_straight.
    eapply Nat.le_trans; [ | apply Hnm ].
    apply Nat.log2_log2_up_spec.
    apply Nat.neq_0_lt_0.
    flia Hnz Hn1.
  }
  apply angle_mul_le_mono_r. 2: {
    apply Nat.lt_le_incl.
    now apply Nat.mod_upper_bound.
  }
  apply angle_mul_nat_div_2π_div_pow2.
  eapply Nat.le_trans; [ | apply Hnm ].
  apply (Nat.le_trans _ (2 * n)). {
    flia Hnz Hn1.
  }
  apply Nat.log2_log2_up_spec.
  apply Nat.neq_0_lt_0.
  flia Hnz Hn1.
}
rewrite <- (angle_mul_0_r n).
apply angle_lim_mul.
(* lemma : angle_lim (angle_div_2_pow α) 0 *)
intros ε Hε.
enough (H : ∃ N, ∀ m, N ≤ m → (1 - ε² / 2 < rngl_cos (α /₂^m))%L). {
  destruct H as (N, HN).
  exists N.
  intros m Hm.
  specialize (HN m Hm).
  apply rngl_cos_lt_angle_eucl_dist_lt. {
    now apply rngl_lt_le_incl in Hε.
  }
  now rewrite angle_sub_0_l.
}
now apply (exists_nat_such_that_rngl_cos_close_to_1 Har).
Qed.

Theorem angle_add_not_overflow_iff :
  ∀ α1 α2,
  angle_add_overflow α1 α2 = false
  ↔ (α1 = 0)%A ∨ (α2 < - α1)%A.
Proof.
intros.
progress unfold angle_add_overflow.
split; intros Htt. {
  apply Bool.andb_false_iff in Htt.
  destruct Htt as [Ht| Htt]; [ left | right ]. {
    apply Bool.negb_false_iff in Ht.
    now apply angle_eqb_eq in Ht.
  } {
    now apply angle_leb_gt in Htt.
  }
} {
  apply Bool.andb_false_iff.
  destruct Htt as [Ht| Htt]; [ left | right ]. {
    now subst α1; rewrite angle_eqb_refl.
  } {
    now apply angle_leb_gt.
  }
}
Qed.

(* to be completed later
Theorem glop :
  rngl_characteristic T = 0 →
  rngl_is_archimedean T = true →
  is_complete T rngl_dist →
  ∀ n i α α',
  i < n
  → angle_div_nat α n α'
  → angle_add_overflow α' (i * α') = false.
Proof.
intros Hch Har Hco * Hin Hdn.
rewrite <- angle_add_overflow_equiv2.
progress unfold angle_add_overflow2.
apply Bool.not_true_iff_false.
apply angle_nlt_ge.
rewrite <- (angle_mul_1_l α') at 2.
rewrite <- angle_mul_add_distr_r.
rewrite Nat.add_1_l.
remember (S i) as j.
assert (0 < j ≤ n) by flia Hin Heqj.
clear i Hin Heqj; rename j into i; rename H into Hin.
move i before n; move Hin after Hdn.
enough
  (H :
   ∀ j α'',
   α'' = seq_angle_to_div_nat α n j
   → (α'' ≤ i * α'')%A). {
...
intros Hch Har Hco * Hin Hdn.
progress unfold angle_div_nat in Hdn.
progress unfold angle_lim in Hdn.
progress unfold is_limit_when_seq_tends_to_inf in Hdn.
remember (∀ ε, _ → ∃ N, ∀ j, _) as x eqn:Hx; subst x.
assert
  (H :
   ∀ ε : T, (0 < ε)%L →
   ∃ N : nat, ∀ j : nat, N ≤ j →
   (1 - ε² / 2 < rngl_cos (α' - seq_angle_to_div_nat α n j))%L). {
  intros ε Hε.
  specialize (Hdn ε Hε).
  destruct Hdn as (N, HN).
  exists N.
  intros j Hj.
  generalize Hε; intros Hε'; apply rngl_lt_le_incl in Hε'.
  specialize (HN j Hj).
  now apply rngl_cos_lt_angle_eucl_dist_lt in HN.
}
clear Hdn; rename H into Hdn.
rewrite <- angle_add_overflow_equiv2.
progress unfold angle_add_overflow2.
apply Bool.not_true_iff_false.
apply angle_nlt_ge.
rewrite <- (angle_mul_1_l α') at 2.
rewrite <- angle_mul_add_distr_r.
rewrite Nat.add_1_l.
remember (S i) as j.
assert (0 < j ≤ n) by flia Hin Heqj.
clear i Hin Heqj; rename j into i; rename H into Hin.
move i before n; move Hin after Hdn.
progress unfold angle_leb.
remember (0 ≤? rngl_sin α')%L as zs eqn:Hzs.
remember (0 ≤? rngl_sin (i * α'))%L as zsi eqn:Hzsi.
symmetry in Hzs, Hzsi.
destruct zs. {
  destruct zsi; [ | easy ].
  apply rngl_leb_le in Hzs, Hzsi.
  apply rngl_leb_le.
  apply rngl_sin_sub_nonneg_iff; [ | easy | ].
  apply rngl_le_neq.
  split; [ easy | ].
  symmetry; intros H.
  apply eq_rngl_sin_0 in H.
  destruct H as [H| H]. {
Search (_ * _ = 0)%A.
...
Search (_ - _² / 2)%L.
About exists_nat_such_that_rngl_cos_close_to_1.
...
eapply (is_limit_when_seq_tends_to_inf_eq_compat _ _ 0 0) in Hdn. 2: {
  intros j; rewrite Nat.add_0_r.

progress unfold is_limit_when_seq_tends_to_inf in Hdn.
eapply (angle_lim_eq_compat 0 0) in Hdn. 2: {
  intros j; rewrite Nat.add_0_r.
  progress unfold seq_angle_to_div_nat in Hdn.
  progress unfold angle_lim in Hdn.
Search angle_div_nat_eq_compat.
progress unfold is_limit_when_seq_tends_to_inf in Hdn.
remember (∀ ε, _ → ∃ N, ∀ j, _) as x eqn:Hx; subst x.
...
rngl_cos_lt_angle_eucl_dist_lt:
  ∀ {T : Type} {ro : ring_like_op T} {rp : ring_like_prop T} {rl : real_like_prop T} 
    {ac : angle_ctx T} (a : T) (α1 α2 : angle T),
    (0 ≤ a)%L → (1 - a² / 2 < rngl_cos (α2 - α1))%L ↔ (angle_eucl_dist α1 α2 < a)%L
...

Theorem angle_div_nat_add_not_overflow :
  ∀ n i α,
  i < n
  → angle_div_nat (n * α) n α
  → angle_add_overflow α (i * α) = false.
Proof.
intros * Hin Hdn.
... ...
now apply (glop n _ (n * α)).
...
intros * Hin Hdn.
apply angle_add_not_overflow_iff.
destruct (angle_eq_dec α 0) as [Htz| Htz]; [ now left | right ].
progress unfold angle_div_nat in Hdn.
progress unfold angle_lim in Hdn.
progress unfold is_limit_when_seq_tends_to_inf in Hdn.
remember (∀ ε, _ → ∃ N, ∀ j, _) as x eqn:Hx; subst x.
Print seq_angle_to_div_nat.
Print angle_eucl_dist.
progress unfold angle_eucl_dist in Hdn.
Search (rngl_cos (seq_angle_to_div_nat _ _ _)).
progress unfold seq_angle_to_div_nat in Hdn.
Search (rngl_cos (_ * _)).
Search (rngl_cos _ - rngl_cos _)%L.
Search (rngl_cos _ + rngl_cos _ = _)%L.
...
progress unfold rl_modl in Hdn.
...
Theorem glop :
  ∀ n i α,
  angle_eucl_dist (seq_angle_to_div_nat α n i) α =
...

Theorem angle_div_nat_prop' :
  rngl_characteristic T = 0 →
  rngl_is_archimedean T = true →
  is_complete T rngl_dist →
  ∀ α n α',
  angle_div_nat α n α'
  → (n = 0 ∧ α' = 0%A) ∨ (n * α')%A = α ∧ angle_mul_nat_div_2π n α' = 0.
Proof.
intros Hch Har Hco.
intros * Hdn.
specialize (angle_div_nat_prop Hch Har Hco α n α' Hdn) as H1.
destruct H1 as [H1| H1]; [ now left | right ].
split; [ easy | ].
subst α; rename α' into α.
(* lemma *)
apply angle_mul_nat_div_2π_iff; cbn.
split. {
  intros i Hin.
  apply Nat.le_0_r.
  (* lemma *)
  apply angle_mul_nat_div_2π_iff.
  cbn.
  split. {
    intros j Hji.
    apply Nat.le_0_r.
    revert i Hji Hin.
    induction j; intros; [ easy | cbn ].
    destruct i; [ easy | ].
    apply Nat.succ_lt_mono in Hji.
    rewrite (IHj _ Hji); [ cbn | flia Hin ].
    apply Nat_eq_b2n_0.
... ...
    apply (angle_div_nat_add_not_overflow n); [ | easy ].
    flia Hji Hin.
  }
  destruct (Nat.eq_dec i 0) as [Hiz| Hiz]; [ easy | ].
  intros j Hji; clear Hiz.
  apply (angle_div_nat_add_not_overflow n); [ | easy ].
  now apply (Nat.lt_trans _ i).
}
destruct (Nat.eq_dec n 0) as [Hnz| Hnz]; [ easy | ].
intros i Hin.
now apply (angle_div_nat_add_not_overflow n).
Qed.
...
*)

Theorem exists_angle_div_nat :
  rngl_characteristic T = 0 →
  rngl_is_archimedean T = true →
  is_complete T rngl_dist →
  ∀ α n,
  n ≠ 0
  → ∃ α', (n * α')%A = α.
Proof.
destruct_ac.
intros Hcz Har Hco * Hnz.
specialize (seq_angle_to_div_nat_is_Cauchy Har n α) as H1.
specialize (rngl_is_complete_angle_is_complete Hco) as H2.
specialize (H2 _ H1).
destruct H2 as (α', Ht).
exists α'.
specialize (angle_div_nat_prop Hcz Har Hco _ _ _ Ht) as H2.
now destruct H2.
Qed.

Theorem angle_eq_mul_succ_nat_0_r :
  ∀ n α,
  angle_add_overflow α (n * α) = false
  → (S n * α)%A = 0%A
  → α = 0%A.
Proof.
intros * Hov Ht.
apply angle_add_overflow_if in Hov.
destruct Hov as [H1| H1]; [ easy | ].
cbn in Ht.
rewrite angle_add_comm in Ht.
apply angle_add_move_0_r in Ht.
rewrite Ht in H1.
now apply angle_lt_irrefl in H1.
Qed.

Theorem angle_mul_nat_integral :
  ∀ n α,
  angle_mul_nat_div_2π n α = 0
  → (n * α = 0)%A
  → n = 0 ∨ α = 0%A.
Proof.
intros * Hn Ht.
destruct n; [ now left | right ].
cbn in Hn.
apply Nat.eq_add_0 in Hn.
destruct Hn as (Hn, H1).
apply Nat_eq_b2n_0 in H1.
now apply (angle_eq_mul_succ_nat_0_r n).
Qed.

Theorem angle_le_le_sub_l :
  rngl_has_opp T = true →
  rngl_is_totally_ordered T = true →
  ∀ α1 α2, (α1 ≤ α2)%A → (α2 - α1 ≤ α2)%A.
Proof.
intros Hop Hto.
specialize (rngl_is_totally_ordered_is_ordered Hto) as Hor.
intros * H12.
progress unfold angle_leb in H12.
progress unfold angle_leb.
remember (0 ≤? rngl_sin α1)%L as s1 eqn:Hs1.
remember (0 ≤? rngl_sin α2)%L as s2 eqn:Hs2.
remember (0 ≤? rngl_sin (α2 - α1))%L as s12 eqn:Hs12.
symmetry in Hs1, Hs2, Hs12.
destruct s12. {
  apply rngl_leb_le in Hs12.
  destruct s2; [ | easy ].
  apply rngl_leb_le in Hs2.
  apply rngl_leb_le.
  destruct s1; [ | easy ].
  apply rngl_leb_le in Hs1.
  apply rngl_leb_le in H12.
  rewrite rngl_cos_sub_comm.
  now apply rngl_cos_le_cos_sub.
}
destruct s2. {
  exfalso.
  apply rngl_leb_nle in Hs12.
  apply Hs12; clear Hs12.
  destruct s1; [ | easy ].
  apply rngl_leb_le in Hs1, Hs2, H12.
  now apply rngl_sin_sub_nonneg.
}
apply (rngl_leb_gt_iff Hto) in Hs2, Hs12.
apply rngl_leb_le.
destruct s1. {
  clear H12.
  apply rngl_leb_le in Hs1.
  change_angle_add_r α2 π.
  progress sin_cos_add_sub_straight_hyp T Hs2.
  progress sin_cos_add_sub_straight_hyp T Hs12.
  progress sin_cos_add_sub_straight_goal T.
  rewrite rngl_cos_sub_comm.
  apply rngl_cos_le_cos_sub; [ now apply rngl_lt_le_incl | easy | ].
  apply rngl_sin_sub_nonneg_iff; [ easy | easy | ].
  now apply rngl_lt_le_incl.
}
apply rngl_leb_le in H12.
apply (rngl_leb_gt_iff Hto) in Hs1.
change_angle_add_r α1 π.
progress sin_cos_add_sub_straight_hyp T Hs1.
progress sin_cos_add_sub_straight_hyp T H12.
progress sin_cos_add_sub_straight_hyp T Hs12.
rewrite angle_sub_sub_distr.
progress sin_cos_add_sub_straight_goal T.
change_angle_add_r α2 π.
progress sin_cos_add_sub_straight_hyp T Hs2.
progress sin_cos_add_sub_straight_hyp T H12.
progress sin_cos_add_sub_straight_hyp T Hs12.
progress sin_cos_add_sub_straight_goal T.
rewrite (rngl_add_opp_l Hop) in H12.
apply -> (rngl_le_sub_0 Hop Hor) in H12.
apply (rngl_nle_gt Hor) in Hs12.
exfalso; apply Hs12.
apply rngl_sin_sub_nonneg; [ | | easy ].
now apply rngl_lt_le_incl.
now apply rngl_lt_le_incl.
Qed.

Theorem angle_eq_mul_nat_cancel_l_le :
  ∀ n α1 α2,
  (α1 ≤ α2)%A
  → angle_mul_nat_div_2π n α2 = 0
  → (n * α1 = n * α2)%A
  → n ≠ 0
  → α1 = α2.
Proof.
destruct_ac.
intros * H12 Hn2 Ht Hnz.
symmetry.
apply angle_sub_move_0_r.
enough (H : n = 0 ∨ (α2 - α1 = 0)%A) by now destruct H.
apply angle_mul_nat_integral. {
  apply (angle_mul_nat_div_2π_le_r _ α2); [ | easy ].
  now apply (angle_le_le_sub_l Hop Hto).
}
rewrite angle_mul_sub_distr_l, Ht.
apply angle_sub_diag.
Qed.

Theorem angle_eq_mul_nat_cancel_l :
  ∀ n α1 α2,
  angle_mul_nat_div_2π n α1 = 0
  → angle_mul_nat_div_2π n α2 = 0
  → (n * α1 = n * α2)%A
  → n ≠ 0
  → α1 = α2.
Proof.
destruct_ac.
intros * Hn1 Hn2 Ht Hnz.
destruct (angle_le_dec α1 α2) as [H12| H12]. {
  now apply (angle_eq_mul_nat_cancel_l_le n).
} {
  apply angle_nle_gt, angle_lt_le_incl in H12.
  symmetry.
  now apply (angle_eq_mul_nat_cancel_l_le n).
}
Qed.

Theorem angle_lim_0_le :
  rngl_is_ordered T = true →
  ∀ f g,
  (∀ i, (g i ≤ f i ≤ π)%A)
  → angle_lim f 0
  → angle_lim g 0.
Proof.
intros Hor.
intros * Hgf Hf ε Hε.
specialize (Hf ε Hε).
destruct Hf as (N, Hn).
exists N; intros i Hi.
eapply (rngl_le_lt_trans Hor); [ | apply Hn, Hi ].
apply angle_le_angle_eucl_dist_le; [ | apply Hgf | apply Hgf ].
apply (angle_le_trans _ (f i)); apply Hgf.
Qed.

Theorem angle_mul_div_nat :
  rngl_characteristic T = 0 →
  rngl_is_archimedean T = true →
  is_complete T rngl_dist →
  ∀ α n,
  n ≠ 0
  → angle_mul_nat_div_2π n α = 0
  → angle_div_nat (n * α) n α.
Proof.
destruct_ac.
intros Hch Har Hco * Hnz Hmn.
specialize (rngl_is_complete_angle_is_complete Hco) as H1.
specialize (seq_angle_to_div_nat_is_Cauchy Har n (n * α)) as H.
specialize (H1 _ H); clear H.
destruct (Nat.eq_dec n 1) as [Hn1| Hn1]. {
  subst n.
  rewrite angle_mul_1_l.
  intros ε Hε.
  progress unfold seq_angle_to_div_nat.
  exists 0.
  intros n _.
  rewrite Nat.div_1_r.
  rewrite angle_div_2_pow_mul_2_pow.
  now rewrite angle_eucl_dist_diag.
}
destruct H1 as (α', Ht).
progress unfold angle_div_nat.
progress unfold angle_lim.
specialize (angle_div_nat_prop Hch Har Hco) as H2.
specialize (H2 (n * α)%A n α').
specialize (H2 Ht).
destruct H2 as [H2| H2]; [ easy | ].
rewrite fold_angle_div_nat in Ht |-*.
destruct (angle_le_dec α' α) as [Htt| Htt]. {
  apply angle_eq_mul_nat_cancel_l_le in H2; [ | easy | easy | easy ].
  now subst α'.
}
apply angle_nle_gt in Htt.
progress unfold angle_div_nat in Ht.
progress unfold angle_div_nat.
apply angle_lim_move_0_r in Ht.
apply angle_lim_move_0_r.
apply angle_lim_opp in Ht.
rewrite angle_opp_0 in Ht.
progress unfold seq_angle_to_div_nat.
destruct (Nat.eq_dec n 0) as [H| H]; [ easy | clear H ].
eapply (angle_lim_eq_compat 0 0). {
  intros i.
  rewrite Nat.add_0_r.
  symmetry.
  rewrite angle_div_2_pow_mul; [ | easy ].
  rewrite angle_mul_nat_assoc.
  rewrite Nat.mul_comm.
  rewrite <- (angle_div_2_pow_mul_2_pow i α) at 2.
  rewrite <- angle_opp_sub_distr.
  rewrite <- angle_mul_sub_distr_r; [ | apply Nat.Div0.mul_div_le ].
  rewrite <- Nat.Div0.mod_eq.
  reflexivity.
}
rewrite <- angle_opp_0.
apply angle_lim_opp.
remember (Nat.log2_up n + 1) as k eqn:Hk.
eapply (angle_lim_eq_compat 0 k). {
  intros.
  rewrite Nat.add_0_r; symmetry.
  easy.
}
apply (angle_lim_0_le Hor (λ i, (n * (α /₂^(i + k)))))%A. {
  intros i.
  split. {
    apply (angle_le_trans _ (n * (α /₂^ (i + k)))). {
      apply angle_mul_le_mono_r. 2: {
        apply Nat.lt_le_incl.
        now apply Nat.mod_upper_bound.
      }
      apply angle_mul_nat_div_2π_div_pow2.
      rewrite Nat.pow_add_r.
      subst k.
      rewrite Nat.pow_add_r.
      cbn.
      rewrite Nat.mul_assoc, Nat.mul_shuffle0.
      rewrite <- (Nat.pow_1_r 2) at 2.
      rewrite <- Nat.pow_add_r.
      apply (Nat.le_trans _ (2 ^ Nat.log2_up n)). {
        apply Nat.log2_up_spec.
        flia Hnz Hn1.
      }
      apply Nat.le_mul_l.
      now apply Nat.pow_nonzero.
    }
    apply angle_le_refl.
  }
  subst k.
  apply angle_mul_div_pow2_le_straight.
  rewrite Nat.add_assoc, Nat.add_comm.
  rewrite Nat.pow_add_r.
  apply Nat.mul_le_mono_l.
  rewrite Nat.pow_add_r.
  apply (Nat.le_trans _ (2 ^ Nat.log2_up n)). {
    apply Nat.log2_up_spec; flia Hnz Hn1.
  }
  apply Nat.le_mul_l.
  now apply Nat.pow_nonzero.
}
intros ε Hε.
specialize (exists_nat_such_that_rngl_cos_close_to_1 Har) as H1.
specialize (H1 (n * α)%A ε Hε).
destruct H1 as (N, HN).
exists N.
intros m Hm.
rewrite angle_eucl_dist_symmetry.
apply rngl_cos_lt_angle_eucl_dist_lt; [ now apply rngl_lt_le_incl | ].
rewrite angle_sub_0_r.
rewrite <- angle_div_2_pow_mul; [ | easy ].
apply HN.
flia Hm.
Qed.

(*
Axiom unique_choiceT : ∀ {A B} (P : A → B → Prop),
  (∀ a, ∃! b, P a b)
  → ∃ₜ f, ∀ a b, P a b → b = f a.

Definition angle_div
  (Hch : rngl_characteristic T = 0)
  (Har : rngl_is_archimedean T = true)
  (Hco : is_complete T rngl_dist) :
  ∀ (α : angle T) (n : nat), angle T.
Proof.
destruct_ac.
assert (H : ∀ αn, ∃! y, angle_div_nat (fst αn) (snd αn) y). {
  intros (α, n); cbn.
  specialize (rngl_is_complete_angle_is_complete Hco) as H1.
  specialize (seq_angle_to_div_nat_is_Cauchy Har n α) as H.
  specialize (H1 _ H); clear H.
  destruct H1 as (α', H1).
  rewrite fold_angle_div_nat in H1.
  exists α'.
  progress unfold unique.
  split; [ easy | ].
  intros α'' Ht.
  specialize (limit_unique Hop Hiv Hto angle_eucl_dist_is_dist) as H2.
  apply (H2 _ _ _ H1 Ht).
}
specialize (unique_choiceT _ H) as H1.
destruct H1 as (f, H1).
apply (λ α n, f (α, n)).
Qed.
Check angle_div.
*)

(*
Require Import Stdlib.Logic.ClassicalUniqueChoice.
Theorem angle_div
  (Hch : rngl_characteristic T = 0)
  (Har : rngl_is_archimedean T = true)
  (Hco : is_complete T rngl_dist) :
  ∀ (α : angle T) (n : nat), angle T.
destruct_ac.
assert (H : ∀ αn, ∃! y, angle_div_nat (fst αn) (snd αn) y). {
  intros (α, n); cbn.
  specialize (rngl_is_complete_angle_is_complete Hco) as H1.
  specialize (seq_angle_to_div_nat_is_Cauchy Har n α) as H.
  specialize (H1 _ H); clear H.
  destruct H1 as (α', H1).
  rewrite fold_angle_div_nat in H1.
  exists α'.
  progress unfold unique.
  split; [ easy | ].
  intros α'' Ht.
  specialize (limit_unique Hop Hiv Hto angle_eucl_dist_is_dist) as H2.
  apply (H2 _ _ _ H1 Ht).
}
About unique_choice.
Search (∀ _ _ _, (∀ _, ∃! _, _) → _).
Search (∀ _ _ _, (∀ _, { _ &  _}) → _).
specialize (unique_choice _ _ _ H) as H1.
...
apply (λ α n, f (α, n)).
...
specialize (rngl_is_complete_angle_is_complete Hco) as H1.
Check unique_choice.
specialize (seq_angle_to_div_nat_is_Cauchy Har n α) as H.
specialize (H1 _ H); clear H.
rewrite fold_angle_div_nat in H1.
destruct H1 as (α', H).
specialize (angle_div_nat_prop Hch Har Hco α n) as H.
...
*)

(* to be completed later
Theorem glop :
  rngl_characteristic T = 0 →
  rngl_is_archimedean T = true →
  is_complete T rngl_dist →
  ∀ n α π_n,
  n ≠ 0
  → angle_div_nat π n π_n
  → (n * α = 0)%A
  → ∃ m, (α = m * (2 * π_n))%A.
Proof.
intros Hch Har Hco * Hnz Hpn Hnt.
revert α π_n Hnt Hpn.
induction n; intros; [ easy | clear Hnz ].
generalize Hpn; intros H.
apply (angle_div_nat_prop Hch Har Hco) in H.
destruct H as [(H, _)| H]; [ easy | ].
destruct (Nat.eq_dec n 0) as [Hnz| Hnz]. {
  subst n.
  rewrite angle_mul_1_l in H, Hnt; subst α.
  now exists 0.
}
specialize (IHn Hnz).
...
    subst π_n.
    progress unfold angle_div_nat in Hpn.
    progress unfold seq_angle_to_div_nat in Hpn.
    cbn in Hpn.
...

Theorem glop :
  rngl_characteristic T = 0 →
  rngl_is_archimedean T = true →
  is_complete T rngl_dist →
  ∀ n α α' π_n,
  n ≠ 0
  → angle_div_nat (n * α) n α'
  → angle_div_nat π n π_n
  → α' = (α - angle_mul_nat_div_2π n α * (2 * π_n))%A.
Proof.
intros Hch Har Hco * Hnz Hnt Hnp.
generalize Hnt; intros H.
apply (angle_div_nat_prop Hch Har Hco) in H.
destruct H as [(H1, H2)| Hnn]; [ easy | ].
symmetry in Hnn |-*.
apply angle_sub_move_0_r in Hnn.
apply angle_sub_move_0_r.
rewrite <- angle_mul_sub_distr_l in Hnn.
rewrite angle_sub_sub_swap.
apply angle_sub_move_0_r.
Search (_ * _ = 0)%A.
...
Theorem glop :
  ∀ n α α' π_n,
  angle_div_nat π n π_n
  → (n * (α - α') = 0
  → ∃ m, α = α' + m * (2 * π_n))%A.
Proof.
intros * Hpn Hntt.
generalize Hntt; intros H.
apply eq_angle_eq in H.
injection H; clear H; intros Hs Hc; move Hc after Hs.
enough
  (∃ m,
   rngl_cos α = rngl_cos (α' + m * (2 * π_n)) ∧
   rngl_sin α = rngl_sin (α' + m * (2 * π_n))). {
  destruct H as (m & Hcm & Hsm).
  exists m.
  apply eq_angle_eq.
  congruence.
}
...

Theorem glop :
  rngl_characteristic T = 0 →
  rngl_is_archimedean T = true →
  is_complete T rngl_dist →
  ∀ n α,
  n ≠ 0
  → ∃ α' π_n,
    angle_div_nat (n * α) n α' ∧
    angle_div_nat π n π_n ∧
    α' = (α - 2 * angle_mul_nat_div_2π n α * π_n)%A.
Proof.
intros Hch Har Hco * Hnz.
specialize (rngl_is_complete_angle_is_complete Hco) as H1.
specialize (seq_angle_to_div_nat_is_Cauchy Har n (n * α)) as H.
specialize (H1 _ H); clear H.
destruct H1 as (α', Ht).
rewrite fold_angle_div_nat in Ht.
specialize (rngl_is_complete_angle_is_complete Hco) as H2.
specialize (seq_angle_to_div_nat_is_Cauchy Har n π) as H.
specialize (H2 _ H); clear H.
destruct H2 as (π_n, Hp).
rewrite fold_angle_div_nat in Hp.
move α' before α; move π_n before α'.
exists α', π_n.
split; [ easy | ].
split; [ easy | ].
generalize Hp; intros H.
apply (angle_div_nat_prop Hch Har Hco) in H.
destruct H as [(H1, H2)| Hp1]; [ easy | ].
generalize Ht; intros H.
apply (angle_div_nat_prop Hch Har Hco) in H.
destruct H as [(H1, H2)| Ht1]; [ easy | ].
Search (_ * _ = _ * _)%A.
...
*)

(* to be completed later
Theorem glop :
  rngl_has_opp T = true →
  rngl_is_totally_ordered T = true →
  ∀ n α,
  angle_div_nat (n * α) n α
  → angle_mul_nat_div_2π n α = 0.
Proof.
intros Hop Hto.
specialize (rngl_is_totally_ordered_is_ordered Hto) as Hor.
specialize (rngl_has_eq_dec_or_is_ordered_r Hor) as Heo.
intros * Htt.
apply angle_mul_nat_div_2π_iff.
cbn.
split. {
  intros i Hi.
  apply Nat.le_0_r.
  revert n Htt Hi.
  induction i; intros; [ easy | ].
  cbn.
  rewrite (IHi n); [ | easy | flia Hi ].
  apply Nat_eq_b2n_0.
  apply angle_add_not_overflow_iff.
  destruct (angle_eq_dec α 0) as [Htz| Htz]; [ now left | right ].
...
Theorem angle_mul_nat_div_2π_le :
  ∀ n α k, k ≤ n → angle_mul_nat_div_2π k α ≤ angle_mul_nat_div_2π n α.
Proof.
(* euh, je crois que c'est faux *)
intros * Hkn.
revert k Hkn.
induction n; intros; cbn. {
  now apply Nat.le_0_r in Hkn; subst k.
}
destruct k; [ easy | cbn ].
apply Nat.succ_le_mono in Hkn.
apply Nat.add_le_mono; [ now apply IHn | ].
remember (angle_add_overflow α (k * α)) as ovk eqn:Hk.
remember (angle_add_overflow α (n * α)) as ovn eqn:Hn.
symmetry in Hk, Hn.
destruct ovk; [ cbn | easy ].
destruct ovn; [ easy | cbn ].
exfalso.
apply Bool.not_false_iff_true in Hk.
apply Hk; clear Hk.
apply (angle_add_overflow_le _ (n * α)); [ | easy ].
apply angle_mul_le_mono_r; [ | easy ].
(*
clear k IHn Hkn.
*)
(* lemma *)
apply angle_add_not_overflow_iff in Hn.
destruct Hn as [Hn| Hn]; [ subst; apply angle_mul_nat_div_2π_0_r | ].
...
(*
  Hn : (n * α < - α)%A
  ============================
  angle_mul_nat_div_2π n α = 0
*)
...
induction n; [ easy | ].
assert (H : (n * α < - α)%A). {
...
  eapply angle_le_lt_trans; [ | apply Hn ].
  apply angle_mul_le_mono_r; [ | flia ].
assert (angle_mul_nat_div_2π (S n) α = angle_mul_nat_div_2π n α). {
  cbn.
  replace (angle_add_overflow _ _) with false.
  apply Nat.add_0_r.
  symmetry.
  apply angle_add_not_overflow_iff.
  (* crotte de bique *)
...
angle_mul_nat_div_2π b α = 0 est une condition suffisante, mais
elle n'est pas nécessaire. Il faudrait affiner :

angle_mul_le_mono_r
     : ∀ (a b : nat) (α : angle T), angle_mul_nat_div_2π b α = 0 → a ≤ b → (a * α ≤ b * α)%A
...
  apply angle_mul_le_mono_r; [ | flia ].
...
cbn in Hn.
destruct n; [ now cbn; rewrite angle_add_overflow_0_r | ].
cbn in Hn |-*.
apply Nat.eq_add_0.
split. {
  apply Nat.eq_add_0.
  split. {
    destruct n; [ easy | ].
    cbn in Hn |-*.
    apply Nat.eq_add_0.
    split. {
      destruct n; [ easy | ].
      cbn in Hn |-*.
      apply Nat.eq_add_0.
      split. {
...
induction n; [ easy | cbn ].
apply Nat.eq_add_0.
split. {
  apply IHn.
  apply (angle_add_overflow_le _ (S n * α)); [ | easy ].
  cbn.
  rewrite angle_add_comm.
  rewrite <- angle_add_0_r at 1.
Search (_ ≤ _ + _)%A.
  apply angle_add_le_mono_l.
...
  apply angle_le_add_r.
... ...
          specialize (angle_mul_nat_div_2π_le n α i) as H4.
          rewrite H1 in H4.
          apply H4.
          now apply Nat.succ_le_mono in Hi.
        }

... ...
apply angle_mul_nat_div_2π_iff.
...
intros Hop Hto.
specialize (rngl_is_totally_ordered_is_ordered Hto) as Hor.
specialize (rngl_has_eq_dec_or_is_ordered_r Hor) as Heo.
intros * Htt.
induction n; [ easy | ].
cbn.
rewrite IHn. {
  apply Nat_eq_b2n_0.
  apply angle_add_not_overflow_iff.
  destruct (angle_eq_dec α 0) as [Htz| Htz]; [ now left | right ].
  progress unfold angle_ltb; cbn.
  rewrite (rngl_leb_0_opp Hop Hto).
  remember (0 ≤? rngl_sin (n * α))%L as zsn eqn:Hzsn.
  remember (rngl_sin α ≤? 0)%L as sz eqn:Hsz.
  symmetry in Hzsn, Hsz.
  destruct zsn. {
    destruct sz; [ | easy ].
    apply rngl_leb_le in Hzsn, Hsz.
    apply (rngl_ltb_lt Heo).
    change_angle_add_r α π.
    progress sin_cos_add_sub_straight_hyp T Hsz.
    progress sin_cos_add_sub_straight_goal T.
    rewrite angle_mul_sub_distr_l in Hzsn |-*.
    destruct (Nat.Even_Odd_dec n) as [Hn| Hn]. {
      apply Nat.Even_EvenT in Hn.
      destruct Hn as (m, Hn).
      subst n; rename m into n; move n after α.
      rewrite Nat.mul_comm in Hzsn at 2.
      rewrite Nat.mul_comm at 2.
      rewrite <- (angle_mul_nat_assoc _ _ π) in Hzsn |-*.
      rewrite angle_mul_2_l in Hzsn |-*.
      rewrite angle_straight_add_straight in Hzsn |-*.
      rewrite angle_mul_0_r in Hzsn |-*.
      rewrite angle_sub_0_r in Hzsn |-*.
(* oh putain, chais pas du tout si je vais y arriver *)
...

Theorem glop' :
  rngl_characteristic T = 0 →
  rngl_is_archimedean T = true →
  is_complete T rngl_dist →
  ∀ α n α',
  angle_div_nat α n α'
  → angle_mul_nat_div_2π n α' = 0.
Proof.
intros Hch Har Hco * Htt.
generalize Htt; intros H.
apply (angle_div_nat_prop Hch Har Hco) in H.
destruct H as [(Hn, Ht)| Hntt]; [ now subst | ].
subst α; rename α' into α.
... ...
now apply glop.
...
*)

Theorem angle_div_nat_0_l : ∀ n α, angle_div_nat 0 n α → α = 0%A.
Proof.
intros * Hn.
progress unfold angle_div_nat in Hn.
progress unfold seq_angle_to_div_nat in Hn.
eapply (angle_lim_eq_compat 0 0) in Hn. 2: {
  intros i; rewrite Nat.add_0_r.
  rewrite angle_0_div_2_pow.
  rewrite angle_mul_0_r.
  easy.
}
now apply angle_lim_const in Hn.
Qed.

Theorem angle_add_not_overflow_diag :
  ∀ α, (α < π)%A → angle_add_overflow α α = false.
Proof.
intros * Htp.
apply angle_add_not_overflow_lt_straight_le_straight; [ easy | ].
now apply angle_lt_le_incl.
Qed.

Theorem fold_seq_angle_to_div_nat :
  ∀ α n i, (2 ^ i / n * (α /₂^i))%A = seq_angle_to_div_nat α n i.
Proof. easy. Qed.

Theorem angle_div_2_pow_le_angle_sub_seq :
  rngl_is_archimedean T = true →
  ∀ n α,
  (∀ i, n ≤ 2 ^ i → seq_angle_to_div_nat (n * α) n i ≠ α)
  → ∀ i, ∃ N, N < i → (α /₂^i ≤ α - seq_angle_to_div_nat (n * α) n i)%A.
Proof.
destruct_ac.
destruct (Nat.eq_dec (rngl_characteristic T) 1) as [Hc1| Hc1]. {
  specialize (rngl_characteristic_1_angle_0 Hc1) as H1.
  exists 0; intros.
  rewrite (H1 (α /₂^ i)%A).
  apply angle_nonneg.
}
intros Har * Hsnz *.
progress unfold seq_angle_to_div_nat.
destruct (angle_eq_dec α 0) as [Htz| Htz]. {
  subst α.
  rewrite angle_0_div_2_pow.
  exists 0; intros.
  apply angle_nonneg.
}
destruct (Nat.eq_dec n 0) as [Hnz| Hnz]. {
  subst n; cbn.
  rewrite angle_sub_0_r.
  exists 0; intros.
  apply angle_div_2_pow_le_diag.
}
remember (α - 2 ^ i / n * ((n * α) /₂^i))%A as α' eqn:Ht.
destruct (angle_eq_dec α' 0) as [Ht'z| Ht'z]. {
  rewrite Ht'z in Ht.
  symmetry in Ht.
  apply -> angle_sub_move_0_r in Ht.
  symmetry in Ht.
  destruct (le_dec n (2 ^ i)) as [Hni| Hni]. 2: {
    apply Nat.nle_gt in Hni.
    rewrite Nat.div_small in Ht; [ | easy ].
    now symmetry in Ht.
  }
  exfalso; revert Ht.
  now apply Hsnz.
}
assert (Hzt : (0 < 1 - rngl_cos α')%L). {
  apply (rngl_lt_0_sub Hop Hor).
  apply rngl_le_neq.
  split ; [ apply rngl_cos_bound | ].
  intros H.
  now apply eq_rngl_cos_1 in H.
}
specialize (exists_nat_such_that_rngl_cos_close_to_1 Har α) as H1.
specialize (H1 (1 - rngl_cos α')%L Hzt).
destruct H1 as (N, Hn).
exists N; intros Hin.
remember (∀ m, _) as u in Hn; subst u. (* renaming *)
assert (Hzs : (0 ≤? rngl_sin (α /₂^i))%L = true). {
  apply rngl_leb_le.
  destruct i; [ easy | ].
  apply rngl_sin_nonneg_angle_le_straight.
  cbn.
  apply angle_div_2_le_straight.
}
remember (0 ≤? rngl_sin α')%L as zs' eqn:Hzs'.
symmetry in Hzs'.
destruct zs'. 2: {
  progress unfold angle_leb.
  now rewrite Hzs, Hzs'.
}
apply rngl_leb_le in Hzs, Hzs'.
progress unfold angle_leb.
apply rngl_leb_le in Hzs, Hzs'.
rewrite Hzs, Hzs'.
apply rngl_leb_le in Hzs, Hzs'.
apply rngl_leb_le.
eapply (rngl_le_lt_trans Hor); [ | now apply Hn, Nat.lt_le_incl ].
rewrite (rngl_squ_sub Hop Hic).
rewrite rngl_squ_1, rngl_mul_1_r.
rewrite <- (rngl_add_sub_swap Hop).
rewrite (rngl_div_sub_distr_r Hop Hiv).
rewrite (rngl_mul_comm Hic).
rewrite (rngl_mul_div Hiq). 2: {
  apply (rngl_2_neq_0 Hos Hc1 Hto).
}
rewrite (rngl_sub_sub_distr Hop).
rewrite (rngl_div_add_distr_r Hiv).
rewrite (rngl_sub_add_distr Hos).
rewrite <- (rngl_div_diag Hiq 2) at 1. 2: {
  apply (rngl_2_neq_0 Hos Hc1 Hto).
}
rewrite <- (rngl_div_sub_distr_r Hop Hiv).
rewrite (rngl_add_sub Hos).
apply (rngl_le_add_l Hos Hor).
apply (rngl_le_0_sub Hop Hor).
apply (rngl_div_le_mono_pos_r Hop Hiv Hto). {
  apply (rngl_0_lt_2 Hos Hc1 Hto).
}
apply (rngl_squ_le_1_iff Hop Hiq Hto).
apply rngl_cos_bound.
Qed.

Theorem is_limit_when_seq_tends_to_inf_shift {A} :
  ∀ n (da : A → _) u L,
  is_limit_when_seq_tends_to_inf da u L
  → is_limit_when_seq_tends_to_inf da (λ i, u (i + n)) L.
Proof.
intros * Hlim ε Hε.
specialize (Hlim ε Hε).
destruct Hlim as (N, Hn).
exists N; intros i Hi.
apply Hn.
apply (Nat.le_trans _ i); [ easy | ].
apply Nat.le_add_r.
Qed.

Theorem rngl_cos_div_2 :
  ∀ α,
  rngl_cos (α /₂) = (rngl_signp (rngl_sin α) * √ ((1 + rngl_cos α) / 2))%L.
Proof. easy. Qed.

Theorem rngl_sin_div_2 :
  ∀ α, rngl_sin (α /₂) = √ ((1 - rngl_cos α) / 2).
Proof. easy. Qed.

Theorem angle_mul_nat_div_2π_for_seq :
  ∀ n α i, angle_mul_nat_div_2π (2 ^ i / n) (α /₂^ i) = 0.
Proof.
intros.
apply angle_mul_nat_div_2π_div_pow2.
destruct n; [ easy | ].
apply Nat.Div0.div_le_upper_bound.
now apply Nat.le_mul_l.
Qed.

(* to be completed
Theorem angle_div_nat_integral :
  rngl_characteristic T = 0 →
  rngl_is_archimedean T = true →
  is_complete T rngl_dist →
  ∀ n α α',
  angle_div_nat α n α'
  → angle_mul_nat_div_2π n α' = 0.
Proof.
(* could be renamed angle_mul_div_nat_if to reflect the fact that
   the theorem angle_mul_div_nat is its reverse *)
(**)
destruct_ac.
intros Hch Har Hco * Htt.
destruct (Nat.eq_dec n 0) as [| Hnz]; [ now subst n | ].
destruct (Nat.eq_dec n 1) as [| Hn1]. {
  subst n; cbn.
  apply Nat_eq_b2n_0.
  apply angle_add_overflow_0_r.
}
destruct (angle_eq_dec α 0) as [Htz| Htz]. {
  subst α.
  apply angle_div_nat_0_l in Htt; subst α'.
  apply angle_mul_nat_div_2π_0_r.
}
generalize Htt; intros H.
apply (angle_div_nat_prop Hch Har Hco) in H.
destruct H as [(H1, H2)| H]; [ now subst n | ].
subst α; rename α' into α.
(*
specialize (angle_div_2_pow_le_angle_sub_seq Har n α) as H1.
assert (H : ∀ i, n ≤ 2 ^ i → seq_angle_to_div_nat (n * α) n i ≠ α). {
  intros * Hni.
  progress unfold seq_angle_to_div_nat.
  intros H2.
  destruct i. {
    cbn in Hni.
    destruct n; [ easy | clear Hnz ].
    destruct n; [ easy | clear Hn1 ].
    now apply Nat.succ_le_mono in Hni.
  }
  destruct i. {
    cbn in Hni.
    destruct n; [ easy | clear Hnz ].
    destruct n; [ easy | clear Hn1 ].
    destruct n. {
      rewrite Nat.div_same in H2; [ | easy ].
      rewrite angle_mul_1_l in H2.
      cbn - [ angle_mul_nat ] in H2.
      (* on doit pouvoir en déduire que α < π *)
      (* encore faut-il que ça serve à quelque chose *)
(* ouais, c'est nul *)
...
  apply (is_limit_when_seq_tends_to_inf_shift n) in Htt.
...
}
rewrite angle_div_2_pow_succ_r_1 in H.
rewrite angle_mul_nat_div_2 in H.
Search (_ * (_ /₂^_) = _)%A.
(* ouais, chais pas *)
...
  apply angle_mul_nat_integral in H. 2: {
    apply (angle_mul_nat_not_overflow_le_l _ (2 ^ i)). {
      apply Nat.Div0.div_le_upper_bound.
      now apply Nat.le_mul_l.
    }
    apply angle_mul_nat_div_2π_pow_div.
  }
  destruct H as [H| H]. {
    apply Nat.div_small_iff in H; [ | easy ].
    now apply Nat.nle_gt in H.
  }
  now apply eq_angle_div_2_pow_0 in H.
}
specialize (H1 H); clear H.
...
*)
specialize (exists_angle_div_nat Hch Har Hco π n Hnz) as H1.
destruct H1 as (π_n, Hp).
move π_n before α.
progress unfold angle_div_nat in Htt.
progress unfold seq_angle_to_div_nat in Htt.
Theorem glop :
  ∀ f g n α,
  angle_lim (λ i, (f n i * g (n * α) i)%A) α
  → (∀ i, angle_mul_nat_div_2π (f n i) (g (n * α)%A i) = 0)
  → angle_mul_nat_div_2π n α = 0.
Proof.
intros * Hlim Hni.
revert f g Hlim Hni.
induction n; intros; [ easy | cbn ].
rewrite (IHn (λ n i, f (S n) i) (λ α' i, g (S n * α)%A i)); [ | easy | easy ].
apply Nat_eq_b2n_0.
... ...
specialize (angle_mul_nat_div_2π_for_seq n (n * α)) as H1.
apply (glop (λ n i, 2 ^ i / n) (λ α i, (α /₂^i)%A)); [ easy | easy ].
...
Theorem glop :
  rngl_characteristic T = 0 →
  rngl_is_archimedean T = true →
  is_complete T rngl_dist →
  ∀ n α,
  2 ≤ n
  → angle_div_nat (n * α) n α
  → (α ≤ π)%A.
Proof.
destruct_ac.
intros Hch Har Hco * H2n Htt.
destruct (Nat.eq_dec (rngl_characteristic T) 1) as [Hc1| Hc1]. {
  now rewrite Hch in Hc1.
}
move Hc1 before Hch.
destruct (Nat.eq_dec n 0) as [Hnz| Hnz]; [ flia Hnz H2n | ].
destruct (Nat.eq_dec n 1) as [Hn1| Hn1]; [ flia Hn1 H2n | ].
clear H2n.
apply rngl_sin_nonneg_angle_le_straight.
progress unfold angle_div_nat in Htt.
progress unfold seq_angle_to_div_nat in Htt.
(**)
assert (
  H :
  ∀ ε, (0 < ε)%L →
  ∃ N, ∀ i, N ≤ i →
  (1 - ε² / 2 < rngl_cos (α - 2 ^ i / n * ((n * α) /₂^i)))%L). {
  intros * Hε.
  specialize (Htt ε Hε).
  destruct Htt as (N, Hn).
  exists N.
  intros m Hm.
  apply rngl_cos_lt_angle_eucl_dist_lt; [ now apply rngl_lt_le_incl | ].
  now apply Hn.
}
clear Htt; rename H into Htt.
...
apply angle_lim_move_0_r in Htt.
apply angle_lim_opp in Htt.
rewrite angle_opp_0 in Htt.
eapply (angle_lim_eq_compat 0 0) in Htt. 2: {
  intros i.
  rewrite Nat.add_0_r.
  rewrite angle_opp_sub_distr.
  easy.
}
...
specialize (exists_nat_such_that_rngl_cos_close_to_1 Har (n * α)) as H1.
progress unfold angle_div_nat in Htt.
progress unfold seq_angle_to_div_nat in Htt.
progress unfold angle_lim in Htt.
progress unfold is_limit_when_seq_tends_to_inf in Htt.
remember (∀ ε, _ → ∃ N, ∀ i, _) as x; subst x. (* renaming *)
remember (∀ ε, _ → ∃ N, ∀ i, _) as x in H1; subst x. (* renaming *)
assert (
  H :
  ∀ ε, (0 < ε)%L →
  ∃ N, ∀ i, N ≤ i →
  (1 - ε² / 2 < rngl_cos (α - 2 ^ i / n * ((n * α) /₂^i)))%L). {
  intros * Hε.
  specialize (Htt ε Hε).
  destruct Htt as (N, Hn).
  exists N.
  intros m Hm.
  apply rngl_cos_lt_angle_eucl_dist_lt; [ now apply rngl_lt_le_incl | ].
  now apply Hn.
}
move H before Htt; clear Htt; rename H into Htt.
progress unfold angle_leb.
remember (0 ≤? rngl_sin α)%L as zs eqn:Hzs.
remember (0 ≤? rngl_sin (2 * π_n))%L as zp eqn:Hzp.
symmetry in Hzs, Hzp.
destruct zs. {
  destruct zp; [ | easy ].
  apply rngl_leb_le in Hzs, Hzp.
  apply rngl_leb_le.
...
Search (rngl_cos (_ /₂)).
Search (rngl_cos (_ /₂^ _)).
Locate "/₂".
Print angle_div_2.
About angle_div_2.
Search (if _ then 1%L else _).
...
Search (_ → rngl_cos _ ≤ rngl_cos _)%L.
apply quadrant_1_sin_sub_nonneg_cos_le; [ easy | easy | | ].
...
generalize Htt; intros Htt_v.
progress unfold angle_div_nat in Htt.
apply angle_lim_move_0_r in Htt.
apply angle_lim_opp in Htt.
rewrite angle_opp_0 in Htt.
eapply (angle_lim_eq_compat 0 0) in Htt. 2: {
  intros i.
  rewrite Nat.add_0_r.
  rewrite angle_opp_sub_distr.
  easy.
}
...
eapply (angle_lim_eq_compat (Nat.log2_up n) 0) in Htt. 2: {
  now intros i; rewrite Nat.add_0_r.
}
... ...
assert (Htp : (α ≤ 2 * π_n)%A). {
...
  eapply angle_lim_0_le in Htt. 2: {
    intros i.
    split. {
...
}
apply Nat.max_lt_iff in Hin.
destruct Hin as [Hin| Hin]. 2: {
  rewrite Nat.div_small in Ht. 2: {
    apply Nat.log2_le_pow2 in Hin; [ | now apply Nat.neq_0_lt_0 ].
    apply (Nat.lt_le_trans _ (2 ^ S i)); [ | easy ].
    now apply Nat.pow_lt_mono_r_iff.
  }
  cbn in Ht.
  rewrite angle_sub_0_r in Ht.
  subst α'.
  apply angle_div_2_pow_le_diag.
}
...
destruct_ac.
intros Hch Har Hco * Htt.
generalize Htt; intros H.
apply (angle_div_nat_prop Hch Har Hco) in H.
destruct H as [(H1, H2)| H]; [ now subst n | ].
destruct (Nat.eq_dec n 0) as [Hnz| Hnz]; [ now subst n | ].
subst α; rename α' into α; move Hnz after Htt.
(* marrant, ça *)
destruct n; [ easy | clear Hnz ].
destruct n; [ now cbn; rewrite angle_add_overflow_0_r | ].
destruct n. {
  cbn in Htt |-*.
  rewrite angle_add_0_r in Htt |-*.
  rewrite angle_add_overflow_0_r; cbn.
  apply Nat_eq_b2n_0.
  cbn in Htt.
  assert (H : (α ≤ π)%A). {
    progress unfold angle_div_nat in Htt.
    apply angle_lim_move_0_r in Htt.
    eapply (angle_lim_eq_compat 1 0) in Htt. 2: {
      intros i.
      rewrite Nat.add_0_r.
      progress unfold seq_angle_to_div_nat.
      rewrite Nat.pow_add_r.
      rewrite Nat.pow_1_r.
      rewrite Nat.div_mul; [ | easy ].
      rewrite Nat.add_comm.
      rewrite angle_div_2_pow_add_r.
      rewrite angle_div_pow2_1.
      rewrite angle_div_2_pow_mul_2_pow.
      rewrite <- angle_mul_2_l.
      reflexivity.
    }
    apply angle_lim_const in Htt.
    symmetry in Htt.
    apply -> angle_sub_move_0_r in Htt.
    rewrite <- Htt.
    apply angle_div_2_le_straight.
  }
  apply angle_add_not_overflow_diag.
  apply angle_le_iff in H.
  destruct H as [H| H]; [ easy | ].
  subst α.
  rewrite angle_straight_add_straight in Htt.
  apply angle_div_nat_0_l in Htt.
  exfalso; revert Htt.
  apply angle_straight_neq_0.
  congruence.
}
destruct n. {
(**)
  cbn.
  rewrite angle_add_0_r.
  rewrite angle_add_overflow_0_r; cbn.
  apply Nat.eq_add_0.
  specialize (exists_angle_div_nat Hch Har Hco π 3 (Nat.neq_succ_0 _)) as H1.
  destruct H1 as (π_3, Hp).
  assert (H : (α ≤ 2 * π_3)%A). {
    progress unfold angle_div_nat in Htt.
    progress unfold seq_angle_to_div_nat in Htt.
    apply angle_lim_move_0_r in Htt.
    apply angle_lim_opp in Htt.
    rewrite angle_opp_0 in Htt.
    eapply (angle_lim_eq_compat 0 0) in Htt. 2: {
      intros i.
      rewrite Nat.add_0_r.
      rewrite angle_opp_sub_distr.
      easy.
    }
    apply (angle_lim_0_le) with (g := λ i, (α /₂^ i)%A) in Htt. 2: {
      intros i.
      split. {
        rewrite fold_seq_angle_to_div_nat.
        progress unfold seq_angle_to_div_nat.
...
(*
i     2 ^ i / 3 * ((3 * α) /₂^i   α - ""
0     0                           α
1     0                           α
2     (3 * α / 4)                 α / 4
3     (3 * α / 4)                 α / 4
4     5 * (3 * α / 16)            α / 16
5     5 * (3 * α / 16)
6     21 * (3 * α / 64)           α / 64
7     21 * (3 * α / 64)
8     85 * (3 * α / 256)
9     85 * (3 * α / 256)
10    341 * (3 * α / 1024)
11    341 * (3 * α / 1024)
...
*)
... ...
  apply angle_le_iff in H.
  destruct H as [H| H]. {
    split; apply Nat_eq_b2n_0. {
      apply angle_add_not_overflow_diag.
      eapply (angle_lt_le_trans _); [ apply H | ].
      apply rngl_sin_nonneg_angle_le_straight.
      rewrite rngl_sin_mul_2_l.
(* possible, mais pas simple *)
...
    }
Search (angle_add_overflow _ (_ + _)).
(* ouais, c'est la merde *)
...
    now apply angle_lt_le_incl.
  }
  exfalso.
  subst α.
  rewrite angle_straight_add_straight in Htt.
  apply angle_div_nat_0_l in Htt.
  revert Htt.
  apply angle_straight_neq_0.
  congruence.
...
  assert (H : (α ≤ 2 * π_n)%A). {
      split. {
        Search (_ < _ - _)%A.
...
    eapply (angle_lim_eq_compat 1 0) in Htt. 2: {
      intros i.
      rewrite Nat.add_0_r.
      progress unfold seq_angle_to_div_nat.
      rewrite Nat.pow_add_r.
      rewrite Nat.pow_1_r.
...
      rewrite Nat.div_mul; [ | easy ].
      rewrite Nat.add_comm.
      rewrite angle_div_2_pow_add_r.
      rewrite angle_div_pow2_1.
      rewrite angle_div_2_pow_mul_2_pow.
      rewrite <- angle_mul_2_l.
      reflexivity.
    }
    apply angle_lim_const in Htt.
    symmetry in Htt.
    apply -> angle_sub_move_0_r in Htt.
    rewrite <- Htt.
    apply angle_div_2_le_straight.
...
  split. {
  apply Nat_eq_b2n_0.
  cbn in Htt.
  assert (H : (α ≤ π)%A). {
...
(**)
  eapply (angle_lim_eq_compat 0 0) in Htt. 2: {
    intros i.
    rewrite Nat.add_0_r.
    progress unfold seq_angle_to_div_nat.
Search ((_ + _) /₂^ _)%A.
Check angle_div_2_pow_mul.
...
    rewrite angle_div_2_pow_mul. 2: {
...
  apply angle_lim_move_0_r in Htt.
  apply angle_lim_opp in Htt.
  rewrite angle_opp_0 in Htt.
  eapply (angle_lim_eq_compat 0 0) in Htt. 2: {
    intros i.
    rewrite Nat.add_0_r.
    rewrite angle_opp_sub_distr.
    easy.
  }
  eapply (angle_lim_eq_compat (Nat.log2_up 3) 0) in Htt. 2: {
    intros.
    rewrite Nat.add_0_r.
    progress unfold seq_angle_to_div_nat.
...
    rewrite angle_div_2_pow_mul. 2: {

...
  eapply (angle_lim_0_le Hor) in Htt. 2: {
    intros i.
    progress unfold seq_angle_to_div_nat.
    replace ((3 * α) /₂^i)%A with (3 * (α /₂^i))%A.
rewrite (angle_div_2_pow_mul i 3) at 2.
...
    specialize (Nat.div_mod (2 ^ i) 3 (Nat.neq_succ_0 _)) as H1.
Search (_ ≤ 2 ^ Nat.log2_up _).
...
2 ^ i / 2 ^ Nat.log2_up n ≤ 2 ^ i / n

Search seq_angle_to_div_nat.
...
  eapply (angle_lim_eq_compat 0 0) in Htt. 2: {
    intros i.
    rewrite Nat.add_0_r.
    progress unfold seq_angle_to_div_nat.
...
    rewrite angle_0_div_2_pow.
    now rewrite angle_mul_0_r.
  }
...
  cbn in Htt |-*.
  rewrite angle_add_0_r in Htt |-*.
  rewrite angle_add_overflow_0_r; cbn.
  apply Nat.eq_add_0.
  split; apply Nat_eq_b2n_0. {
    progress unfold angle_div_nat in Htt.
...
    progress unfold seq_angle_to_div_nat in Htt.
    progress unfold angle_lim in Htt.
    progress unfold is_limit_when_seq_tends_to_inf in Htt.
...

Theorem exists_angle_div_nat :
  rngl_characteristic T = 0 →
  rngl_is_archimedean T = true →
  is_complete T rngl_dist →
  ∀ α n,
  n ≠ 0
  → ∃ α', (n * α')%A = α ∧ angle_mul_nat_div_2π n α' = 0.
Proof.
destruct_ac.
intros Hcz Har Hco * Hnz.
specialize (seq_angle_to_div_nat_is_Cauchy Har n α) as H1.
specialize (rngl_is_complete_angle_is_complete Hco) as H2.
specialize (H2 _ H1).
clear H1.
destruct H2 as (α', Ht).
rewrite fold_angle_div_nat in Ht.
exists α'.
specialize (angle_div_nat_prop Hcz Har Hco _ _ _ Ht) as H2.
split; [ now destruct H2 | ].
destruct H2 as [(H2, H3)| H2]; [ now subst n α' | ].
(**)
clear H2.
... ...
apply angle_div_nat_integral in Ht.
now destruct Ht.
...
rewrite <- H2 in Ht.
clear α H2.
rename α' into α.
Theorem glop :
  ∀ n α α',
  angle_div_nat α n α'
  → angle_mul_nat_div_2π n α' = 0.
Proof.
intros * Htt.
Search angle_div_nat.
progress unfold angle_div_nat in Htt.
... ...
now apply glop in Ht.
...
Print is_limit_when_seq_tends_to_inf.
Theorem glop {A} :
  ∀ (da : A → A → T) (P : A → Prop) u L,
  (∀ i, P (u i))
  → is_limit_when_seq_tends_to_inf da u L
  → P L.
Proof.
(* est-ce qu'il faut que ça soit continu, peut-être, euh ? *)
intros * Hp Hlim.
progress unfold is_limit_when_seq_tends_to_inf in Hlim.
...
Print seq_angle_to_div_nat.
Theorem glop :
  ∀ α n i, (seq_angle_to_div_nat α n i ≤ α)%A.
Search (seq_angle_to_div_nat _ _ _ ≤ _)%A.
seq_angle_to_div_nat_le_straight_div_pow2_log2_pred:
  ∀ {T : Type} {ro : ring_like_op T} {rp : ring_like_prop T} {rl : real_like_prop T} 
    {ac : angle_ctx T} (n i : nat) (α : angle T),
    n ≠ 1 → (seq_angle_to_div_nat α n i ≤ π /₂^(Nat.log2 n - 1))%A
...
eapply (glop angle_eucl_dist) with (L := α'); [ | apply Ht ].
intros i.
...
Search is_limit_when_seq_tends_to_inf.
progress unfold seq_angle_to_div_nat in Ht.
Print is_limit_when_seq_tends_to_inf.
...
Check is_limit_when_seq_tends_to_inf_eq_compat.
rewrite is_limit_when_seq_tends_to_inf_eq_compat in Ht.
...
...
progress unfold is_limit_when_seq_tends_to_inf in Ht.
remember (∀ ε, _ → ∃ N, ∀ i, _) as x; subst x.
Search (_ → angle_mul_nat_div_2π _ _ = _).
...
Qed.
*)

End a.
