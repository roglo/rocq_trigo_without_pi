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

Definition angle_div_nat θ n θ' :=
  angle_lim (seq_angle_to_div_nat θ n) θ'.

Theorem angle_lim_eq_compat :
  ∀ a b f g θ,
  (∀ i, f (i + a) = g (i + b))
  → angle_lim f θ
  → angle_lim g θ.
Proof.
intros * Hfg Hf.
eapply is_limit_when_seq_tends_to_inf_eq_compat; [ apply Hfg | easy ].
Qed.

Theorem angle_lim_opp :
  ∀ f θ, angle_lim f θ → angle_lim (λ i, (- f i)%A) (- θ).
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
  ∀ f θ, angle_lim f θ ↔ angle_lim (λ i, (f i - θ)%A) 0%A.
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
  ∀ θ1 θ2,
  (θ2 ≤ θ1)%A
  → (0 ≤ rngl_sin θ1)%L
  → (0 ≤ rngl_sin θ2)%L
  → angle_eucl_dist θ1 θ2 =
    (2 *
     (√((1 - rngl_cos θ1) / 2) * √((1 + rngl_cos θ2) / 2) -
      √((1 + rngl_cos θ1) / 2) * √((1 - rngl_cos θ2) / 2)))%L.
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
change_angle_add_r θ1 π.
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
  ∀ θ1 θ2,
  (rngl_sin θ1 < 0)%L
  → (0 ≤ rngl_sin θ2)%L
  → angle_eucl_dist θ1 θ2 =
    (2 *
     (√((1 - rngl_cos θ1) / 2) * √((1 + rngl_cos θ2) / 2) +
      √((1 + rngl_cos θ1) / 2) * √((1 - rngl_cos θ2) / 2)))%L.
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
change_angle_add_r θ1 π.
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
  ∀ θ1 θ2,
  (θ2 ≤ θ1)%A
  → angle_eucl_dist θ1 θ2 = (2 * rngl_sin (θ1 /₂ - θ2 /₂))%L.
Proof.
destruct_ac.
intros * Ht21.
rewrite rngl_sin_sub.
cbn.
remember (rngl_cos θ1) as c1 eqn:Hco1.
remember (rngl_cos θ2) as c2 eqn:Hco2.
remember (rngl_sin θ1) as s1 eqn:Hsi1.
remember (rngl_sin θ2) as s2 eqn:Hsi2.
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
  change_angle_add_r θ1 π.
  change_angle_add_r θ2 π.
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
  ∀ θ1 θ2,
  angle_eucl_dist θ1 θ2 = (2 * rngl_sin ((θ1 - θ2) /₂))%L.
Proof.
destruct_ac.
intros.
rewrite angle_div_2_sub.
remember (θ2 ≤? θ1)%A as t21 eqn:Ht21.
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
  ∀ θ1 θ2 θ3 θ4,
  angle_eucl_dist θ1 θ2 = angle_eucl_dist θ3 θ4 ↔
  (θ1 + θ4 = θ2 + θ3 ∨ θ1 + θ3 = θ2 + θ4)%A.
Proof.
destruct_ac.
destruct (Nat.eq_dec (rngl_characteristic T) 1) as [Hc1| Hc1]. {
  specialize (rngl_characteristic_1_angle_0 Hc1) as H1.
  intros.
  rewrite angle_eucl_dist_move_0_r.
  rewrite (angle_eucl_dist_move_0_r θ3).
  rewrite (H1 (θ1 - θ2))%A.
  rewrite (H1 (θ3 - θ4))%A.
  rewrite (H1 (θ1 + θ4))%A.
  rewrite (H1 (θ2 + θ3))%A.
  rewrite (H1 (θ1 + θ3))%A.
  rewrite (H1 (θ2 + θ4))%A.
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
rewrite (angle_eucl_dist_move_0_r θ3).
destruct H12 as [H12| H12]. {
  apply angle_add_move_r in H12.
  subst θ1.
  rewrite angle_sub_sub_swap.
  rewrite angle_add_sub_swap.
  rewrite angle_sub_diag.
  now rewrite angle_add_0_l.
}
apply angle_add_move_r in H12.
subst θ1.
rewrite angle_sub_sub_swap.
rewrite angle_add_sub_swap.
rewrite angle_sub_diag.
rewrite angle_add_0_l.
rewrite <- angle_eucl_dist_opp_opp.
rewrite angle_opp_sub_distr.
now rewrite angle_opp_0.
Qed.

Theorem rngl_cos_le_iff_angle_eucl_le :
  ∀ θ1 θ2 θ3 θ4,
  (rngl_cos (θ1 - θ2) ≤ rngl_cos (θ3 - θ4)
   ↔ angle_eucl_dist θ3 θ4 ≤ angle_eucl_dist θ1 θ2)%L.
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
rewrite <- (rngl_abs_nonneg_eq Hop Hor (angle_eucl_dist θ1 _)). 2: {
  apply (dist_nonneg Hop Hiv Hto angle_eucl_dist_is_dist).
}
rewrite angle_eucl_dist_move_0_r.
rewrite (angle_eucl_dist_move_0_r θ1).
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
  ∀ θ1 θ2 θ3 θ4,
  (rngl_cos (θ1 - θ2) < rngl_cos (θ3 - θ4)
   ↔ angle_eucl_dist θ3 θ4 < angle_eucl_dist θ1 θ2)%L.
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
  rewrite (angle_eucl_dist_move_0_r θ1) in H.
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
  rewrite (angle_eucl_dist_move_0_r θ1) in Htt.
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
  ∀ θ1 θ2,
  (θ1 ≤ π)%A
  → (θ2 ≤ π)%A
  → (θ1 ≤ θ2)%A ↔ (angle_eucl_dist θ1 0 ≤ angle_eucl_dist θ2 0)%L.
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

(* to be completed later
Theorem angle_div_nat_prop :
  rngl_characteristic T = 0 →
  rngl_is_archimedean T = true →
  is_complete T rngl_dist →
  ∀ θ n θ',
  angle_div_nat θ n θ'
  → (n = 0 ∧ θ' = 0%A) ∨ (n * θ')%A = θ ∧ angle_mul_nat_div_2π n θ' = 0.
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
  apply angle_lim_const in Hdn; subst θ'.
  split; [ easy | cbn ].
  apply Nat_eq_b2n_0.
  apply angle_add_overflow_0_r.
}
progress unfold angle_div_nat in Hdn.
rename Hdn into Hlim.
specialize (angle_lim_mul n _ _ Hlim) as H1.
enough (H2 : angle_lim (λ i, (n * seq_angle_to_div_nat θ n i)%A) θ). {
  specialize (limit_unique Hop Hiv Hto angle_eucl_dist_is_dist) as H3.
  apply (H3 _ (n * θ')%A) in H2; [ clear H3 | easy ].
  split; [ easy | ].
...
}
clear θ' Hlim H1.
destruct (angle_eq_dec θ 0) as [Htz| Htz]. {
  subst θ.
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
eapply (angle_lim_eq_compat 0 0). {
  intros i.
  rewrite Nat.add_0_r; symmetry.
  progress unfold seq_angle_to_div_nat.
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
enough (H : angle_lim (λ i, (n * (θ /₂^i))%A) 0). {
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
(* lemma : angle_lim (angle_div_2_pow θ) 0 *)
intros ε Hε.
enough (H : ∃ N, ∀ m, N ≤ m → (1 - ε² / 2 < rngl_cos (θ /₂^m))%L). {
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
...
*)

Theorem angle_div_nat_prop :
  rngl_characteristic T = 0 →
  rngl_is_archimedean T = true →
  is_complete T rngl_dist →
  ∀ θ n θ',
  angle_div_nat θ n θ'
  → (n = 0 ∧ θ' = 0%A) ∨ (n * θ')%A = θ.
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
enough (H2 : angle_lim (λ i, (n * seq_angle_to_div_nat θ n i)%A) θ). {
  specialize (limit_unique Hop Hiv Hto angle_eucl_dist_is_dist) as H3.
  now apply (H3 _ (n * θ')%A) in H2.
}
clear θ' Hlim H1.
destruct (angle_eq_dec θ 0) as [Htz| Htz]. {
  subst θ.
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
eapply (angle_lim_eq_compat 0 0). {
  intros i.
  rewrite Nat.add_0_r; symmetry.
  progress unfold seq_angle_to_div_nat.
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
enough (H : angle_lim (λ i, (n * (θ /₂^i))%A) 0). {
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
(* lemma : angle_lim (angle_div_2_pow θ) 0 *)
intros ε Hε.
enough (H : ∃ N, ∀ m, N ≤ m → (1 - ε² / 2 < rngl_cos (θ /₂^m))%L). {
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

Theorem fold_angle_div_nat :
  ∀ n θ θ',
  is_limit_when_seq_tends_to_inf angle_eucl_dist
    (seq_angle_to_div_nat n θ) θ' =
  angle_div_nat n θ θ'.
Proof. easy. Qed.

(* to be completed later
Theorem angle_div_nat_integral :
  ∀ n θ θ',
  angle_div_nat θ n θ'
  → n = 0 ∨angle_mul_nat_div_2π n θ' = 0.
Proof.
intros * Htt.
destruct (Nat.eq_dec n 0) as [Hnz| Hnz]; [ now left | right ].
progress unfold angle_div_nat in Htt.
Search angle_div_nat.
...

Theorem exists_angle_div_nat :
  rngl_characteristic T = 0 →
  rngl_is_archimedean T = true →
  is_complete T rngl_dist →
  ∀ θ n,
  n ≠ 0
  → ∃ θ', (n * θ')%A = θ ∧ angle_mul_nat_div_2π n θ' = 0.
Proof.
destruct_ac.
intros Hcz Har Hco * Hnz.
specialize (seq_angle_to_div_nat_is_Cauchy Har n θ) as H1.
specialize (rngl_is_complete_angle_is_complete Hco) as H2.
specialize (H2 _ H1).
clear H1.
destruct H2 as (θ', Ht).
rewrite fold_angle_div_nat in Ht.
exists θ'.
specialize (angle_div_nat_prop Hcz Har Hco _ _ _ Ht) as H2.
split; [ now destruct H2 | ].
destruct H2 as [(H2, H3)| H2]; [ now subst n θ' | ].
(**)
clear H2.
... ...
apply angle_div_nat_integral in Ht.
now destruct Ht.
...
rewrite <- H2 in Ht.
clear θ H2.
rename θ' into θ.
Theorem glop :
  ∀ n θ θ',
  angle_div_nat θ n θ'
  → angle_mul_nat_div_2π n θ' = 0.
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
  ∀ θ n i, (seq_angle_to_div_nat θ n i ≤ θ)%A.
Search (seq_angle_to_div_nat _ _ _ ≤ _)%A.
seq_angle_to_div_nat_le_straight_div_pow2_log2_pred:
  ∀ {T : Type} {ro : ring_like_op T} {rp : ring_like_prop T} {rl : real_like_prop T} 
    {ac : angle_ctx T} (n i : nat) (θ : angle T),
    n ≠ 1 → (seq_angle_to_div_nat θ n i ≤ π /₂^(Nat.log2 n - 1))%A
...
eapply (glop angle_eucl_dist) with (L := θ'); [ | apply Ht ].
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

Theorem exists_angle_div_nat :
  rngl_characteristic T = 0 →
  rngl_is_archimedean T = true →
  is_complete T rngl_dist →
  ∀ θ n,
  n ≠ 0
  → ∃ θ', (n * θ')%A = θ.
Proof.
destruct_ac.
intros Hcz Har Hco * Hnz.
specialize (seq_angle_to_div_nat_is_Cauchy Har n θ) as H1.
specialize (rngl_is_complete_angle_is_complete Hco) as H2.
specialize (H2 _ H1).
destruct H2 as (θ', Ht).
exists θ'.
specialize (angle_div_nat_prop Hcz Har Hco _ _ _ Ht) as H2.
now destruct H2.
Qed.

Theorem angle_eq_mul_succ_nat_0_r :
  ∀ n θ,
  angle_add_overflow θ (n * θ) = false
  → (S n * θ)%A = 0%A
  → θ = 0%A.
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
  ∀ n θ,
  angle_mul_nat_div_2π n θ = 0
  → (n * θ = 0)%A
  → n = 0 ∨ θ = 0%A.
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
  ∀ θ1 θ2, (θ1 ≤ θ2)%A → (θ2 - θ1 ≤ θ2)%A.
Proof.
intros Hop Hto.
specialize (rngl_is_totally_ordered_is_ordered Hto) as Hor.
intros * H12.
progress unfold angle_leb in H12.
progress unfold angle_leb.
remember (0 ≤? rngl_sin θ1)%L as s1 eqn:Hs1.
remember (0 ≤? rngl_sin θ2)%L as s2 eqn:Hs2.
remember (0 ≤? rngl_sin (θ2 - θ1))%L as s12 eqn:Hs12.
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
  change_angle_add_r θ2 π.
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
change_angle_add_r θ1 π.
progress sin_cos_add_sub_straight_hyp T Hs1.
progress sin_cos_add_sub_straight_hyp T H12.
progress sin_cos_add_sub_straight_hyp T Hs12.
rewrite angle_sub_sub_distr.
progress sin_cos_add_sub_straight_goal T.
change_angle_add_r θ2 π.
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
  ∀ n θ1 θ2,
  (θ1 ≤ θ2)%A
  → angle_mul_nat_div_2π n θ2 = 0
  → (n * θ1 = n * θ2)%A
  → n ≠ 0
  → θ1 = θ2.
Proof.
destruct_ac.
intros * H12 Hn2 Ht Hnz.
symmetry.
apply angle_sub_move_0_r.
enough (H : n = 0 ∨ (θ2 - θ1 = 0)%A) by now destruct H.
apply angle_mul_nat_integral. {
  apply (angle_mul_nat_div_2π_le_r _ θ2); [ | easy ].
  now apply (angle_le_le_sub_l Hop Hto).
}
rewrite angle_mul_sub_distr_l, Ht.
apply angle_sub_diag.
Qed.

Theorem angle_eq_mul_nat_cancel_l :
  ∀ n θ1 θ2,
  angle_mul_nat_div_2π n θ1 = 0
  → angle_mul_nat_div_2π n θ2 = 0
  → (n * θ1 = n * θ2)%A
  → n ≠ 0
  → θ1 = θ2.
Proof.
destruct_ac.
intros * Hn1 Hn2 Ht Hnz.
destruct (angle_le_dec θ1 θ2) as [H12| H12]. {
  now apply (angle_eq_mul_nat_cancel_l_le n).
} {
  apply angle_nle_gt, angle_lt_le_incl in H12.
  symmetry.
  now apply (angle_eq_mul_nat_cancel_l_le n).
}
Qed.

Theorem angle_add_not_overflow_iff :
  ∀ θ1 θ2,
  angle_add_overflow θ1 θ2 = false
  ↔ (θ1 = 0)%A ∨ (θ2 < - θ1)%A.
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
    now subst θ1; rewrite angle_eqb_refl.
  } {
    now apply angle_leb_gt.
  }
}
Qed.

Theorem angle_mul_nat_div_2π_iff :
  ∀ n θ k,
  angle_mul_nat_div_2π n θ = k
  ↔ (∀ i, i < n → angle_mul_nat_div_2π i θ ≤ k) ∧
    (if Nat.eq_dec n 0 then k = 0
     else if Nat.eq_dec k 0 then
       ∀ i, i < n → angle_add_overflow θ (i * θ) = false
     else
       ∃ i, i < n ∧ angle_mul_nat_div_2π i θ = k - 1 ∧
       angle_add_overflow θ (i * θ) = true ∧
       ∀ j, i < j < n → angle_add_overflow θ (j * θ) = false).
Proof.
intros.
revert k.
induction n; intros; [ easy | ].
cbn - [ angle_mul_nat_div_2π ].
split; intros H1. {
  split. {
    intros i Hi.
    cbn in H1.
    remember (angle_add_overflow θ (n * θ)) as ov eqn:Hov.
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
  destruct (Nat.eq_dec (angle_mul_nat_div_2π n θ) 0) as [Hmz| Hmz]. {
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
    now destruct (angle_add_overflow θ (n * θ)).
  }
  destruct H3 as (i & Hin & Haa & Hov & H3).
  remember (angle_add_overflow θ (n * θ)) as ov eqn:Hovn.
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
remember (angle_add_overflow θ (n * θ)) as ov eqn:Hovn.
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

(* to be completed later
Theorem glop :
  rngl_has_opp T = true →
  rngl_is_totally_ordered T = true →
  ∀ n θ,
  angle_div_nat (n * θ) n θ
  → angle_mul_nat_div_2π n θ = 0.
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
  destruct (angle_eq_dec θ 0) as [Htz| Htz]; [ now left | right ].
...
Theorem angle_mul_nat_div_2π_le :
  ∀ n θ k, k ≤ n → angle_mul_nat_div_2π k θ ≤ angle_mul_nat_div_2π n θ.
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
remember (angle_add_overflow θ (k * θ)) as ovk eqn:Hk.
remember (angle_add_overflow θ (n * θ)) as ovn eqn:Hn.
symmetry in Hk, Hn.
destruct ovk; [ cbn | easy ].
destruct ovn; [ easy | cbn ].
exfalso.
apply Bool.not_false_iff_true in Hk.
apply Hk; clear Hk.
apply (angle_add_overflow_le _ (n * θ)); [ | easy ].
apply angle_mul_le_mono_r; [ | easy ].
(*
clear k IHn Hkn.
*)
(* lemma *)
apply angle_add_not_overflow_iff in Hn.
destruct Hn as [Hn| Hn]; [ subst; apply angle_mul_nat_div_2π_0_r | ].
...
(*
  Hn : (n * θ < - θ)%A
  ============================
  angle_mul_nat_div_2π n θ = 0
*)
...
induction n; [ easy | ].
assert (H : (n * θ < - θ)%A). {
...
  eapply angle_le_lt_trans; [ | apply Hn ].
  apply angle_mul_le_mono_r; [ | flia ].
assert (angle_mul_nat_div_2π (S n) θ = angle_mul_nat_div_2π n θ). {
  cbn.
  replace (angle_add_overflow _ _) with false.
  apply Nat.add_0_r.
  symmetry.
  apply angle_add_not_overflow_iff.
  (* crotte de bique *)
...
angle_mul_nat_div_2π b θ = 0 est une condition suffisante, mais
elle n'est pas nécessaire. Il faudrait affiner :

angle_mul_le_mono_r
     : ∀ (a b : nat) (θ : angle T), angle_mul_nat_div_2π b θ = 0 → a ≤ b → (a * θ ≤ b * θ)%A
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
  apply (angle_add_overflow_le _ (S n * θ)); [ | easy ].
  cbn.
  rewrite angle_add_comm.
  rewrite <- angle_add_0_r at 1.
Search (_ ≤ _ + _)%A.
  apply angle_add_le_mono_l.
...
  apply angle_le_add_r.
... ...
          specialize (angle_mul_nat_div_2π_le n θ i) as H4.
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
  destruct (angle_eq_dec θ 0) as [Htz| Htz]; [ now left | right ].
  progress unfold angle_ltb; cbn.
  rewrite (rngl_leb_0_opp Hop Hto).
  remember (0 ≤? rngl_sin (n * θ))%L as zsn eqn:Hzsn.
  remember (rngl_sin θ ≤? 0)%L as sz eqn:Hsz.
  symmetry in Hzsn, Hsz.
  destruct zsn. {
    destruct sz; [ | easy ].
    apply rngl_leb_le in Hzsn, Hsz.
    apply (rngl_ltb_lt Heo).
    change_angle_add_r θ π.
    progress sin_cos_add_sub_straight_hyp T Hsz.
    progress sin_cos_add_sub_straight_goal T.
    rewrite angle_mul_sub_distr_l in Hzsn |-*.
    destruct (Nat.Even_Odd_dec n) as [Hn| Hn]. {
      apply Nat.Even_EvenT in Hn.
      destruct Hn as (m, Hn).
      subst n; rename m into n; move n after θ.
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
  ∀ θ n θ',
  angle_div_nat θ n θ'
  → angle_mul_nat_div_2π n θ' = 0.
Proof.
intros Hch Har Hco * Htt.
generalize Htt; intros H.
apply (angle_div_nat_prop Hch Har Hco) in H.
destruct H as [(Hn, Ht)| Hntt]; [ now subst | ].
subst θ; rename θ' into θ.
... ...
now apply glop.
...
*)

Theorem angle_lim_le_compat :
  ∀ f g,
  (∀ i, (g i ≤ f i ≤ π)%A)
  → angle_lim f 0
  → angle_lim g 0.
Proof.
destruct_ac.
intros * Hgf Hf.
intros ε Hε.
specialize (Hf ε Hε).
destruct Hf as (N, Hf).
exists N.
intros n Hn.
specialize (Hf n Hn).
eapply (rngl_le_lt_trans Hor); [ | apply Hf ].
apply angle_le_angle_eucl_dist_le; [ | | apply Hgf ]. {
  apply (angle_le_trans _ (f n)); apply Hgf.
}
apply Hgf.
Qed.

(* to be completed
Theorem angle_mul_div_nat :
  rngl_characteristic T = 0 →
  rngl_is_archimedean T = true →
  is_complete T rngl_dist →
  ∀ θ n,
  n ≠ 0
  → angle_mul_nat_div_2π n θ = 0
  → angle_div_nat (n * θ) n θ.
Proof.
destruct_ac.
intros Hch Har Hco * Hnz Hmn.
specialize (rngl_is_complete_angle_is_complete Hco) as H1.
specialize (seq_angle_to_div_nat_is_Cauchy Har n (n * θ)) as H.
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
move Hn1 before Hnz.
destruct H1 as (θ', Ht).
progress unfold angle_div_nat.
progress unfold angle_lim.
specialize (angle_div_nat_prop Hch Har Hco) as H2.
specialize (H2 (n * θ)%A n θ').
specialize (H2 Ht).
destruct H2 as [H2| H2]; [ easy | ].
(**)
rewrite fold_angle_div_nat in Ht |-*.
(*
intros ε Hε.
specialize (Ht ε Hε).
destruct Ht as (N, Ht).
exists N; intros m Hm.
specialize (Ht m Hm).
progress unfold seq_angle_to_div_nat in Ht.
progress unfold seq_angle_to_div_nat.
(* ttt... non, ça a pas trop l'air de le faire... *)
*)
destruct (angle_le_dec θ' θ) as [Htt| Htt]. {
  apply angle_eq_mul_nat_cancel_l_le in H2; [ | easy | easy | easy ].
  now subst θ'.
}
apply angle_nle_gt in Htt.
progress unfold angle_div_nat in Ht.
progress unfold angle_div_nat.
apply angle_lim_move_0_r in Ht.
apply angle_lim_move_0_r.
apply angle_lim_opp in Ht.
rewrite angle_opp_0 in Ht.
progress unfold seq_angle_to_div_nat.
eapply (angle_lim_eq_compat 0 0). {
  intros i.
  rewrite Nat.add_0_r.
  symmetry.
  rewrite angle_div_2_pow_mul; [ | easy ].
  rewrite angle_mul_nat_assoc.
  rewrite Nat.mul_comm.
  rewrite <- (angle_div_2_pow_mul_2_pow i θ) at 2.
  rewrite <- angle_opp_sub_distr.
  rewrite <- angle_mul_sub_distr_r; [ | apply Nat.Div0.mul_div_le ].
  rewrite <- Nat.Div0.mod_eq.
  reflexivity.
}
rewrite <- angle_opp_0.
apply angle_lim_opp.
remember (Nat.log2_up n) as k eqn:Hk.
eapply (angle_lim_eq_compat 0 k). {
  intros.
  rewrite Nat.add_0_r; symmetry.
  easy.
}
apply angle_lim_le_compat with (f := λ i, (n * (θ /₂^(i + k)))%A). {
  intros i.
  split. {
    apply (angle_le_trans _ (n * (θ /₂^ (i + k)))). {
      apply angle_mul_le_mono_r. 2: {
        apply Nat.lt_le_incl.
        now apply Nat.mod_upper_bound.
      }
      apply angle_mul_nat_div_2π_div_pow2.
      rewrite Nat.pow_add_r.
      subst k.
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
  rewrite angle_div_2_pow_add_r.
Search (_ /₂^Nat.log2_up _)%A.
...
}
...
Search angle_mul_nat_div_2π.
angle_mul_nat_integral:
  ∀ (n : nat) (θ : angle T),
    angle_mul_nat_div_2π n θ = 0 → (n * θ)%A = 0%A → n = 0 ∨ θ = 0%A
...
Search (_ * _ = _ * _)%A.
(* n=2 θ=π/2 θ'=3π/2 *)
(* ah non, ce contre-exemple ne fonctionne pas avec Ht *)
(* chercher d'autres contre exemples, peut-être *)
(**)
...
assert (θ = θ'). {
  apply (angle_eq_mul_nat_cancel_l n); [ easy | | easy | easy ].
  destruct (angle_le_dec θ' θ) as [Htt| Htt]. {
    now apply (angle_mul_nat_div_2π_le_r _ θ).
  }
  apply angle_nle_gt in Htt.
Search (_ < _ * _)%A.
...
Theorem angle_mul_nat_div_2π_add_r :
  ∀ n θ1 θ2,
  angle_add_overflow θ1 θ2 = false
  → angle_mul_nat_div_2π n (θ1 + θ2) = 0
  → angle_mul_nat_div_2π n θ2 = 0.
Proof.
intros * Hov H12.
apply angle_add_overflow_if in Hov.
destruct Hov as [Hov| Hov]. {
  now rewrite Hov, angle_add_0_l in H12.
}
induction n; [ easy | ].
cbn.
rewrite IHn; [ | now apply Nat.eq_add_0 in H12 ].
apply Nat_eq_b2n_0.
...
 (IHn H1), Nat.add_0_l.
apply Nat.eq_add_0 in H12.
destruct H12 as (H1, H2).
rewrite (IHn H1), Nat.add_0_l.
apply Nat_eq_b2n_0.
apply angle_mul_nat_div_2π_succ_l_false.
...
intros * Hov H12.
induction n; [ easy | cbn ].
cbn in H12.
apply Nat.eq_add_0 in H12.
destruct H12 as (H1, H2).
apply Nat_eq_b2n_0 in H2.
apply angle_eq_mul_succ_nat_0_r in H2. 2: {
...
intros * Hov H12.
induction n; [ easy | cbn ].
cbn in H12.
apply Nat.eq_add_0 in H12.
apply Nat.eq_add_0.
destruct H12 as (H1, H2).
split; [ now apply IHn | ].
apply Nat_eq_b2n_0 in H2.
apply Nat_eq_b2n_0.
rewrite <- angle_mul_1_l at 1.
apply angle_mul_nat_div_2π_distr_add_overflow.
cbn.
rewrite IHn. {
  apply Nat_eq_b2n_0.
... ...
  now apply angle_mul_nat_div_2π_add_r in H3.
...
  apply angle_eq_mul_succ_nat_0_r in H4. 2: {
    rewrite angle_mul_add_distr_l.
    rewrite Hnn, angle_add_0_r.
    apply angle_mul_nat_integral in Hnn. 2: {
      cbn.
      rewrite H2.

...
specialize (IHn H1 H3).
rewrite IHn; cbn.
rewrite angle_mul_add_distr_l in H4.
...
apply angle_eq_mul_succ_nat_0_r in H2. 2: {
Search (_ * _ = 0)%A.
...
Search (angle_add_overflow _ (_ + _)).
...
rewrite angle_add_overflow_comm in H2 |-*.
eapply AngleAddOverflowLe.angle_add_overflow_le; [ | ].
...
intros * Hnz Hn1 Hn2 Hnn H12.
induction n; intros; [ easy | clear Hnz ].
destruct (Nat.eq_dec n 0) as [Hnz| Hnz]. {
  now subst n; do 2 rewrite angle_mul_1_l in Hnn.
}
apply (IHn Hnz).
now apply Nat.eq_add_0 in Hn1.
now apply Nat.eq_add_0 in Hn2.
clear IHn.
...
intros * Hnz Hn1 Hn2 Hnn H12.
revert θ1 θ2 Hn1 Hn2 Hnn H12.
induction n; intros; [ easy | clear Hnz ].
destruct (Nat.eq_dec n 0) as [Hnz| Hnz]. {
  now subst n; do 2 rewrite angle_mul_1_l in Hnn.
}
specialize (IHn Hnz).
cbn in Hn1, Hn2.
apply Nat.eq_add_0 in Hn1, Hn2.
destruct Hn1 as (Ha1, Ho1).
destruct Hn2 as (Ha2, Ho2).
move Ha2 before Ha1.
apply Nat_eq_b2n_0 in Ho1, Ho2.
apply IHn; [ easy | easy | | easy ].
cbn in Hnn.
apply angle_add_move_l in Hnn.
rewrite angle_add_sub_swap in Hnn.
symmetry in Hnn.
apply angle_add_move_r in Hnn.
rewrite <- angle_mul_sub_distr_l in Hnn.
rewrite <- angle_opp_sub_distr in Hnn.
symmetry in Hnn.
apply angle_add_move_0_r in Hnn.
rewrite <- (angle_mul_1_l (θ1 - θ2)) in Hnn at 2.
rewrite <- angle_mul_add_distr_r in Hnn.
rewrite Nat.add_1_r in Hnn.
... ...
apply (angle_mul_nat_cancel_l n); [ easy | easy | | easy ].
...
rewrite <- angle_opp_involutive in Hnn.
apply angle_add_move_0_r in Hnn.
rewrite angle_add_opp_r in Hnn.
rewrite <- angle_mul_sub_distr_l in Hnn.
...
Search (angle_mul_nat_div_2π _ (_ + _)).
(*
contre exemple :
  2 x π = 0
*)
...
intros * Hnz Hnn.
induction n; intros; [ easy | clear Hnz ].
destruct (Nat.eq_dec n 0) as [Hnz| Hnz]. {
  now subst n; do 2 rewrite angle_mul_1_l in Hnn.
}
apply (IHn Hnz).
cbn in Hnn.
apply angle_add_move_l in Hnn.
rewrite angle_add_sub_swap in Hnn.
symmetry in Hnn.
apply angle_add_move_r in Hnn.
rewrite <- angle_mul_sub_distr_l in Hnn.
rewrite <- angle_opp_sub_distr in Hnn.
symmetry in Hnn.
apply angle_add_move_0_r in Hnn.
rewrite <- (angle_mul_1_l (θ1 - θ2)) in Hnn at 2.
rewrite <- angle_mul_add_distr_r in Hnn.
rewrite Nat.add_1_r in Hnn.
...
Search (_ * _ = 0)%A.
Require Import AngleAddLeMonoL_1.
Require Import AngleAddLeMonoL_2.
Require Import AngleAddLeMonoL_3.
Require Import AngleAddLeMonoL_prop.
Require Import AngleAddLeMonoL.
Require Import AngleAddOverflowEquiv.
Require Import AngleAddOverflowLe.
Require Import AngleDef.
Require Import AngleDiv2Add.
Require Import AngleDiv2.
Require Import AngleTypeIsComplete.
Require Import Angle.
Require Import Distance.
Require Import Order.
Require Import SeqAngleIsCauchy.
Require Import TacChangeAngle.
Require Import TrigoWithoutPiExt.
Search (_ * _ = 0)%A.
Search (_ + _)%A.
angle_add_move_l:
  ∀ {T : Type} {ro : ring_like_op T} {rp : ring_like_prop T} 
    {ac : angle_ctx T} (θ1 θ2 θ3 : angle T),
    (θ1 + θ2)%A = θ3 ↔ θ2 = (θ3 - θ1)%A
Search (rngl_sin (_ * _)).
...
  now apply (angle_mul_nat_cancel_l n _ _ Hnz).
...
  clear Hmn H1 Ht.
  revert θ θ' H2.
  induction n; intros; [ easy | clear Hnz ].
  destruct (Nat.eq_dec n 0) as [Hnz| Hnz]. {
    now subst n; do 2 rewrite angle_mul_1_l in H2.
  }
  apply IHn; [ easy | ].
..
apply angle_mul_nat_cancel_l in H2.
...
exists θ'.
specialize (angle_div_nat_prop Hcz Har Hco _ _ _ Ht) as H2.
now destruct H2.
...
intros Hch Har Hco * Hnz Hmn.
progress unfold angle_div_nat.
progress unfold seq_angle_to_div_nat.
eapply (angle_lim_eq_compat 0 0). {
  intros i.
  rewrite Nat.add_0_r.
  symmetry.
  rewrite angle_div_2_pow_mul; [ | easy ].
  rewrite angle_mul_nat_assoc.
  rewrite Nat.mul_comm.
  rewrite <- angle_mul_nat_assoc.
  easy.
}
specialize (exists_angle_div_nat Hch Har Hco) as H1.
specialize (H1 θ n Hnz).
destruct H1 as (θ', Ht).
rewrite <- Ht.
apply angle_lim_mul.
...
Inspect 5.
Search angle_lim.
Theorem glop :
  ∀ f a θ θ',
  angle_lim f θ
  → θ' = (a * θ)%A
  → angle_lim (λ i, (a * f i)%A) θ'.
Admitted.
eapply glop.
(* bof... *)
...
  clear Hnz.
  revert i.
  induction n; intros; [ easy | ].
  apply (angle_mul_nat_not_overflow_le_l _ (S n)); [ | easy ].
  cbn in Hmn.
  apply Nat.eq_add_0 in Hmn.
  destruct Hmn as (H1, H2).
  specialize (IHn H1).
...
  rewrite Nat.pow_add_r.
Search (2 ^ Nat.log2 _).
...
Search angle_mul_nat_div_2π.
...
}
Search angle_lim.
...
intros Hch Har Hco * Hnz Hmn.
intros ε Hε.
progress unfold seq_angle_to_div_nat.
remember (∃ N : nat, ∀ i : nat, _) as P; subst P.
(**)
enough (H :
  ∃ N, ∀ i, N ≤ i →
  (angle_eucl_dist (2 ^ i / n * n * (θ /₂^i)) θ < ε)%L). {
  destruct H as (N, H).
  exists N.
  intros i Hi.
  specialize (H i Hi).
  rewrite angle_div_2_pow_mul; [ | easy ].
  now rewrite angle_mul_nat_assoc.
}
...
induction n; [ easy | clear Hnz ].
destruct (Nat.eq_dec n 0) as [Hnz| Hnz]. {
  subst n.
  exists 0.
  intros i _.
  rewrite Nat.div_1_r.
  rewrite angle_mul_1_l.
  rewrite angle_div_2_pow_mul_2_pow.
  now rewrite angle_eucl_dist_diag.
}
specialize (IHn Hnz).
cbn in Hmn.
apply Nat.eq_add_0 in Hmn.
destruct Hmn as (H1, H2).
apply Nat_eq_b2n_0 in H2.
specialize (IHn H1).
destruct IHn as (N, H3).
remember (∃ M : nat, ∀ i : nat, _) as P; subst P.
...
*)

End a.
