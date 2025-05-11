Set Nested Proofs Allowed.
From Stdlib Require Import Utf8 Arith.

Require Import RingLike.Core.
Require Import RingLike.RealLike.
Require Import RingLike.Misc.

Require Import Angle TrigoWithoutPiExt.
Require Import Angle_order.
Require Import AngleDiv2.
Require Import AngleDiv2Add.
Require Import AngleAddLeMonoL.
Require Import AngleTypeIsComplete.
Require Import SeqAngleIsCauchy.
Require Import TacChangeAngle.

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
specialize (rngl_int_dom_or_inv_1_quo Hiv Hon) as Hii.
destruct (Nat.eq_dec (rngl_characteristic T) 1) as [Hc1| Hc1]. {
  specialize (rngl_characteristic_1 Hon Hos Hc1) as H1.
  intros.
  rewrite (H1 (_ * _))%L.
  apply H1.
}
intros * Ht21 Hzs1 Hzs2.
apply rngl_leb_le in Hzs1, Hzs2.
assert (H2r : √2 ≠ 0%L). {
  intros H.
  apply (f_equal rngl_squ) in H.
  rewrite (rngl_squ_sqrt Hon) in H. 2: {
    apply (rngl_0_le_2 Hon Hos Hor).
  }
  rewrite (rngl_squ_0 Hos) in H.
  now apply (rngl_2_neq_0 Hon Hos Hc1 Hor) in H.
}
rewrite (rl_sqrt_div Hon Hop Hiv Hor); cycle 1. {
  apply (rngl_le_0_sub Hop Hor).
  apply rngl_cos_bound.
} {
  apply (rngl_0_lt_2 Hon Hos Hc1 Hor).
}
rewrite (rl_sqrt_div Hon Hop Hiv Hor); cycle 1. {
  apply (rngl_le_opp_l Hop Hor).
  apply rngl_cos_bound.
} {
  apply (rngl_0_lt_2 Hon Hos Hc1 Hor).
}
rewrite (rl_sqrt_div Hon Hop Hiv Hor); cycle 1. {
  apply (rngl_le_opp_l Hop Hor).
  apply rngl_cos_bound.
} {
  apply (rngl_0_lt_2 Hon Hos Hc1 Hor).
}
rewrite (rl_sqrt_div Hon Hop Hiv Hor); cycle 1. {
  apply (rngl_le_0_sub Hop Hor).
  apply rngl_cos_bound.
} {
  apply (rngl_0_lt_2 Hon Hos Hc1 Hor).
}
do 2 rewrite (rngl_div_mul_mul_div Hic Hiv).
do 2 rewrite (rngl_mul_div_assoc Hiv).
rewrite (rngl_div_div Hos Hon Hiv); [ | easy | easy ].
rewrite (rngl_div_div Hos Hon Hiv); [ | easy | easy ].
rewrite fold_rngl_squ.
rewrite (rngl_squ_sqrt Hon). 2: {
  apply (rngl_0_le_2 Hon Hos Hor).
}
rewrite (rngl_mul_sub_distr_l Hop).
do 2 rewrite (rngl_mul_comm Hic 2).
rewrite (rngl_div_mul Hon Hiv). 2: {
  apply (rngl_2_neq_0 Hon Hos Hc1 Hor).
}
rewrite (rngl_div_mul Hon Hiv). 2: {
  apply (rngl_2_neq_0 Hon Hos Hc1 Hor).
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
change_angle_add_r θ1 angle_straight.
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
rewrite (rl_sqrt_squ Hon Hop Hor).
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
apply (rl_sqrt_le_rl_sqrt Hon Hop Hor Hii). {
  apply (rngl_mul_nonneg_nonneg Hos Hor).
  apply (rngl_le_0_sub Hop Hor), rngl_cos_bound.
  apply (rngl_le_0_sub Hop Hor), rngl_cos_bound.
}
apply (rngl_mul_le_compat_nonneg Hor). {
  split. {
    apply (rngl_le_0_sub Hop Hor), rngl_cos_bound.
  }
  rewrite <- (rngl_add_opp_r Hop).
  apply (rngl_add_le_mono_l Hop Hor).
  apply (rngl_opp_le_compat Hop Hor).
  now rewrite (rngl_opp_involutive Hop).
} {
  split. {
    apply (rngl_le_0_sub Hop Hor), rngl_cos_bound.
  }
  rewrite <- (rngl_add_opp_r Hop).
  now apply (rngl_add_le_mono_l Hop Hor).
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
specialize (rngl_int_dom_or_inv_1_quo Hiv Hon) as Hii.
destruct (Nat.eq_dec (rngl_characteristic T) 1) as [Hc1| Hc1]. {
  specialize (rngl_characteristic_1 Hon Hos Hc1) as H1.
  intros.
  rewrite (H1 (_ * _))%L.
  apply H1.
}
intros * Hs1z Hzs2.
apply (rngl_leb_gt Hor) in Hs1z.
apply rngl_leb_le in Hzs2.
assert (H2r : √2 ≠ 0%L). {
  intros H.
  apply (f_equal rngl_squ) in H.
  rewrite (rngl_squ_sqrt Hon) in H. 2: {
    apply (rngl_0_le_2 Hon Hos Hor).
  }
  rewrite (rngl_squ_0 Hos) in H.
  now apply (rngl_2_neq_0 Hon Hos Hc1 Hor) in H.
}
rewrite (rl_sqrt_div Hon Hop Hiv Hor); cycle 1. {
  apply (rngl_le_0_sub Hop Hor).
  apply rngl_cos_bound.
} {
  apply (rngl_0_lt_2 Hon Hos Hc1 Hor).
}
rewrite (rl_sqrt_div Hon Hop Hiv Hor); cycle 1. {
  apply (rngl_le_opp_l Hop Hor).
  apply rngl_cos_bound.
} {
  apply (rngl_0_lt_2 Hon Hos Hc1 Hor).
}
rewrite (rl_sqrt_div Hon Hop Hiv Hor); cycle 1. {
  apply (rngl_le_opp_l Hop Hor).
  apply rngl_cos_bound.
} {
  apply (rngl_0_lt_2 Hon Hos Hc1 Hor).
}
rewrite (rl_sqrt_div Hon Hop Hiv Hor); cycle 1. {
  apply (rngl_le_0_sub Hop Hor).
  apply rngl_cos_bound.
} {
  apply (rngl_0_lt_2 Hon Hos Hc1 Hor).
}
do 2 rewrite (rngl_div_mul_mul_div Hic Hiv).
do 2 rewrite (rngl_mul_div_assoc Hiv).
rewrite (rngl_div_div Hos Hon Hiv); [ | easy | easy ].
rewrite (rngl_div_div Hos Hon Hiv); [ | easy | easy ].
rewrite fold_rngl_squ.
rewrite (rngl_squ_sqrt Hon). 2: {
  apply (rngl_0_le_2 Hon Hos Hor).
}
rewrite rngl_mul_add_distr_l.
do 2 rewrite (rngl_mul_comm Hic 2).
rewrite (rngl_div_mul Hon Hiv). 2: {
  apply (rngl_2_neq_0 Hon Hos Hc1 Hor).
}
rewrite (rngl_div_mul Hon Hiv). 2: {
  apply (rngl_2_neq_0 Hon Hos Hc1 Hor).
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
change_angle_add_r θ1 angle_straight.
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
  rewrite (rngl_leb_0_opp Hop Hor) in Hs1z.
  apply (rngl_leb_gt Hor) in Hs1z.
  apply (rngl_lt_le_incl Hor) in Hs1z.
  apply rngl_leb_le in Hs1z.
  congruence.
}
rewrite (rl_sqrt_squ Hon Hop Hor).
rewrite (rngl_mul_comm Hic).
rewrite (rngl_mul_comm Hic (_ - _)).
apply (rngl_abs_nonneg_eq Hop Hor).
apply (rngl_add_nonneg_nonneg Hor).
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
  rewrite (rngl_mul_1_l Hon).
  destruct zs2. {
    rewrite (rngl_mul_1_l Hon).
    apply rngl_leb_le in Hzs1, Hzs2.
    now apply angle_eucl_dist_2_mul_sqrt_sub_sqrt.
  }
  exfalso.
  progress unfold angle_leb in Ht21.
  now rewrite Hzs1, Hzs2 in Ht21.
} {
  destruct zs2. {
    do 2 rewrite (rngl_mul_opp_l Hop).
    do 2 rewrite (rngl_mul_1_l Hon).
    rewrite (rngl_sub_opp_r Hop).
    apply (rngl_leb_gt Hor) in Hzs1.
    apply rngl_leb_le in Hzs2.
    now apply angle_eucl_dist_2_mul_sqrt_add_sqrt.
  }
  apply (rngl_leb_gt Hor) in Hzs1, Hzs2.
  change_angle_add_r θ1 angle_straight.
  change_angle_add_r θ2 angle_straight.
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
  do 2 rewrite (rngl_mul_1_l Hon).
  rewrite (rngl_mul_opp_r Hop).
  rewrite (rngl_sub_opp_r Hop).
  rewrite (rngl_add_opp_l Hop).
  generalize Hzs1; intros H1.
  generalize Hzs2; intros H2.
  apply (rngl_lt_le_incl Hor) in H1, H2.
  apply angle_eucl_dist_2_mul_sqrt_sub_sqrt; [ | easy | easy ].
  (* lemma *)
  progress unfold angle_leb in Ht21.
  do 2 rewrite rngl_sin_sub_straight_r in Ht21.
  do 2 rewrite rngl_cos_sub_straight_r in Ht21.
  progress unfold angle_leb.
  apply rngl_leb_le in H1, H2.
  rewrite H1, H2.
  apply (rngl_opp_neg_pos Hop Hor) in Hzs1, Hzs2.
  apply (rngl_leb_gt Hor) in Hzs1, Hzs2.
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
  rewrite (rngl_mul_inv_diag_l Hon Hiv) in H12. 2: {
    apply (rngl_2_neq_0 Hon Hos Hc1 Hor).
  }
  do 2 rewrite (rngl_mul_1_l Hon) in H12.
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
  rewrite (angle_mul_2_l angle_straight) in H12.
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
specialize (rngl_int_dom_or_inv_1_quo Hiv Hon) as Hii.
destruct (Nat.eq_dec (rngl_characteristic T) 1) as [Hc1| Hc1]. {
  specialize (rngl_characteristic_1 Hon Hos Hc1) as H1.
  intros.
  do 2 rewrite (H1 (angle_eucl_dist _ _)).
  do 2 rewrite (H1 (rngl_cos _)).
  easy.
}
intros.
rewrite <- (rngl_abs_nonneg_eq Hop Hor (angle_eucl_dist _ _)). 2: {
  apply (dist_nonneg Hon Hop Hiv Hor angle_eucl_dist_is_dist).
}
rewrite <- (rngl_abs_nonneg_eq Hop Hor (angle_eucl_dist θ1 _)). 2: {
  apply (dist_nonneg Hon Hop Hiv Hor angle_eucl_dist_is_dist).
}
rewrite angle_eucl_dist_move_0_r.
rewrite (angle_eucl_dist_move_0_r θ1).
do 2 rewrite rngl_cos_angle_eucl_dist_0_r.
split; intros H1. {
  apply (rngl_sub_le_mono_l Hop Hor) in H1.
  apply (rngl_div_le_mono_pos_r Hon Hop Hiv Hor Hii) in H1. 2: {
    apply (rngl_0_lt_2 Hon Hos Hc1 Hor).
  }
  now apply (rngl_squ_le_abs_le Hop Hor Hii) in H1.
} {
  apply (rngl_sub_le_mono_l Hop Hor).
  apply (rngl_div_le_mono_pos_r Hon Hop Hiv Hor Hii). {
    apply (rngl_0_lt_2 Hon Hos Hc1 Hor).
  }
  now apply (rngl_abs_le_squ_le Hop Hor).
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
  apply (rngl_lt_iff Hor).
  split. {
    apply (rngl_lt_le_incl Hor) in Htt.
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
    now apply (rngl_lt_irrefl Hor) in Htt.
  }
  apply angle_add_move_0_r in H.
  rewrite H in Htt.
  now apply (rngl_lt_irrefl Hor) in Htt.
} {
  apply (rngl_lt_iff Hor).
  split. {
    apply (rngl_lt_le_incl Hor) in Htt.
    now apply rngl_cos_le_iff_angle_eucl_le.
  }
  intros H.
  rewrite angle_eucl_dist_move_0_r in Htt.
  rewrite (angle_eucl_dist_move_0_r θ1) in Htt.
  apply rngl_cos_eq in H.
  destruct H; rewrite H in Htt. {
    now apply (rngl_lt_irrefl Hor) in Htt.
  }
  rewrite <- angle_eucl_dist_opp_opp in Htt.
  rewrite angle_opp_0 in Htt.
  now apply (rngl_lt_irrefl Hor) in Htt.
}
Qed.

Theorem angle_le_angle_eucl_dist_le :
  ∀ θ1 θ2,
  (θ1 ≤ angle_straight)%A
  → (θ2 ≤ angle_straight)%A
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
  specialize (limit_unique Hon Hop Hiv Hor angle_eucl_dist_is_dist) as H3.
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
specialize (rngl_int_dom_or_inv_1_quo Hiv Hon) as Hii.
destruct (Nat.eq_dec (rngl_characteristic T) 1) as [Hc1| Hc1]. {
  specialize (rngl_characteristic_1 Hon Hos Hc1) as H2.
  intros ε Hε.
  rewrite (H2 ε) in Hε.
  now apply (rngl_lt_irrefl Hor) in Hε.
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
      apply angle_mul_nat_overflow_div_pow2.
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
  apply angle_mul_nat_overflow_div_pow2.
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
    now apply (rngl_lt_le_incl Hor) in Hε.
  }
  now rewrite angle_sub_0_l.
}
now apply (exists_nat_such_that_rngl_cos_close_to_1 Har).
Qed.

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

End a.
