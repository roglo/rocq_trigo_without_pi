Set Nested Proofs Allowed.
From Stdlib Require Import Utf8 Arith.

Require Import RingLike.Core.
Require Import RingLike.RealLike.
Require Import RingLike.Misc.

Require Import AngleDef Angle TrigoWithoutPiExt.
Require Import Angle_order.
Require Import AngleDiv2.
Require Import AngleDiv2Add.
Require Import AngleAddLeMonoL.
Require Import AngleTypeIsComplete.
Require Import Distance.
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
    apply (rngl_0_le_2 Hon Hos Hiq Hor).
  }
  rewrite (rngl_squ_0 Hos) in H.
  now apply (rngl_2_neq_0 Hon Hos Hiq Hc1 Hor) in H.
}
rewrite (rl_sqrt_div Hon Hop Hiv Hor); cycle 1. {
  apply (rngl_le_0_sub Hop Hor).
  apply rngl_cos_bound.
} {
  apply (rngl_0_lt_2 Hon Hos Hiq Hc1 Hor).
}
rewrite (rl_sqrt_div Hon Hop Hiv Hor); cycle 1. {
  apply (rngl_le_opp_l Hop Hor).
  apply rngl_cos_bound.
} {
  apply (rngl_0_lt_2 Hon Hos Hiq Hc1 Hor).
}
rewrite (rl_sqrt_div Hon Hop Hiv Hor); cycle 1. {
  apply (rngl_le_opp_l Hop Hor).
  apply rngl_cos_bound.
} {
  apply (rngl_0_lt_2 Hon Hos Hiq Hc1 Hor).
}
rewrite (rl_sqrt_div Hon Hop Hiv Hor); cycle 1. {
  apply (rngl_le_0_sub Hop Hor).
  apply rngl_cos_bound.
} {
  apply (rngl_0_lt_2 Hon Hos Hiq Hc1 Hor).
}
do 2 rewrite (rngl_div_mul_mul_div Hic Hiv).
do 2 rewrite (rngl_mul_div_assoc Hiv).
rewrite (rngl_div_div Hon Hos Hiv); [ | easy | easy ].
rewrite (rngl_div_div Hon Hos Hiv); [ | easy | easy ].
rewrite fold_rngl_squ.
rewrite (rngl_squ_sqrt Hon). 2: {
  apply (rngl_0_le_2 Hon Hos Hiq Hor).
}
rewrite (rngl_mul_sub_distr_l Hop).
do 2 rewrite (rngl_mul_comm Hic 2).
rewrite (rngl_div_mul Hon Hiv). 2: {
  apply (rngl_2_neq_0 Hon Hos Hiq Hc1 Hor).
}
rewrite (rngl_div_mul Hon Hiv). 2: {
  apply (rngl_2_neq_0 Hon Hos Hiq Hc1 Hor).
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
apply (rl_sqrt_le_rl_sqrt Hon Hop Hiq Hor). {
  apply (rngl_mul_nonneg_nonneg Hon Hos Hiq Hor).
  apply (rngl_le_0_sub Hop Hor), rngl_cos_bound.
  apply (rngl_le_0_sub Hop Hor), rngl_cos_bound.
}
apply (rngl_mul_le_compat_nonneg Hon Hiq Hor). {
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
    apply (rngl_0_le_2 Hon Hos Hiq Hor).
  }
  rewrite (rngl_squ_0 Hos) in H.
  now apply (rngl_2_neq_0 Hon Hos Hiq Hc1 Hor) in H.
}
rewrite (rl_sqrt_div Hon Hop Hiv Hor); cycle 1. {
  apply (rngl_le_0_sub Hop Hor).
  apply rngl_cos_bound.
} {
  apply (rngl_0_lt_2 Hon Hos Hiq Hc1 Hor).
}
rewrite (rl_sqrt_div Hon Hop Hiv Hor); cycle 1. {
  apply (rngl_le_opp_l Hop Hor).
  apply rngl_cos_bound.
} {
  apply (rngl_0_lt_2 Hon Hos Hiq Hc1 Hor).
}
rewrite (rl_sqrt_div Hon Hop Hiv Hor); cycle 1. {
  apply (rngl_le_opp_l Hop Hor).
  apply rngl_cos_bound.
} {
  apply (rngl_0_lt_2 Hon Hos Hiq Hc1 Hor).
}
rewrite (rl_sqrt_div Hon Hop Hiv Hor); cycle 1. {
  apply (rngl_le_0_sub Hop Hor).
  apply rngl_cos_bound.
} {
  apply (rngl_0_lt_2 Hon Hos Hiq Hc1 Hor).
}
do 2 rewrite (rngl_div_mul_mul_div Hic Hiv).
do 2 rewrite (rngl_mul_div_assoc Hiv).
rewrite (rngl_div_div Hon Hos Hiv); [ | easy | easy ].
rewrite (rngl_div_div Hon Hos Hiv); [ | easy | easy ].
rewrite fold_rngl_squ.
rewrite (rngl_squ_sqrt Hon). 2: {
  apply (rngl_0_le_2 Hon Hos Hiq Hor).
}
rewrite rngl_mul_add_distr_l.
do 2 rewrite (rngl_mul_comm Hic 2).
rewrite (rngl_div_mul Hon Hiv). 2: {
  apply (rngl_2_neq_0 Hon Hos Hiq Hc1 Hor).
}
rewrite (rngl_div_mul Hon Hiv). 2: {
  apply (rngl_2_neq_0 Hon Hos Hiq Hc1 Hor).
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
apply (rngl_le_0_add Hos Hor).
apply rl_sqrt_nonneg.
apply (rngl_mul_nonneg_nonneg Hon Hos Hiq Hor).
apply (rngl_le_opp_l Hop Hor), rngl_cos_bound.
apply (rngl_le_opp_l Hop Hor), rngl_cos_bound.
apply rl_sqrt_nonneg.
apply (rngl_mul_nonneg_nonneg Hon Hos Hiq Hor).
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
    apply (rngl_2_neq_0 Hon Hos Hiq Hc1 Hor).
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
  apply (rngl_div_le_mono_pos_r Hon Hop Hiv Hor) in H1. 2: {
    apply (rngl_0_lt_2 Hon Hos Hiq Hc1 Hor).
  }
  now apply (rngl_squ_le_abs_le Hon Hop Hiq Hor) in H1.
} {
  apply (rngl_sub_le_mono_l Hop Hor).
  apply (rngl_div_le_mono_pos_r Hon Hop Hiv Hor). {
    apply (rngl_0_lt_2 Hon Hos Hiq Hc1 Hor).
  }
  now apply (rngl_abs_le_squ_le Hon Hop Hiq Hor).
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
  apply (rngl_le_neq Hor).
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
  apply (rngl_le_neq Hor).
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

(*

Require Import AngleAddOverflowEquiv.

Definition angle_add_overflow1 θ1 θ2 :=
  if (θ1 =? 0)%A then false
  else if (θ2 =? 0)%A then false
  else if (0 <? rngl_sin θ1)%L then
    if (0 <? rngl_sin θ2)%L then false
    else (rngl_cos θ1 ≤? rngl_cos θ2)%L
  else
    if (0 <? rngl_sin θ2)%L then (rngl_cos θ2 ≤? rngl_cos θ1)%L
    else true.

Require Import Angle.
Require Import RingLike.RealLike.

Theorem angle_add_overflow_equiv1 :
  ∀ θ1 θ2, angle_add_overflow1 θ1 θ2 = angle_add_overflow θ1 θ2.
Proof.
destruct_ac.
intros.
progress unfold angle_add_overflow.
progress unfold angle_add_overflow1.
remember (θ1 =? 0)%A as t1z eqn:Ht1z.
remember (θ2 =? 0)%A as t2z eqn:Ht2z.
symmetry in Ht1z, Ht2z.
destruct t1z; [ easy | cbn ].
apply angle_eqb_neq in Ht1z.
destruct t2z. {
  apply angle_eqb_eq in Ht2z; subst θ2.
  symmetry.
  apply angle_leb_gt.
  apply angle_lt_iff.
  split; [ apply angle_nonneg | ].
  intros H; apply Ht1z; clear Ht1z.
  symmetry in H.
  apply (f_equal angle_opp) in H.
  rewrite angle_opp_involutive in H.
  now rewrite angle_opp_0 in H.
}
apply angle_eqb_neq in Ht2z.
progress unfold angle_leb.
cbn.
rewrite (rngl_leb_opp_r Hop Hor).
rewrite (rngl_opp_0 Hop).
remember (0 <? rngl_sin θ1)%L as zs1 eqn:Hzs1.
remember (rngl_sin θ1 ≤? 0)%L as s1z eqn:Hs1z.
symmetry in Hzs1, Hs1z.
remember (0 <? rngl_sin θ2)%L as zs2 eqn:Hzs2.
remember (0 ≤? rngl_sin θ2)%L as zse2 eqn:Hzse2.
symmetry in Hzs2, Hzse2.
destruct zs1. {
  apply rngl_ltb_lt in Hzs1.
  destruct s1z. {
    apply rngl_leb_le in Hs1z.
    now apply rngl_nlt_ge in Hs1z.
  }
  clear Hs1z.
  destruct zs2. {
    apply rngl_ltb_lt in Hzs2.
    destruct zse2; [ easy | ].
    apply (rngl_leb_gt Hor) in Hzse2.
    now apply (rngl_lt_asymm Hor) in Hzs2.
  }
  apply (rngl_ltb_ge_iff Hor) in Hzs2.
  destruct zse2; [ | easy ].
  apply rngl_leb_le in Hzse2.
  apply (rngl_le_antisymm Hor) in Hzse2; [ clear Hzs2 | easy ].
  apply eq_rngl_sin_0 in Hzse2.
  destruct Hzse2; [ easy | subst; cbn ].
  apply (rngl_leb_gt Hor).
  apply (rngl_le_neq Hor).
  split; [ apply rngl_cos_bound | ].
  intros H; symmetry in H.
  apply eq_rngl_cos_opp_1 in H; subst.
  now apply (rngl_lt_irrefl Hor) in Hzs1.
}
apply rngl_ltb_nlt in Hzs1.
destruct s1z; [ | now apply (rngl_leb_gt Hor) in Hs1z ].
apply rngl_leb_le in Hs1z.
destruct zs2. {
  destruct zse2; [ easy | ].
  apply rngl_ltb_lt in Hzs2.
  apply (rngl_leb_gt Hor) in Hzse2.
  now apply (rngl_lt_asymm Hor) in Hzs2.
}
symmetry.
destruct zse2; [ | easy ].
apply (rngl_ltb_ge_iff Hor) in Hzs2.
apply rngl_leb_le in Hzse2.
apply (rngl_le_antisymm Hor) in Hzse2; [ | easy ].
apply eq_rngl_sin_0 in Hzse2.
destruct Hzse2; [ easy | subst; cbn ].
apply rngl_leb_le, rngl_cos_bound.
Qed.

Theorem angle_add_overflow_assoc' :
  ∀ θ1 θ2 θ3,
  angle_add_overflow θ1 θ2 = angle_add_overflow θ2 θ3
  → angle_add_overflow (θ1 + θ2) θ3 = angle_add_overflow θ1 (θ2 + θ3).
Proof.
(**)
destruct_ac.
intros * H12.
remember (angle_add_overflow θ2 θ3) as ov eqn:H23.
symmetry in H23.
destruct ov. 2: {
  remember (angle_add_overflow (θ1 + θ2) θ3) as ov eqn:Hov.
  symmetry in Hov |-*.
  destruct ov; [ now apply angle_add_overflow_move_add | ].
  rewrite angle_add_comm.
  now apply angle_add_not_overflow_move_add.
}
(**)
rewrite <- angle_add_overflow_equiv2 in H12, H23.
do 2 rewrite <- angle_add_overflow_equiv2.
progress unfold angle_add_overflow2 in H12.
progress unfold angle_add_overflow2 in H23.
progress unfold angle_add_overflow2.
rewrite angle_add_assoc.
remember (θ1 + θ2 + θ3 <? θ1)%A as l123 eqn:H123.
symmetry in H123.
destruct l123. {
  progress unfold angle_ltb in H12.
  progress unfold angle_ltb in H23.
  progress unfold angle_ltb in H123.
  progress unfold angle_ltb.
  remember (0 ≤? rngl_sin (θ1 + θ2 + θ3))%L as z123 eqn:Hz123.
  symmetry in Hz123.
  destruct z123. {
    apply rngl_leb_le in Hz123.
    remember (0 ≤? rngl_sin (θ1 + θ2))%L as z12 eqn:Hz12.
    symmetry in Hz12.
    destruct z12. {
      apply rngl_leb_le in Hz12.
      remember (0 ≤? rngl_sin θ1)%L as zs1 eqn:Hzs1.
      symmetry in Hzs1.
      destruct zs1. {
        apply rngl_leb_le in Hzs1.
        apply rngl_ltb_lt in H12.
        apply rngl_ltb_lt in H123.
        apply rngl_ltb_lt.
        apply (rngl_nle_gt_iff Hor).
        intros Hc123.
        apply rngl_nle_gt in H12.
        apply H12; clear H12.
        remember (0 ≤? rngl_sin (θ2 + θ3))%L as zs23 eqn:Hzs23.
        remember (0 ≤? rngl_sin θ2)%L as zs2 eqn:Hzs2.
        symmetry in Hzs23, Hzs2.
        destruct zs23. {
          apply rngl_leb_le in Hzs23.
          destruct zs2. {
            apply rngl_leb_le in Hzs2.
            apply rngl_ltb_lt in H23.
            destruct (rngl_le_dec Hor 0 (rngl_cos θ1)) as [Hzc1| Hzc1]. {
              destruct (rngl_le_dec Hor 0 (rngl_cos θ2)) as [Hzc2| Hzc2]. {
                now apply quadrant_1_rngl_cos_add_le_cos_l.
              }
              apply (rngl_nle_gt_iff Hor) in Hzc2.
              apply rngl_cos_add_le_cos; [ | easy | easy | easy ].
              now right; right; left.
            }
            apply (rngl_nle_gt_iff Hor) in Hzc1.
            generalize Hzc1; intros H.
            apply (rngl_lt_le_incl Hor) in H.
            apply angle_add_overflow_le_lemma_2;
              [ | easy | easy | easy | easy ].
            clear H; intros H.
            apply eq_rngl_cos_opp_1 in H; subst θ1.
            rewrite rngl_sin_add_straight_l in Hz12.
            apply (rngl_opp_nonneg_nonpos Hop Hor) in Hz12.
            apply (rngl_le_antisymm Hor) in Hzs2; [ | easy ].
            clear Hzc1 Hzs1 Hz12.
            apply eq_rngl_sin_0 in Hzs2.
            destruct Hzs2; subst θ2. {
              apply rngl_nle_gt in H23.
              apply H23, rngl_cos_bound.
            }
            rewrite rngl_sin_add_straight_l in Hzs23.
            apply (rngl_opp_nonneg_nonpos Hop Hor) in Hzs23.
            rewrite rngl_cos_add_straight_l in H23.
            cbn in H23.
            rewrite angle_straight_add_straight in Hz123.
            rewrite angle_add_0_l in Hz123.
            apply (rngl_le_antisymm Hor) in Hz123; [ | easy ].
            clear Hzs23.
            apply eq_rngl_sin_0 in Hz123.
            destruct Hz123; subst θ3. {
              now apply (rngl_lt_irrefl Hor) in H23.
            }
            rewrite angle_straight_add_straight in H123.
            rewrite angle_add_0_l in H123.
            now apply (rngl_lt_irrefl Hor) in H123.
          }
          clear H23.
          apply (rngl_leb_gt Hor) in Hzs2.
          change_angle_sub_r θ2 angle_straight.
          rewrite angle_add_assoc in Hz12, Hc123, H123, Hz123 |-*.
          rewrite angle_add_add_swap in Hc123, H123, Hz123.
          progress sin_cos_add_sub_straight_hyp T Hz12.
          progress sin_cos_add_sub_straight_hyp T Hzs2.
          progress sin_cos_add_sub_straight_hyp T Hzs23.
          progress sin_cos_add_sub_straight_hyp T Hc123.
          progress sin_cos_add_sub_straight_hyp T H123.
          progress sin_cos_add_sub_straight_hyp T Hz123.
          progress sin_cos_add_sub_straight_goal T.
          rewrite (rngl_add_opp_l Hop) in Hc123.
          apply -> (rngl_le_sub_0 Hop Hor) in Hc123.
          apply (rngl_lt_opp_r Hop Hor) in H123.
          move Hzs1 after Hzs2.
          destruct (rngl_lt_dec Hor 0 (rngl_cos θ1)) as [Hzc1| Hzc1]. {
            destruct (rngl_le_dec Hor 0 (rngl_cos θ2)) as [Hzc2| Hzc2]. {
              apply (rngl_nlt_ge_iff Hor).
              intros Hc121.
              apply rngl_nlt_ge in Hz12.
              apply Hz12; clear Hz12.
              now apply rngl_sin_add_pos_1.
            }
            apply (rngl_nle_gt_iff Hor) in Hzc2.
(**)
            change_angle_sub_l θ2 angle_straight.
            progress sin_cos_add_sub_straight_hyp T Hz12.
            rewrite angle_add_sub_assoc in Hz123, H123, Hc123.
            rewrite angle_add_sub_swap in Hz123, H123, Hc123.
            progress sin_cos_add_sub_straight_hyp T Hz123.
            progress sin_cos_add_sub_straight_hyp T H123.
            progress sin_cos_add_sub_straight_hyp T Hc123.
            progress sin_cos_add_sub_straight_hyp T Hzs23.
            progress sin_cos_add_sub_straight_hyp T Hzs2.
            progress sin_cos_add_sub_straight_hyp T Hzc2.
            progress sin_cos_add_sub_straight_goal T.
            rewrite (rngl_add_opp_l Hop).
            apply (rngl_le_0_sub Hop Hor).
...
            change_angle_sub_r θ2 angle_right.
            progress sin_cos_add_sub_right_hyp T Hz12.
            progress sin_cos_add_sub_right_hyp T Hz123.
            progress sin_cos_add_sub_right_hyp T H123.
            progress sin_cos_add_sub_right_hyp T Hc123.
            progress sin_cos_add_sub_right_hyp T Hzs23.
            progress sin_cos_add_sub_right_hyp T Hzs2.
            progress sin_cos_add_sub_right_hyp T Hzc2.
            progress sin_cos_add_sub_right_goal T.
...
rewrite <- angle_add_overflow_equiv1 in H12, H23.
do 2 rewrite <- angle_add_overflow_equiv1.
progress unfold angle_add_overflow1 in H12.
progress unfold angle_add_overflow1 in H23.
progress unfold angle_add_overflow1.
remember (θ1 =? 0)%A as t1z eqn:Ht1z.
remember (θ2 =? 0)%A as t2z eqn:Ht2z.
remember (θ3 =? 0)%A as t3z eqn:Ht3z.
symmetry in Ht1z, Ht2z, Ht3z.
destruct t1z; [ easy | ].
destruct t2z; [ easy | ].
destruct t3z; [ easy | ].
move Ht1z after Ht2z.
remember (0 <? rngl_sin θ1)%L as zs1 eqn:Hzs1.
remember (0 <? rngl_sin θ2)%L as zs2 eqn:Hzs2.
remember (0 <? rngl_sin θ3)%L as zs3 eqn:Hzs3.
symmetry in Hzs1, Hzs2, Hzs3.
destruct zs1. {
  destruct zs2; [ easy | ].
  move Hzs1 after Hzs2.
  destruct zs3. {
    remember (θ1 + θ2 =? 0)%A as t12z eqn:Ht12z.
    remember (θ2 + θ3 =? 0)%A as t23z eqn:Ht23z.
    remember (0 <? rngl_sin (θ1 + θ2))%L as zs12 eqn:Hzs12.
    remember (0 <? rngl_sin (θ2 + θ3))%L as zs23 eqn:Hzs23.
    symmetry in Ht12z, Ht23z, Hzs12, Hzs23.
    destruct t12z. {
      destruct t23z; [ easy | ].
      destruct zs23; [ easy | symmetry ].
      apply angle_eqb_eq in Ht12z.
      apply angle_eqb_neq in Ht23z.
      apply angle_add_move_0_r in Ht12z; subst θ1.
      cbn in Hzs1.
      rewrite (rngl_ltb_opp_r Hop Hor) in Hzs1.
      rewrite (rngl_opp_0 Hop) in Hzs1.
clear Ht1z Hzs2 H12.
clear zs12 Hzs12.
rewrite rngl_cos_opp.
apply rngl_ltb_lt in Hzs1, Hzs3.
apply rngl_leb_le in H23.
apply (rngl_ltb_ge_iff Hor) in Hzs23.
apply (rngl_leb_gt Hor).
(*
apply rngl_nlt_ge in Hzs23.
apply (rngl_nle_gt_iff Hor).
intros H223; apply Hzs23; clear Hzs23.
*)
apply angle_eqb_neq in Ht2z, Ht3z.
change_angle_sub_r θ2 angle_straight.
progress sin_cos_add_sub_straight_hyp T Hzs1.
progress sin_cos_add_sub_straight_hyp T H23.
progress sin_cos_add_sub_straight_hyp T Ht23z.
progress sin_cos_add_sub_straight_hyp T Hzs23.
progress sin_cos_add_sub_straight_goal T.
rewrite (rngl_add_opp_r Hop).
apply (rngl_lt_0_sub Hop Hor).
Search (rngl_cos _ < rngl_cos (_ + _))%L.
...
      apply rngl_ltb_lt in Hzs1, Hzs2.
        now apply (rngl_lt_asymm Hor) in Hzs1.
      }
      destruct zs12. {
        destruct t23z; [ easy | ].
        destruct zs23; [ easy | symmetry ].
        apply (rngl_leb_gt Hor).
        apply rngl_ltb_lt in Hzs1, Hzs2, Hzs3.
...
        eapply (rngl_lt_trans Hor). {
          apply (rngl_lt_sub_l Hop Hor).
          now apply (rngl_mul_pos_pos Hon Hop Hiq Hor).
        }
...
        apply (rngl_le_lt_trans Hor _ (rngl_cos θ3)). {
...
          rewrite <- (rngl_mul_1_l Hon (rngl_cos θ3)) at 2.
Search (_ * _ ≤ _ * _)%L.
...
          apply (rngl_mul_le_mono_nonneg_r Hon Hop Hiq Hor).

Search (_ * _ ≤ _)%L.
...
          apply <- (rngl_mul_lt_mono_pos_r Hon Hop Hiq Hor 1%L).
          apply rngl
Search (rngl_cos (_ + _) < rngl_cos _)%L.
...
intros * H12.
remember (angle_add_overflow θ2 θ3) as ov eqn:H23.
symmetry in H23.
destruct ov. 2: {
  remember (angle_add_overflow (θ1 + θ2) θ3) as ov eqn:Hov.
  symmetry in Hov |-*.
  destruct ov; [ now apply angle_add_overflow_move_add | ].
  rewrite angle_add_comm.
  now apply angle_add_not_overflow_move_add.
} {
  destruct (angle_lt_dec θ2 angle_straight) as [H2s| H2s]. {
(**)
    change_angle_sub_r θ1 angle_straight.
    change_angle_sub_r θ3 angle_straight.
    move θ1 after θ2.
    do 2 rewrite <- angle_add_overflow_equiv2.
    progress unfold angle_add_overflow2.
    progress sin_cos_add_sub_right_goal T.
    do 2 rewrite (angle_add_add_swap _ angle_straight).
    rewrite <- angle_add_assoc.
    rewrite angle_straight_add_straight.
    rewrite angle_add_0_r.
    progress unfold angle_ltb.
    remember (0 ≤? rngl_sin (θ1 + θ2 + θ3))%L as z123 eqn:Hz123.
    symmetry in Hz123.
    destruct z123. {
      progress sin_cos_add_sub_straight_goal T.
...
    generalize H12; intros H1s.
    rewrite angle_add_overflow_comm in H1s.
    apply angle_add_overflow_lt_straight_ge_straight in H1s; [ | easy ].
    generalize H23; intros H3s.
    apply angle_add_overflow_lt_straight_ge_straight in H3s; [ | easy ].
    remember (θ1 - angle_straight)%A as θ.
    apply angle_add_move_r in Heqθ.
    subst θ1; rename θ into θ1; move θ1 after θ2.
    remember (θ3 - angle_straight)%A as θ.
    apply angle_add_move_r in Heqθ.
    subst θ3; rename θ into θ3; move θ3 before θ2.
...
  H23 : angle_add_overflow θ2 (θ3 + angle_straight) = true
  H12 : angle_add_overflow (θ1 + angle_straight) θ2 = true
  H2s : (θ2 < angle_straight)%A
  H1s : (angle_straight ≤ θ1 + angle_straight)%A
  H3s : (angle_straight ≤ θ3 + angle_straight)%A
  ============================
  angle_add_overflow (θ1 + angle_straight + θ2) (θ3 + angle_straight) =
  angle_add_overflow (θ1 + angle_straight) (θ2 + (θ3 + angle_straight))
...
Search (angle_straight ≤ _)%A.
Search (_ < angle_straight)%A.
Search (_ ≤ _ + _)%A.
Theorem glop : ∀ θ, (angle_straight ≤ θ + angle_straight)%A → (θ < angle_straight)%A.
...
    apply glop in H1s, H3s.
...
Search (angle_add_overflow _ (_ + _)).
rewrite angle_add_comm in H12.
apply angle_add_overflow_move_add in H12.
rewrite (angle_add_comm θ3).
rewrite <- angle_add_overflow_assoc.
...
  rewrite <- angle_add_overflow_equiv2 in H23, H12.
  progress unfold angle_add_overflow2 in H23, H12.
  remember (angle_add_overflow (θ1 + θ2) θ3) as ov eqn:Hov.
  symmetry in Hov |-*.
  destruct ov. {
    rewrite <- angle_add_overflow_equiv2 in Hov |-*.
    progress unfold angle_add_overflow2 in Hov |-*.
    progress unfold angle_ltb.
    remember (0 ≤? rngl_sin (θ1 + (θ2 + θ3)))%L as zs1 eqn:Hzs1.
    symmetry in Hzs1.
    destruct zs1. {
      remember (0 ≤? rngl_sin θ1)%L as zs2 eqn:Hzs2.
      symmetry in Hzs2.
      destruct zs2; [ | easy ].
      apply rngl_leb_le in Hzs1.
      apply rngl_leb_le in Hzs2.
      apply rngl_ltb_lt.
Search (rngl_cos _ < rngl_cos (_ + _))%L.
...
Search (_ + _ < _ + _)%A.
Search (_ + _ < _)%A.
...
do 2 rewrite <- angle_add_overflow_equiv2.
rewrite <- angle_add_assoc.
rewrite angle_add_lt_mono_l.
...
  remember (angle_add_overflow (θ1 + θ2) θ3) as ov eqn:Hov.
  symmetry in Hov |-*.
  destruct ov. {
...
Qed.
...
*)

End a.
