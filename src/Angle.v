(** * Angles Without π

    In this approach, an angle is not a real number but a pair of real
    numbers (x, y) such that x² + y² = 1. The cosine is then x, and the
    sine is y.

    The identity sin² + cos² = 1 holds by definition. We can define angle
    addition (see below), and the usual formulas for cos(x + y) and
    sin(x + y) follow naturally.

    There is no need for the number π here; the angle π is simply (-1, 0).
*)

Set Nested Proofs Allowed.
Require Import Stdlib.Arith.Arith.
Require Import RingLike.Utf8.

Require Import RingLike.Core.
Require Import RingLike.RealLike.

Require Import AngleDef.

Section a.

Context {T : Type}.
Context {ro : ring_like_op T}.
Context {rp : ring_like_prop T}.
Context {rl : real_like_prop T}.
Context {ac : angle_ctx T}.

Theorem rngl_cos_add :
  ∀ α1 α2,
  rngl_cos (α1 + α2) =
    (rngl_cos α1 * rngl_cos α2 - rngl_sin α1 * rngl_sin α2)%L.
Proof. easy. Qed.

Theorem rngl_sin_add :
  ∀ α1 α2,
  rngl_sin (α1 + α2) =
    (rngl_sin α1 * rngl_cos α2 + rngl_cos α1 * rngl_sin α2)%L.
Proof. easy. Qed.

Theorem rngl_cos_sub :
  ∀ α1 α2,
  (rngl_cos (α1 - α2) =
     rngl_cos α1 * rngl_cos α2 + rngl_sin α1 * rngl_sin α2)%L.
Proof.
destruct_ac.
intros; cbn.
rewrite (rngl_mul_opp_r Hop).
apply (rngl_sub_opp_r Hop).
Qed.

Theorem rngl_sin_sub :
  ∀ α1 α2,
  rngl_sin (α1 - α2) =
    (rngl_sin α1 * rngl_cos α2 - rngl_cos α1 * rngl_sin α2)%L.
Proof.
destruct_ac.
intros; cbn.
rewrite (rngl_mul_opp_r Hop).
apply (rngl_add_opp_r Hop).
Qed.

Theorem rngl_add_cos_nonneg_sqrt_mul_le :
  ∀ α1 α2,
  (0 ≤ rngl_cos α1 + rngl_cos α2)%L
  → (√((1 - rngl_cos α1) * (1 - rngl_cos α2)) ≤
      √((1 + rngl_cos α1) * (1 + rngl_cos α2)))%L.
Proof.
destruct_ac.
intros * H12.
assert (Hz1ac :  ∀ α, (0 ≤ 1 + rngl_cos α)%L). {
  intros.
  apply (rngl_le_sub_le_add_l Hop Hor).
  progress unfold rngl_sub.
  rewrite Hop, rngl_add_0_l.
  apply rngl_cos_bound.
}
assert (Hz1sc : ∀ α, (0 ≤ 1 - rngl_cos α)%L). {
  intros.
  apply (rngl_le_add_le_sub_r Hop Hor).
  rewrite rngl_add_0_l.
  apply rngl_cos_bound.
}
destruct (Nat.eq_dec (rngl_characteristic T) 1) as [Hc1| Hc1]. {
  specialize (rngl_characteristic_1 Hos Hc1) as H1.
  rewrite H1, (H1 (√_))%L.
  apply (rngl_le_refl Hor).
}
apply (rngl_square_le_simpl_nonneg Hop Hiq Hto). {
  apply rl_sqrt_nonneg.
  now apply (rngl_mul_nonneg_nonneg Hos Hor).
}
do 2 rewrite fold_rngl_squ.
rewrite rngl_squ_sqrt. 2: {
  now apply (rngl_mul_nonneg_nonneg Hos Hor).
}
rewrite rngl_squ_sqrt. 2: {
  now apply (rngl_mul_nonneg_nonneg Hos Hor).
}
rewrite (rngl_mul_sub_distr_l Hop).
rewrite rngl_mul_1_r.
rewrite (rngl_mul_sub_distr_r Hop).
rewrite rngl_mul_1_l.
rewrite (rngl_sub_sub_distr Hop).
rewrite rngl_mul_add_distr_l.
rewrite rngl_mul_1_r.
rewrite rngl_mul_add_distr_r.
rewrite rngl_mul_1_l.
rewrite rngl_add_assoc.
apply (rngl_add_le_mono_r Hos Hor).
rewrite <- (rngl_sub_add_distr Hos).
apply (rngl_le_sub_le_add_r Hop Hor).
do 2 rewrite <- rngl_add_assoc.
apply (rngl_le_add_r Hos Hor).
rewrite rngl_add_assoc.
rewrite rngl_add_add_swap.
rewrite rngl_add_assoc.
rewrite <- rngl_add_assoc.
rewrite <- rngl_mul_2_l.
rewrite <- (rngl_mul_2_l (rngl_cos α2)).
rewrite <- rngl_mul_add_distr_l.
apply (rngl_mul_nonneg_nonneg Hos Hor); [ | easy ].
apply rngl_lt_le_incl.
apply (rngl_0_lt_2 Hos Hc1 Hto).
Qed.

Theorem eq_rngl_sin_0 : ∀ α, rngl_sin α = 0%L → α = 0%A ∨ α = π.
Proof.
destruct_ac.
intros * Hα.
destruct α as (c, s, Hcs).
cbn in Hα |-*.
subst s; cbn.
specialize (cos2_sin2_prop_add_squ _ _ Hcs) as H1.
rewrite (rngl_squ_0 Hos) in H1.
rewrite rngl_add_0_r in H1.
rewrite <- rngl_squ_1 in H1.
apply (rngl_squ_eq_cases Hop Hiv Heo) in H1. 2: {
  rewrite rngl_mul_1_l.
  apply rngl_mul_1_r.
}
now destruct H1; subst c; [ left | right ]; apply eq_angle_eq.
Qed.

Theorem rngl_cos_add_straight_l :
  ∀ α, rngl_cos (π + α) = (- rngl_cos α)%L.
Proof.
destruct_ac.
intros; cbn.
rewrite (rngl_mul_opp_l Hop).
rewrite rngl_mul_1_l.
rewrite (rngl_mul_0_l Hos).
apply (rngl_sub_0_r Hos).
Qed.

Theorem rngl_cos_add_straight_r :
  ∀ α, rngl_cos (α + π) = (- rngl_cos α)%L.
Proof.
destruct_ac.
intros; cbn.
rewrite (rngl_mul_opp_r Hop).
rewrite rngl_mul_1_r.
rewrite (rngl_mul_0_r Hos).
apply (rngl_sub_0_r Hos).
Qed.

Theorem rngl_cos_add_right_l :
  ∀ α, rngl_cos (π/₂ + α) = (- rngl_sin α)%L.
Proof.
destruct_ac.
intros; cbn.
rewrite rngl_mul_1_l.
rewrite (rngl_mul_0_l Hos).
apply (rngl_sub_0_l Hop).
Qed.

Theorem rngl_cos_add_right_r :
  ∀ α, rngl_cos (α + π/₂) = (- rngl_sin α)%L.
Proof.
destruct_ac.
intros; cbn.
rewrite rngl_mul_1_r.
rewrite (rngl_mul_0_r Hos).
apply (rngl_sub_0_l Hop).
Qed.

Theorem rngl_sin_add_right_l :
  ∀ α, rngl_sin (π/₂ + α) = rngl_cos α.
Proof.
destruct_ac.
intros; cbn.
rewrite rngl_mul_1_l.
rewrite (rngl_mul_0_l Hos).
apply rngl_add_0_r.
Qed.

Theorem rngl_sin_add_right_r :
  ∀ α, rngl_sin (α + π/₂) = rngl_cos α.
Proof.
destruct_ac.
intros; cbn.
rewrite rngl_mul_1_r.
rewrite (rngl_mul_0_r Hos).
apply rngl_add_0_l.
Qed.

Theorem rngl_cos_sub_straight_l :
  ∀ α, rngl_cos (π - α) = (- rngl_cos α)%L.
Proof.
destruct_ac.
intros; cbn.
rewrite (rngl_mul_opp_l Hop).
rewrite rngl_mul_1_l.
rewrite (rngl_mul_0_l Hos).
now rewrite (rngl_sub_0_r Hos).
Qed.

Theorem rngl_sin_sub_straight_l :
  ∀ α, rngl_sin (π - α) = rngl_sin α.
Proof.
destruct_ac.
intros; cbn.
rewrite (rngl_mul_opp_l Hop).
rewrite rngl_mul_1_l.
rewrite (rngl_mul_0_l Hos).
rewrite rngl_add_0_l.
apply (rngl_opp_involutive Hop).
Qed.

Theorem rngl_cos_sub_straight_r :
  ∀ α, rngl_cos (α - π) = (- rngl_cos α)%L.
Proof.
destruct_ac.
intros; cbn.
rewrite (rngl_mul_opp_r Hop).
rewrite rngl_mul_1_r.
rewrite (rngl_opp_0 Hop).
rewrite (rngl_mul_0_r Hos).
now rewrite (rngl_sub_0_r Hos).
Qed.

Theorem rngl_sin_sub_straight_r :
  ∀ α, rngl_sin (α - π) = (- rngl_sin α)%L.
Proof.
destruct_ac.
intros; cbn.
rewrite (rngl_opp_0 Hop).
rewrite (rngl_mul_opp_r Hop).
rewrite (rngl_mul_0_r Hos).
rewrite rngl_add_0_r.
now rewrite rngl_mul_1_r.
Qed.

Theorem rngl_sin_nonneg_cos_le_sin_le :
  ∀ α1 α2,
  (0 ≤ rngl_sin α1)%L
  → (0 ≤ rngl_sin α2)%L
  → (rngl_cos α1 ≤ rngl_cos α2)%L
  → if (0 ≤? rngl_cos α1)%L then (rngl_sin α2 ≤ rngl_sin α1)%L
    else if (0 ≤? rngl_cos α2)%L then (0 ≤ rngl_sin (α1 - α2))%L
    else (rngl_sin α1 ≤ rngl_sin α2)%L.
Proof.
destruct_ac.
intros * Hzs1 Hzs2 Hc12.
remember (0 ≤? rngl_cos α1)%L as zc1 eqn:Hzc1.
symmetry in Hzc1.
destruct zc1. {
  apply rngl_leb_le in Hzc1.
  rewrite <- (rngl_abs_nonneg_eq Hop Hor) in Hc12. 2: {
    eapply (rngl_le_trans Hor); [ apply Hzc1 | easy ].
  }
  rewrite <- (rngl_abs_nonneg_eq Hop Hor _ Hzc1) in Hc12.
  rewrite <- (rngl_abs_nonneg_eq Hop Hor); [ | easy ].
  rewrite <- (rngl_abs_nonneg_eq Hop Hor _ Hzs2).
  apply (rngl_abs_le_squ_le Hop Hto) in Hc12.
  apply (rngl_squ_le_abs_le Hop Hiq Hto).
  specialize (cos2_sin2_1 α1) as Hcs1.
  specialize (cos2_sin2_1 α2) as Hcs2.
  apply (rngl_add_sub_eq_r Hos) in Hcs1, Hcs2.
  rewrite <- Hcs1, <- Hcs2 in Hc12.
  now apply (rngl_sub_le_mono_l Hop Hor) in Hc12.
}
apply (rngl_leb_gt_iff Hto) in Hzc1.
remember (0 ≤? rngl_cos α2)%L as zc2 eqn:Hzc2.
symmetry in Hzc2.
destruct zc2. {
  apply rngl_leb_le in Hzc2; cbn.
  rewrite (rngl_mul_opp_r Hop).
  rewrite rngl_add_comm.
  rewrite (rngl_add_opp_l Hop).
  apply (rngl_le_0_sub Hop Hor).
  apply (rngl_le_trans Hor _ 0)%L. {
    apply (rngl_mul_nonpos_nonneg Hop Hor); [ | easy ].
    now apply rngl_lt_le_incl.
  } {
    now apply (rngl_mul_nonneg_nonneg Hos Hor).
  }
} {
  apply (rngl_leb_gt_iff Hto) in Hzc2.
  apply (rngl_opp_le_compat Hop Hor) in Hc12.
  rewrite <- (rngl_abs_nonpos_eq Hop Hto) in Hc12. 2: {
    now apply rngl_lt_le_incl.
  }
  rewrite <- (rngl_abs_nonpos_eq Hop Hto) in Hc12. 2: {
    now apply rngl_lt_le_incl.
  }
  rewrite <- (rngl_abs_nonneg_eq Hop Hor); [ | easy ].
  rewrite <- (rngl_abs_nonneg_eq Hop Hor _ Hzs1).
  apply (rngl_abs_le_squ_le Hop Hto) in Hc12.
  apply (rngl_squ_le_abs_le Hop Hiq Hto).
  specialize (cos2_sin2_1 α1) as Hcs1.
  specialize (cos2_sin2_1 α2) as Hcs2.
  apply (rngl_add_sub_eq_r Hos) in Hcs1, Hcs2.
  rewrite <- Hcs1, <- Hcs2 in Hc12.
  now apply (rngl_sub_le_mono_l Hop Hor) in Hc12.
}
Qed.

Theorem rngl_cos_cos_sin_sin_nonneg_sin_le_cos_le_iff :
  ∀ α1 α2,
  (0 ≤ rngl_sin α1)%L
  → (0 ≤ rngl_sin α2)%L
  → (0 ≤ rngl_cos α1)%L
  → (0 ≤ rngl_cos α2)%L
  → (rngl_sin α1 ≤ rngl_sin α2)%L
  ↔ (rngl_cos α2 ≤ rngl_cos α1)%L.
Proof.
destruct_ac.
intros * Hzs1 Hzs2 Hzc1 Hzc2.
split. {
  intros Hss.
  apply (rngl_nlt_ge Hor) in Hss.
  apply (rngl_nlt_ge_iff Hto).
  intros Hcc; apply Hss; clear Hss.
  apply rngl_le_neq.
  split. {
    apply rngl_lt_le_incl in Hcc.
    specialize rngl_sin_nonneg_cos_le_sin_le as H1.
    specialize (H1 _ _ Hzs1 Hzs2 Hcc).
    apply rngl_leb_le in Hzc1.
    now rewrite Hzc1 in H1.
  }
  intros Hss.
  apply (rngl_nle_gt Hor) in Hcc.
  apply Hcc; clear Hcc.
  rewrite <- (rngl_abs_nonneg_eq Hop Hor); [ | easy ].
  rewrite <- (rngl_abs_nonneg_eq Hop Hor (rngl_cos α2)); [ | easy ].
  apply (rngl_squ_le_abs_le Hop Hiq Hto).
  specialize (cos2_sin2_1 α1) as H1.
  apply (rngl_add_move_r Hop) in H1.
  rewrite H1; clear H1.
  specialize (cos2_sin2_1 α2) as H1.
  apply (rngl_add_move_r Hop) in H1.
  rewrite H1, Hss; clear H1.
  apply (rngl_le_refl Hor).
} {
  intros Hcc.
  specialize rngl_sin_nonneg_cos_le_sin_le as H1.
  specialize (H1 _ _ Hzs2 Hzs1 Hcc).
  apply rngl_leb_le in Hzc2.
  now rewrite Hzc2 in H1.
}
Qed.

Theorem rngl_cos_cos_sin_sin_nonneg_sin_lt_cos_lt_iff :
  ∀ α1 α2,
  (0 ≤ rngl_sin α1)%L
  → (0 ≤ rngl_sin α2)%L
  → (0 ≤ rngl_cos α1)%L
  → (0 ≤ rngl_cos α2)%L
  → (rngl_sin α1 < rngl_sin α2)%L
  ↔ (rngl_cos α2 < rngl_cos α1)%L.
Proof.
destruct_ac.
intros * Hzs1 Hzs2 Hzc1 Hzc2.
split. 2: {
  intros Hcc.
  apply (rngl_nle_gt Hor) in Hcc.
  apply (rngl_nle_gt_iff Hto).
  intros Hss; apply Hcc; clear Hcc.
  now apply rngl_cos_cos_sin_sin_nonneg_sin_le_cos_le_iff.
} {
  intros Hss.
  apply (rngl_nle_gt Hor) in Hss.
  apply (rngl_nle_gt_iff Hto).
  intros Hcc; apply Hss; clear Hss.
  now apply rngl_cos_cos_sin_sin_nonneg_sin_le_cos_le_iff.
}
Qed.

Theorem eq_rngl_cos_0 :
  ∀ α, rngl_cos α = 0%L ↔ (α = π/₂ ∨ α = - π/₂)%A.
Proof.
destruct_ac.
intros.
split; intros Hα; [ | now destruct Hα; subst α ].
specialize (cos2_sin2_1 α) as H1.
rewrite Hα in H1.
rewrite (rngl_squ_0 Hos) in H1.
apply (rngl_add_move_l Hop) in H1.
rewrite (rngl_sub_0_r Hos) in H1.
rewrite <- rngl_squ_1 in H1.
apply (rngl_squ_eq_cases Hop Hiv Heo) in H1. 2: {
  rewrite rngl_mul_1_l.
  apply rngl_mul_1_r.
}
destruct H1. {
  left; apply eq_angle_eq.
  now rewrite Hα, H.
} {
  right; apply eq_angle_eq.
  now rewrite Hα, H.
}
Qed.

Theorem eq_rngl_cos_1 : ∀ α, rngl_cos α = 1%L ↔ α = 0%A.
Proof.
destruct_ac.
intros.
split; intros Hα; [ | now subst α ].
specialize (cos2_sin2_1 α) as H1.
rewrite Hα in H1.
rewrite rngl_squ_1 in H1.
apply (rngl_add_move_l Hop) in H1.
rewrite (rngl_sub_diag Hos) in H1.
apply (eq_rngl_squ_0 Hos) in H1. 2: {
  apply Bool.orb_true_iff; right.
  rewrite Heo, Bool.andb_true_r.
  apply (rngl_has_inv_has_inv_or_pdiv Hiv).
}
apply eq_angle_eq.
now rewrite Hα, H1.
Qed.

Theorem eq_rngl_cos_opp_1 : ∀ α, (rngl_cos α = -1 → α = π)%L.
Proof.
destruct_ac.
intros * Hα.
destruct α as (c, s, Hcs).
cbn in Hα |-*.
subst c.
apply eq_angle_eq; cbn.
f_equal.
apply cos2_sin2_prop_add_squ in Hcs.
rewrite (rngl_squ_opp Hop) in Hcs.
rewrite rngl_squ_1 in Hcs.
apply (rngl_add_sub_eq_l Hos) in Hcs.
rewrite (rngl_sub_diag Hos) in Hcs.
symmetry in Hcs.
apply (eq_rngl_squ_0 Hos) in Hcs; [ easy | ].
apply Bool.orb_true_iff; right.
rewrite Heo, Bool.andb_true_r.
apply (rngl_has_inv_has_inv_or_pdiv Hiv).
Qed.

Theorem eq_rngl_sin_1 : ∀ α, rngl_sin α = 1%L ↔ α = π/₂.
Proof.
destruct_ac.
intros.
split; intros Hα; [ | now subst α ].
specialize (cos2_sin2_1 α) as H1.
rewrite Hα in H1.
rewrite rngl_squ_1 in H1.
apply (rngl_add_move_r Hop) in H1.
rewrite (rngl_sub_diag Hos) in H1.
apply (eq_rngl_squ_0 Hos) in H1. 2: {
  apply Bool.orb_true_iff; right.
  rewrite Heo, Bool.andb_true_r.
  apply (rngl_has_inv_has_inv_or_pdiv Hiv).
}
apply eq_angle_eq.
now rewrite Hα, H1.
Qed.

Theorem rngl_cos_eq :
  ∀ α1 α2, rngl_cos α1 = rngl_cos α2 → α1 = α2 ∨ α1 = (- α2)%A.
Proof.
destruct_ac.
intros * Hcc.
destruct (rngl_eqb_dec (rngl_sin α1) (rngl_sin α2)) as [Hss| Hss]. {
  apply (rngl_eqb_eq Heo) in Hss.
  left.
  apply eq_angle_eq.
  now rewrite Hcc, Hss.
}
apply (rngl_eqb_neq Heo) in Hss.
right.
apply eq_angle_eq.
rewrite Hcc; f_equal.
cbn.
specialize (cos2_sin2_1 α1) as H1.
specialize (cos2_sin2_1 α2) as H2.
apply (rngl_add_move_l Hop) in H1, H2.
rewrite Hcc in H1.
rewrite <- H2 in H1; clear H2.
apply (eq_rngl_squ_rngl_abs Hop Hto) in H1; cycle 1. {
  apply Bool.orb_true_iff; right.
  apply (rngl_has_inv_has_inv_or_pdiv Hiv).
} {
  apply (rngl_mul_comm Hic).
}
progress unfold rngl_abs in H1.
remember (rngl_sin α1 ≤? 0)%L as s1z eqn:Hs1z.
remember (rngl_sin α2 ≤? 0)%L as s2z eqn:Hs2z.
symmetry in Hs1z, Hs2z.
destruct s1z; [ | now destruct s2z ].
destruct s2z; [ now apply (rngl_opp_inj Hop) in H1 | ].
rewrite <- H1; symmetry.
apply (rngl_opp_involutive Hop).
Qed.

Theorem rngl_sin_eq :
  ∀ α1 α2, rngl_sin α1 = rngl_sin α2 → α1 = α2 ∨ α1 = (π - α2)%A.
Proof.
destruct_ac.
intros * Hss.
destruct (rngl_eqb_dec (rngl_cos α1) (rngl_cos α2)) as [Hcc| Hcc]. {
  apply (rngl_eqb_eq Heo) in Hcc.
  left.
  apply eq_angle_eq.
  now rewrite Hcc, Hss.
}
apply (rngl_eqb_neq Heo) in Hcc.
right.
apply eq_angle_eq.
rewrite rngl_cos_sub_straight_l.
rewrite rngl_sin_sub_straight_l.
rewrite Hss; f_equal.
specialize (cos2_sin2_1 α1) as H1.
specialize (cos2_sin2_1 α2) as H2.
apply (rngl_add_move_r Hop) in H1, H2.
rewrite Hss in H1.
rewrite <- H2 in H1; clear H2.
apply (eq_rngl_squ_rngl_abs Hop Hto) in H1; cycle 1. {
  rewrite Bool.orb_true_iff; right.
  apply (rngl_has_inv_has_inv_or_pdiv Hiv).
} {
  apply (rngl_mul_comm Hic).
}
progress unfold rngl_abs in H1.
remember (rngl_cos α1 ≤? 0)%L as c1z eqn:Hc1z.
remember (rngl_cos α2 ≤? 0)%L as c2z eqn:Hc2z.
symmetry in Hc1z, Hc2z.
destruct c1z; [ | now destruct c2z ].
destruct c2z; [ now apply (rngl_opp_inj Hop) in H1 | ].
rewrite <- H1; symmetry.
apply (rngl_opp_involutive Hop).
Qed.

Theorem rngl_cos_cos_sin_sin_neg_sin_le_cos_le_iff :
  ∀ α1 α2,
  (0 ≤ rngl_sin α1)%L
  → (0 ≤ rngl_sin α2)%L
  → (rngl_cos α1 ≤ 0)%L
  → (rngl_cos α2 ≤ 0)%L
  → (rngl_sin α1 ≤ rngl_sin α2)%L ↔ (rngl_cos α1 ≤ rngl_cos α2)%L.
Proof.
destruct_ac.
destruct (Nat.eq_dec (rngl_characteristic T) 1) as [Hc1| Hc1]. {
  specialize (rngl_characteristic_1 Hos Hc1) as H1.
  intros * Hzs1 Hzs2 Hzc1 Hzc2.
  rewrite (H1 (rngl_sin α1)), (H1 (rngl_sin α2)).
  rewrite (H1 (rngl_cos α1)), (H1 (rngl_cos α2)).
  easy.
}
intros * Hzs1 Hzs2 Hzc1 Hzc2.
split. {
  intros Hss.
  apply (rngl_nlt_ge Hor) in Hss.
  apply (rngl_nlt_ge_iff Hto).
  intros Hcc; apply Hss; clear Hss.
  apply rngl_le_neq.
  split. {
    apply rngl_lt_le_incl in Hcc.
    specialize rngl_sin_nonneg_cos_le_sin_le as H1.
    specialize (H1 _ _ Hzs2 Hzs1 Hcc).
    destruct (rngl_leb_dec 0 (rngl_cos α1)) as [H| H]. {
      apply rngl_leb_le in H.
      apply (rngl_le_antisymm Hor) in H; [ | easy ].
      apply eq_rngl_cos_0 in H.
      destruct H; subst α1; [ apply rngl_sin_bound | ].
      exfalso.
      apply (rngl_nlt_ge Hor) in Hzs1.
      apply Hzs1, (rngl_opp_1_lt_0 Hop Hc1 Hto).
    }
    apply (rngl_leb_gt_iff Hto) in H.
    move H before Hzc1; clear Hzc1; rename H into Hzc1.
    destruct (rngl_leb_dec 0 (rngl_cos α2)) as [H| H]. {
      apply rngl_leb_le in H.
      apply (rngl_le_antisymm Hor) in H; [ | easy ].
      apply eq_rngl_cos_0 in H.
      destruct H; subst α2. {
        apply rngl_lt_le_incl in Hzc1.
        apply (rngl_le_antisymm Hor) in Hcc; [ | easy ].
        cbn in Hcc.
        apply eq_rngl_cos_0 in Hcc.
        destruct Hcc; subst α1; [ apply (rngl_le_refl Hor) | ].
        exfalso.
        apply (rngl_nlt_ge Hor) in Hzs1.
        apply Hzs1; clear Hzs1; cbn.
        apply (rngl_opp_1_lt_0 Hop Hc1 Hto).
      }
      apply rngl_sin_bound.
    }
    apply (rngl_leb_gt_iff Hto) in H.
    move H before Hzc2; clear Hzc2; rename H into Hzc2.
    generalize Hzc2; intros H.
    apply (rngl_leb_gt_iff Hto) in H.
    rewrite H in H1; clear H.
    generalize Hzc1; intros H.
    apply (rngl_leb_gt_iff Hto) in H.
    now rewrite H in H1; clear H.
  }
  intros H.
  apply rngl_sin_eq in H.
  destruct H; subst α2; [ now apply rngl_lt_irrefl in Hcc | ].
  rewrite rngl_cos_sub_straight_l in Hcc, Hzc2.
  apply (rngl_opp_nonpos_nonneg Hop Hor) in Hzc2.
  apply (rngl_le_antisymm Hor) in Hzc2; [ | easy ].
  rewrite Hzc2 in Hcc.
  rewrite (rngl_opp_0 Hop) in Hcc.
  now apply rngl_lt_irrefl in Hcc.
} {
  intros Hcc.
  destruct (rngl_leb_dec 0 (rngl_cos α1)) as [H| H]. {
    apply rngl_leb_le in H.
    apply (rngl_le_antisymm Hor) in H; [ | easy ].
    apply eq_rngl_cos_0 in H.
    destruct H; subst α1. {
      apply (rngl_le_antisymm Hor) in Hcc; [ | easy ].
      apply eq_rngl_cos_0 in Hcc.
      destruct Hcc; subst α2; [ apply (rngl_le_refl Hor) | ].
      exfalso.
      apply (rngl_nlt_ge Hor) in Hzs2.
      apply Hzs2, (rngl_opp_1_lt_0 Hop Hc1 Hto).
    }
    apply rngl_sin_bound.
  }
  apply (rngl_leb_gt_iff Hto) in H.
  move H before Hzc1; clear Hzc1; rename H into Hzc1.
  destruct (rngl_leb_dec 0 (rngl_cos α2)) as [H| H]. {
    apply rngl_leb_le in H.
    apply (rngl_le_antisymm Hor) in H; [ | easy ].
    apply eq_rngl_cos_0 in H.
    destruct H; subst α2. {
      apply rngl_sin_bound.
    }
    exfalso.
    apply (rngl_nlt_ge Hor) in Hzs2.
    apply Hzs2, (rngl_opp_1_lt_0 Hop Hc1 Hto).
  }
  apply (rngl_leb_gt_iff Hto) in H.
  move H before Hzc2; clear Hzc2; rename H into Hzc2.
  specialize rngl_sin_nonneg_cos_le_sin_le as H1.
  specialize (H1 _ _ Hzs1 Hzs2 Hcc).
  generalize Hzc1; intros H.
  apply (rngl_leb_gt_iff Hto) in H.
  rewrite H in H1; clear H.
  generalize Hzc2; intros H.
  apply (rngl_leb_gt_iff Hto) in H.
  now rewrite H in H1; clear H.
}
Qed.

Theorem rngl_add_cos_nonneg_when_sin_nonneg :
  ∀ α1 α2,
  (0 ≤ rngl_sin α1)%L
  → (0 ≤ rngl_sin α2)%L
  → (0 ≤ rngl_sin (α1 + α2))%L
  → (0 ≤ rngl_cos α1)%L
  → (0 ≤ rngl_cos α1 + rngl_cos α2)%L.
Proof.
destruct_ac.
intros * Hzs1 Hzs2 Hzs3 Hzc1.
destruct (Nat.eq_dec (rngl_characteristic T) 1) as [Hc1| Hc1]. {
  specialize (rngl_characteristic_1 Hos Hc1) as H1.
  rewrite H1.
  apply (rngl_le_refl Hor).
}
remember (α1 + α2)%A as α3 eqn:Hα3.
destruct (rngl_leb_dec 0 (rngl_cos α2)) as [Hzc2| Hzc2]. {
  apply rngl_leb_le in Hzc2.
  now apply (rngl_le_0_add Hos Hor).
}
apply (rngl_leb_gt_iff Hto) in Hzc2.
(* here, for sin α3 to be non negative, then the negativity
   of α2 must not be greater than the positivity of α1 *)
apply (rngl_le_sub_le_add_r Hop Hor).
rewrite (rngl_sub_0_l Hop).
apply (rngl_nlt_ge_iff Hto).
intros Hcc.
apply (rngl_nlt_ge Hor) in Hzs3.
apply Hzs3; clear Hzs3.
subst α3; cbn.
(* special case for sin α2 = 0 *)
destruct (rngl_eqb_dec (rngl_sin α2) 0) as [H2z| H2z]. {
  apply (rngl_eqb_eq Heo) in H2z.
  rewrite H2z, (rngl_mul_0_r Hos), rngl_add_0_r.
  destruct (rngl_eqb_dec (rngl_sin α1) 0) as [H1z| H1z]. {
    apply (rngl_eqb_eq Heo) in H1z.
    apply eq_rngl_sin_0 in H2z, H1z.
    destruct H2z; subst α2. {
      apply (rngl_nle_gt_iff Hto) in Hzc2.
      exfalso; apply Hzc2; clear Hzc2; cbn.
      apply (rngl_0_le_1 Hos Hto).
    }
    clear Hzs2 Hzc2.
    cbn in Hcc.
    exfalso.
    destruct H1z; subst α1. {
      rewrite (rngl_opp_involutive Hop) in Hcc.
      cbn in Hcc.
      now apply rngl_lt_irrefl in Hcc.
    }
    cbn in Hzc1.
    apply (rngl_nlt_ge Hor) in Hzc1.
    apply Hzc1; clear Hzc1.
    apply (rngl_opp_neg_pos Hop Hor).
    apply (rngl_0_lt_1 Hos Hc1 Hto).
  }
  apply (rngl_mul_pos_neg Hop Hiq Hor); [ | easy ].
  apply rngl_le_neq.
  split; [ easy | ].
  apply (rngl_eqb_neq Heo) in H1z.
  now apply not_eq_sym.
}
apply (rngl_eqb_neq Heo) in H2z.
assert (Hzls2 : (0 < rngl_sin α2)%L). {
  apply rngl_le_neq.
  split; [ easy | ].
  now apply not_eq_sym.
}
clear H2z.
assert (Hs21 : (rngl_sin α2 < rngl_sin α1)%L). {
  apply (rngl_lt_opp_r Hop Hor) in Hcc.
  remember (π - α2)%A as α eqn:Hα.
  symmetry in Hα.
  apply angle_sub_move_l in Hα.
  subst α2; rename α into α2.
  move α2 before α1.
  rewrite rngl_cos_sub_straight_l in Hcc, Hzc2.
  rewrite rngl_sin_sub_straight_l in Hzs2 |-*.
  rewrite (rngl_add_opp_r Hop) in Hcc.
  apply -> (rngl_lt_sub_0 Hop Hor) in Hcc.
  apply (rngl_opp_neg_pos Hop Hor) in Hzc2.
  apply rngl_lt_le_incl in Hzc2.
  now apply rngl_cos_cos_sin_sin_nonneg_sin_lt_cos_lt_iff.
}
rewrite rngl_add_comm.
apply
  (rngl_le_lt_trans Hor _
     ((- rngl_cos α2) * rngl_sin α2 +
        rngl_sin α1 * rngl_cos α2))%L. {
  apply (rngl_add_le_mono_r Hos Hor).
  apply (rngl_mul_le_mono_pos_r Hop Hiq Hto); [ easy | ].
  now apply rngl_lt_le_incl.
}
rewrite rngl_add_comm.
rewrite (rngl_mul_comm Hic).
rewrite (rngl_mul_opp_l Hop).
rewrite (rngl_add_opp_r Hop).
rewrite <- (rngl_mul_sub_distr_l Hop).
rewrite (rngl_mul_comm Hic).
apply (rngl_mul_pos_neg Hop Hiq Hor); [ | easy ].
now apply (rngl_lt_0_sub Hop Hor).
Qed.

Theorem rngl_sin_nonneg_sin_nonneg_add_1_cos_add_sub :
  ∀ α1 α2,
  (0 ≤? rngl_sin α1)%L = (0 ≤? rngl_sin α2)%L
  → ((1 + rngl_cos (α1 + α2)) * 2)%L =
      (√((1 + rngl_cos α1) * (1 + rngl_cos α2)) -
       √((1 - rngl_cos α1) * (1 - rngl_cos α2)))²%L.
Proof.
destruct_ac.
intros * Hzs12.
assert (Ha12 : ∀ α1 α2, (0 ≤ (1 + rngl_cos α1) * (1 + rngl_cos α2))%L). {
  intros.
  apply (rngl_mul_nonneg_nonneg Hos Hor). {
    apply (rngl_le_sub_le_add_l Hop Hor).
    progress unfold rngl_sub.
    rewrite Hop, rngl_add_0_l.
    apply rngl_cos_bound.
  } {
    apply (rngl_le_sub_le_add_l Hop Hor).
    progress unfold rngl_sub.
    rewrite Hop, rngl_add_0_l.
    apply rngl_cos_bound.
  }
}
assert (Hs12 : ∀ α1 α2, (0 ≤ (1 - rngl_cos α1) * (1 - rngl_cos α2))%L). {
  intros.
  apply (rngl_mul_nonneg_nonneg Hos Hor). {
    apply (rngl_le_add_le_sub_l Hop Hor).
    rewrite rngl_add_0_r.
    apply rngl_cos_bound.
  } {
    apply (rngl_le_add_le_sub_l Hop Hor).
    rewrite rngl_add_0_r.
    apply rngl_cos_bound.
  }
}
rewrite (rngl_squ_sub Hop Hic).
rewrite rngl_squ_sqrt; [ | easy ].
rewrite rngl_squ_sqrt; [ | easy ].
rewrite <- (rngl_add_sub_swap Hop).
rewrite <- rngl_mul_assoc.
rewrite <- rl_sqrt_mul; [ | easy | easy ].
rewrite rngl_mul_assoc.
rewrite (rngl_mul_mul_swap Hic (1 + rngl_cos α1))%L.
rewrite <- rngl_mul_assoc.
rewrite (rngl_squ_sub_squ' Hop).
rewrite rngl_mul_1_r, rngl_mul_1_l.
rewrite (rngl_add_sub Hos).
rewrite (rngl_squ_sub_squ' Hop).
rewrite rngl_mul_1_r, rngl_mul_1_l.
rewrite (rngl_add_sub Hos).
rewrite rngl_squ_1.
replace (1 - rngl_cos² α1)%L with (rngl_sin² α1). 2: {
  symmetry.
  apply (rngl_add_sub_eq_l Hos).
  apply cos2_sin2_prop_add_squ.
  apply rngl_cos2_sin2.
}
replace (1 - rngl_cos² α2)%L with (rngl_sin² α2). 2: {
  symmetry.
  apply (rngl_add_sub_eq_l Hos).
  apply cos2_sin2_prop_add_squ.
  apply rngl_cos2_sin2.
}
rewrite rl_sqrt_mul; cycle 1. {
  apply (rngl_squ_nonneg Hos Hto).
} {
  apply (rngl_squ_nonneg Hos Hto).
}
do 2 rewrite (rl_sqrt_squ Hop Hto).
rewrite (rngl_mul_add_distr_l (1 + rngl_cos α1))%L.
rewrite rngl_mul_1_r.
rewrite (rngl_mul_add_distr_r 1 (rngl_cos α1))%L.
rewrite rngl_mul_1_l.
rewrite (rngl_mul_sub_distr_l Hop (1 - rngl_cos α1))%L.
rewrite rngl_mul_1_r.
rewrite (rngl_mul_sub_distr_r Hop 1 (rngl_cos α1))%L.
rewrite rngl_mul_1_l.
rewrite rngl_add_assoc.
rewrite (rngl_add_sub_assoc Hop (1 + _ + _ + _ * _))%L.
rewrite (rngl_add_sub_assoc Hop _ 1 (rngl_cos α1))%L.
rewrite (rngl_sub_sub_distr Hop _ (rngl_cos α2)).
rewrite rngl_add_add_swap.
rewrite (rngl_add_add_swap _ (rngl_cos α2) 1)%L.
rewrite (rngl_add_add_swap _ (rngl_cos α1) 1)%L.
rewrite (rngl_add_sub_swap Hop _ _ (rngl_cos α1)).
rewrite (rngl_add_sub_swap Hop _ _ (rngl_cos α1)).
rewrite (rngl_add_sub Hos).
rewrite (rngl_add_sub_swap Hop _ _ (rngl_cos α2)).
rewrite (rngl_add_sub Hos).
rewrite <- rngl_add_assoc.
rewrite <- (rngl_mul_2_l (rngl_cos α1 * _)%L).
rewrite rngl_add_mul_r_diag_l.
rewrite <- (rngl_mul_sub_distr_l Hop).
rewrite (rngl_mul_comm Hic).
f_equal.
rewrite <- (rngl_add_sub_assoc Hop).
f_equal; cbn.
f_equal.
remember (0 ≤? rngl_sin α2)%L as zs2 eqn:Hzs2.
symmetry in Hzs2.
destruct zs2. {
  apply rngl_leb_le in Hzs2, Hzs12.
  rewrite (rngl_abs_nonneg_eq Hop Hor); [ | easy ].
  rewrite (rngl_abs_nonneg_eq Hop Hor); [ | easy ].
  easy.
} {
  apply (rngl_leb_gt_iff Hto) in Hzs2, Hzs12.
  apply rngl_lt_le_incl in Hzs2, Hzs12.
  rewrite (rngl_abs_nonpos_eq Hop Hto); [ | easy ].
  rewrite (rngl_abs_nonpos_eq Hop Hto); [ | easy ].
  rewrite (rngl_mul_opp_l Hop).
  rewrite (rngl_mul_opp_r Hop).
  symmetry.
  apply (rngl_opp_involutive Hop).
}
Qed.

Theorem rngl_sin_nonneg_sin_nonneg_sin_nonneg :
  ∀ α1 α2,
  α1 ≠ π ∨ α2 ≠ π
  → (0 ≤ rngl_sin α1)%L
  → (0 ≤ rngl_sin α2)%L
  → (0 ≤ rngl_sin (α1 + α2))%L
  → √((1 + rngl_cos (α1 + α2)) / 2)%L =
      (√((1 + rngl_cos α1) / 2) * √((1 + rngl_cos α2) / 2) -
       √((1 - rngl_cos α1) / 2) * √((1 - rngl_cos α2) / 2))%L.
Proof.
(* same goal but different hypotheses in the theorem
   rngl_sin_nonneg_sin_nonneg_add_cos_nonneg defined above;
   perhaps there is something to do? *)
(*
intros * Haov Hzs1 Hzs2 Hzs3.
apply rngl_sin_nonneg_sin_nonneg_add_cos_nonneg; try easy.
...
*)
destruct_ac.
intros * H12ns Hzs1 Hzs2 Hzs3.
destruct (Nat.eq_dec (rngl_characteristic T) 1) as [Hc1| Hc1]. {
  specialize (rngl_characteristic_1 Hos Hc1) as H1.
  rewrite H1.
  apply H1.
}
assert (Hz1ac :  ∀ α, (0 ≤ 1 + rngl_cos α)%L). {
  intros.
  apply (rngl_le_sub_le_add_l Hop Hor).
  progress unfold rngl_sub.
  rewrite Hop, rngl_add_0_l.
  apply rngl_cos_bound.
}
assert (Hz1sc : ∀ α, (0 ≤ 1 - rngl_cos α)%L). {
  intros.
  apply (rngl_le_add_le_sub_r Hop Hor).
  rewrite rngl_add_0_l.
  apply rngl_cos_bound.
}
assert (Ha12 : ∀ α1 α2, (0 ≤ (1 + rngl_cos α1) * (1 + rngl_cos α2))%L). {
  intros.
  apply (rngl_mul_nonneg_nonneg Hos Hor). {
    apply (rngl_le_sub_le_add_l Hop Hor).
    progress unfold rngl_sub.
    rewrite Hop, rngl_add_0_l.
    apply rngl_cos_bound.
  } {
    apply (rngl_le_sub_le_add_l Hop Hor).
    progress unfold rngl_sub.
    rewrite Hop, rngl_add_0_l.
    apply rngl_cos_bound.
  }
}
assert (Hs12 : ∀ α1 α2, (0 ≤ (1 - rngl_cos α1) * (1 - rngl_cos α2))%L). {
  intros.
  apply (rngl_mul_nonneg_nonneg Hos Hor). {
    apply (rngl_le_add_le_sub_l Hop Hor).
    rewrite rngl_add_0_r.
    apply rngl_cos_bound.
  } {
    apply (rngl_le_add_le_sub_l Hop Hor).
    rewrite rngl_add_0_r.
    apply rngl_cos_bound.
  }
}
specialize (rngl_0_lt_2 Hos Hc1 Hto) as Hz2.
specialize (rngl_2_neq_0 Hos Hc1 Hto) as H20.
assert (Hze2 : (0 ≤ 2)%L) by now apply rngl_lt_le_incl.
assert (Hs2z : (√2 ≠ 0)%L). {
  intros H.
  apply (f_equal rngl_squ) in H.
  rewrite rngl_squ_sqrt in H; [ | now apply rngl_lt_le_incl ].
  now rewrite (rngl_squ_0 Hos) in H.
}
rewrite (rl_sqrt_div Hop Hiv Hto); [ | easy | easy ].
rewrite (rl_sqrt_div Hop Hiv Hto); [ | easy | easy ].
rewrite (rl_sqrt_div Hop Hiv Hto); [ | easy | easy ].
rewrite (rl_sqrt_div Hop Hiv Hto); [ | easy | easy ].
rewrite (rl_sqrt_div Hop Hiv Hto); [ | easy | easy ].
do 2 rewrite (rngl_div_mul_mul_div Hic Hiv).
do 2 rewrite (rngl_mul_div_assoc Hiv).
rewrite <- rl_sqrt_mul; [ | easy | easy ].
rewrite <- rl_sqrt_mul; [ | easy | easy ].
rewrite (rngl_div_div Hos Hiv); [ | easy | easy ].
rewrite (rngl_div_div Hos Hiv); [ | easy | easy ].
rewrite <- rl_sqrt_mul; [ | easy | easy ].
rewrite fold_rngl_squ.
rewrite (rl_sqrt_squ Hop Hto).
rewrite (rngl_abs_nonneg_eq Hop Hor); [ | easy ].
rewrite <- (rngl_div_sub_distr_r Hop Hiv).
apply (rngl_mul_cancel_r Hi1 _ _ 2)%L; [ easy | ].
rewrite (rngl_div_mul Hiv); [ | easy ].
rewrite <- (rngl_abs_nonneg_eq Hop Hor (√_ / _ * _))%L. 2: {
  apply (rngl_mul_nonneg_nonneg Hos Hor); [ | easy ].
  apply (rngl_div_nonneg Hop Hiv Hto). 2: {
    apply rngl_le_neq.
    split; [ now apply rl_sqrt_nonneg | ].
    now apply not_eq_sym.
  }
  now apply rl_sqrt_nonneg.
}
remember (√(_ * _))%L as x eqn:Hx.
remember (√(_ * _))%L as y eqn:Hy in |-*.
destruct (rngl_ltb_dec x y) as [Hxy| Hxy]. {
  exfalso.
  apply (rngl_ltb_lt Heo), (rngl_nle_gt Hor) in Hxy.
  apply Hxy; clear Hxy.
  subst x y.
  apply rngl_add_cos_nonneg_sqrt_mul_le.
  destruct (rngl_leb_dec 0 (rngl_cos α1)) as [Hzc1| Hzc1]. {
    apply rngl_leb_le in Hzc1.
    now apply rngl_add_cos_nonneg_when_sin_nonneg.
  }
  destruct (rngl_leb_dec 0 (rngl_cos α2)) as [Hzc2| Hzc2]. {
    apply rngl_leb_le in Hzc2.
    rewrite angle_add_comm in Hzs3.
    rewrite rngl_add_comm.
    now apply rngl_add_cos_nonneg_when_sin_nonneg.
  }
  apply (rngl_leb_gt_iff Hto) in Hzc1, Hzc2.
  exfalso.
  apply (rngl_nlt_ge Hor) in Hzs3.
  apply Hzs3; clear Hzs3.
  cbn.
  (* special case for sin α2 = 0 *)
  destruct (rngl_eqb_dec (rngl_sin α2) 0) as [H2z| H2z]. {
    apply (rngl_eqb_eq Heo) in H2z.
    rewrite H2z, (rngl_mul_0_r Hos), rngl_add_0_r.
    destruct (rngl_eqb_dec (rngl_sin α1) 0) as [H1z| H1z]. {
      apply (rngl_eqb_eq Heo) in H1z.
      apply eq_rngl_sin_0 in H2z, H1z.
      destruct H2z as [H2z| H2z]. {
        subst α2.
        apply (rngl_nle_gt Hor) in Hzc2.
        exfalso; apply Hzc2; clear Hzc2; cbn.
        apply (rngl_0_le_1 Hos Hto).
      }
      destruct H12ns as [H12ns| H12ns]; [ | easy ].
      destruct H1z as [H1z| H1z]; [ | easy ].
      subst α1 α2.
      exfalso.
      apply (rngl_nle_gt Hor) in Hzc1.
      apply Hzc1; clear Hzc1; cbn.
      apply (rngl_0_le_1 Hos Hto).
    }
    apply (rngl_eqb_neq Heo) in H1z.
    apply (rngl_mul_pos_neg Hop Hiq Hor); [ | easy ].
    apply rngl_le_neq.
    split; [ easy | ].
    now apply not_eq_sym.
  }
  apply (rngl_eqb_neq Heo) in H2z.
  rewrite rngl_add_comm.
  apply (rngl_add_neg_nonpos Hop Hor). {
    rewrite (rngl_mul_comm Hic).
    apply (rngl_mul_pos_neg Hop Hiq Hor); [ | easy ].
    apply rngl_le_neq.
    split; [ easy | ].
    now apply not_eq_sym.
  }
  apply (rngl_mul_nonneg_nonpos Hop Hor); [ easy | ].
  now apply rngl_lt_le_incl.
}
apply (rngl_ltb_ge_iff Hto) in Hxy.
rewrite <- (rngl_abs_nonneg_eq Hop Hor). 2: {
  now apply (rngl_le_0_sub Hop Hor).
}
apply (eq_rngl_squ_rngl_abs Hop Hto). {
  rewrite Bool.orb_true_iff; right.
  apply (rngl_has_inv_has_inv_or_pdiv Hiv).
} {
  apply (rngl_mul_comm Hic).
}
rewrite (rngl_squ_mul Hic).
rewrite (rngl_squ_div Hic Hos Hiv); [ | easy ].
rewrite rngl_squ_sqrt; [ | easy ].
rewrite rngl_squ_sqrt; [ | easy ].
progress unfold rngl_squ at 1.
rewrite rngl_mul_assoc.
rewrite (rngl_div_mul Hiv); [ | easy ].
subst x y.
apply rngl_sin_nonneg_sin_nonneg_add_1_cos_add_sub.
apply rngl_leb_le in Hzs1, Hzs2.
congruence.
Qed.

Theorem rngl_sin_sub_anticomm :
  ∀ α1 α2, rngl_sin (α1 - α2) = (- rngl_sin (α2 - α1))%L.
Proof.
destruct_ac.
intros; cbn.
do 2 rewrite (rngl_mul_opp_r Hop).
do 2 rewrite (rngl_add_opp_r Hop).
rewrite (rngl_opp_sub_distr Hop).
rewrite (rngl_mul_comm Hic).
f_equal.
apply (rngl_mul_comm Hic).
Qed.

Theorem rngl_sin_add_straight_l :
  ∀ α, (rngl_sin (π + α) = - rngl_sin α)%L.
Proof.
destruct_ac.
intros; cbn.
rewrite (rngl_mul_0_l Hos).
rewrite rngl_add_0_l.
rewrite (rngl_mul_opp_l Hop).
f_equal.
apply rngl_mul_1_l.
Qed.

Theorem rngl_sin_sub_nonneg :
  ∀ α1 α2,
  (0 ≤ rngl_sin α1)%L
  → (0 ≤ rngl_sin α2)%L
  → (rngl_cos α1 ≤ rngl_cos α2)%L
  → (0 ≤ rngl_sin (α1 - α2))%L.
Proof.
destruct_ac.
intros * Hs1 Hs2 Hc12.
specialize rngl_sin_nonneg_cos_le_sin_le as H1.
specialize (H1 _ _ Hs1 Hs2 Hc12).
remember (0 ≤? rngl_cos α1)%L as zc1 eqn:Hzc1.
symmetry in Hzc1.
destruct zc1. {
  apply rngl_leb_le in Hzc1; cbn.
  rewrite (rngl_mul_opp_r Hop).
  rewrite (rngl_add_opp_r Hop).
  apply (rngl_le_0_sub Hop Hor).
  rewrite (rngl_mul_comm Hic).
  now apply (rngl_mul_le_compat_nonneg Hor).
} {
  apply (rngl_leb_gt_iff Hto) in Hzc1.
  remember (0 ≤? rngl_cos α2)%L as zc2 eqn:Hzc2.
  symmetry in Hzc2.
  destruct zc2; [ easy | ].
  apply (rngl_leb_gt_iff Hto) in Hzc2; cbn.
  rewrite (rngl_mul_opp_r Hop).
  rewrite (rngl_add_opp_r Hop).
  apply (rngl_le_0_sub Hop Hor).
  rewrite (rngl_mul_comm Hic).
  apply rngl_lt_le_incl in Hzc2.
  now apply (rngl_mul_le_compat_nonpos_nonneg Hop Hor).
}
Qed.

Theorem rngl_sin_sub_nonneg_iff :
  ∀ α1 α2,
  (0 < rngl_sin α1)%L
  → (0 ≤ rngl_sin α2)%L
  → (rngl_cos α1 ≤ rngl_cos α2)%L
  ↔ (0 ≤ rngl_sin (α1 - α2))%L.
Proof.
destruct_ac.
destruct (Nat.eq_dec (rngl_characteristic T) 1) as [Hc1| Hc1]. {
  specialize (rngl_characteristic_1 Hos Hc1) as H1.
  intros * Hs1 Hs2.
  do 2 rewrite (H1 (rngl_cos _)).
  now rewrite (H1 (rngl_sin _)).
}
intros * Hs1 Hs2.
split. {
  apply rngl_sin_sub_nonneg; try easy.
  now apply rngl_lt_le_incl.
}
intros Hs12.
apply (rngl_nlt_ge_iff Hto).
intros Hcc.
generalize Hcc; intros Hcc2.
apply rngl_lt_le_incl in Hcc2.
specialize rngl_sin_nonneg_cos_le_sin_le as H1.
generalize Hs1; intros Hs1'.
apply rngl_lt_le_incl in Hs1'.
specialize (H1 _ _ Hs2 Hs1' Hcc2).
remember (0 ≤? rngl_cos α2)%L as zc2 eqn:Hzc2.
symmetry in Hzc2.
destruct zc2. {
  apply rngl_leb_le in Hzc2.
  rewrite rngl_sin_sub_anticomm in Hs12.
  apply (rngl_opp_nonneg_nonpos Hop Hor) in Hs12.
  apply (rngl_nlt_ge Hor) in Hs12.
  apply Hs12; clear Hs12.
  apply rngl_le_neq.
  split; [ now apply rngl_sin_sub_nonneg | ].
  intros H; symmetry in H.
  apply eq_rngl_sin_0 in H.
  destruct H as [H| H]. {
    apply -> angle_sub_move_0_r in H.
    subst α2.
    now apply rngl_lt_irrefl in Hcc.
  }
  apply angle_sub_move_r in H.
  subst α2.
  rewrite rngl_sin_add_straight_l in Hs2.
  apply (rngl_opp_nonneg_nonpos Hop Hor) in Hs2.
  now apply (rngl_nle_gt Hor) in Hs1.
}
apply (rngl_leb_gt_iff Hto) in Hzc2.
remember (0 ≤? rngl_cos α1)%L as zc1 eqn:Hzc1.
symmetry in Hzc1.
destruct zc1. {
  apply rngl_leb_le in Hzc1.
  rewrite rngl_sin_sub_anticomm in Hs12.
  apply (rngl_opp_nonneg_nonpos Hop Hor) in Hs12.
  apply (rngl_le_antisymm Hor) in H1; [ | easy ].
  apply eq_rngl_sin_0 in H1.
  destruct H1. {
    apply -> angle_sub_move_0_r in H.
    subst α2.
    now apply rngl_lt_irrefl in Hcc.
  }
  apply angle_sub_move_r in H.
  subst α2.
  rewrite rngl_sin_add_straight_l in Hs2.
  apply (rngl_opp_nonneg_nonpos Hop Hor) in Hs2.
  now apply (rngl_nle_gt Hor) in Hs1.
}
apply (rngl_leb_gt_iff Hto) in Hzc1.
rewrite rngl_sin_sub_anticomm in Hs12.
apply (rngl_opp_nonneg_nonpos Hop Hor) in Hs12.
apply (rngl_nlt_ge Hor) in Hs12.
apply Hs12; clear Hs12.
apply rngl_le_neq.
split; [ now apply rngl_sin_sub_nonneg | ].
intros H; symmetry in H.
apply eq_rngl_sin_0 in H.
destruct H as [H| H]. {
  apply -> angle_sub_move_0_r in H.
  subst α2.
  now apply rngl_lt_irrefl in Hcc.
}
apply angle_sub_move_r in H.
subst α2.
rewrite rngl_sin_add_straight_l in Hs2.
apply (rngl_opp_nonneg_nonpos Hop Hor) in Hs2.
now apply (rngl_nle_gt Hor) in Hs1.
Qed.

(* to be completed
Theorem rngl_sin_sub_nonneg_iff' :
  ∀ α1 α2,
  α2 ≠ π
  → (0 ≤ rngl_sin α1)%L
  → (0 ≤ rngl_sin α2)%L
  → (rngl_cos α1 ≤ rngl_cos α2)%L
  ↔ (0 ≤ rngl_sin (α1 - α2))%L.
Proof.
destruct_ac.
destruct (Nat.eq_dec (rngl_characteristic T) 1) as [Hc1| Hc1]. {
  specialize (rngl_characteristic_1 Hos Hc1) as H1.
  intros * H1p Hs1 Hs2.
  do 2 rewrite (H1 (rngl_cos _)).
  now rewrite (H1 (rngl_sin _)).
}
intros * H2p Hs1 Hs2.
(**)
clear H2p.
destruct (angle_eq_dec α2 π) as [H2p| H2p]. {
  subst α2.
  rewrite rngl_sin_sub_straight_r.
  cbn.
  split; intros H1. {
Search (rngl_cos _ = (-1)%L).
...
    assert (H : rngl_cos α1 = (-1)%L). {
      apply eq_rngl_cos_opp_1.
...
    apply (rngl_opp_nonneg_nonpos Hop Hor).
    apply rngl_cos_le_opp_1 in H1.
...
split; [ now apply rngl_sin_sub_nonneg | ].
intros Hs12.
apply (rngl_lt_eq_cases Hor) in Hs1.
destruct Hs1 as [Hs1| Hs1]; [ now apply rngl_sin_sub_nonneg_iff | ].
symmetry in Hs1.
apply eq_rngl_sin_0 in Hs1.
destruct Hs1; subst α1; [ cbn | apply rngl_cos_bound ].
rewrite angle_sub_0_l in Hs12.
cbn in Hs12.
apply (rngl_opp_nonneg_nonpos Hop Hor) in Hs12.
apply (rngl_le_antisymm Hor) in Hs2; [ | easy ].
apply eq_rngl_sin_0 in Hs2.
destruct Hs2 as [Hs2| Hs2]; subst α2; [ | easy ].
apply (rngl_le_refl Hor).
Qed.
...
*)

Theorem rngl_characteristic_1_angle_0 :
  rngl_characteristic T = 1 →
  ∀ α, (α = 0)%A.
Proof.
destruct_ac.
intros Hc1 *.
specialize (rngl_characteristic_1 Hos Hc1) as H1.
apply eq_angle_eq.
do 2 rewrite (H1 (rngl_cos _)).
now do 2 rewrite (H1 (rngl_sin _)).
Qed.

Theorem rngl_add_cos_neg_when_sin_nonneg_neg :
  ∀ α1 α2,
  (0 ≤ rngl_sin α1)%L
  → (0 ≤ rngl_sin α2)%L
  → (rngl_sin (α1 + α2) < 0)%L
  → (0 ≤ rngl_cos α1)%L
  → (rngl_cos α1 + rngl_cos α2 < 0)%L.
Proof.
destruct_ac.
intros * Hzs1 Hzs2 Hs3z Hzc1.
destruct (Nat.eq_dec (rngl_characteristic T) 1) as [Hc1| Hc1]. {
  specialize (rngl_characteristic_1 Hos Hc1) as H1.
  rewrite (H1 (rngl_sin _)) in Hs3z.
  now apply rngl_lt_irrefl in Hs3z.
}
remember (α1 + α2)%A as α3 eqn:Hα3.
destruct (rngl_leb_dec 0 (rngl_cos α2)) as [Hzc2| Hzc2]. {
  apply rngl_leb_le in Hzc2.
  apply (rngl_nle_gt Hor) in Hs3z.
  exfalso; apply Hs3z; clear Hs3z.
  rewrite Hα3; cbn.
  apply (rngl_le_0_add Hos Hor). {
    now apply (rngl_mul_nonneg_nonneg Hos Hor).
  } {
    now apply (rngl_mul_nonneg_nonneg Hos Hor).
  }
}
apply (rngl_leb_gt_iff Hto) in Hzc2.
apply (rngl_nle_gt_iff Hto).
intros Hcc.
assert (Hs21 : (rngl_sin α1 ≤ rngl_sin α2)%L). {
  remember (π - α2)%A as α eqn:Hα.
  symmetry in Hα.
  apply angle_sub_move_l in Hα.
  subst α2; rename α into α2.
  move α2 before α1.
  rewrite rngl_cos_sub_straight_l in Hcc, Hzc2.
  rewrite rngl_sin_sub_straight_l in Hzs2 |-*.
  rewrite (rngl_add_opp_r Hop) in Hcc.
  apply -> (rngl_le_0_sub Hop Hor) in Hcc.
  apply (rngl_opp_neg_pos Hop Hor) in Hzc2.
  move Hzc2 before Hzc1.
  apply rngl_lt_le_incl in Hzc2.
  now apply rngl_cos_cos_sin_sin_nonneg_sin_le_cos_le_iff.
}
apply (rngl_nle_gt Hor) in Hs3z.
apply Hs3z; clear Hs3z.
rewrite Hα3; cbn.
rewrite rngl_add_comm.
replace (rngl_cos α1) with (rngl_cos α1 + rngl_cos α2 - rngl_cos α2)%L. 2: {
  apply (rngl_add_sub Hos).
}
rewrite (rngl_mul_sub_distr_r Hop).
rewrite <- (rngl_sub_sub_distr Hop).
rewrite (rngl_mul_comm Hic (rngl_cos α2)).
rewrite <- (rngl_mul_sub_distr_r Hop).
progress unfold rngl_sub at 1.
rewrite Hop.
rewrite <- (rngl_mul_opp_r Hop).
(* ok, all terms are non negative *)
apply (rngl_le_0_add Hos Hor). {
  now apply (rngl_mul_nonneg_nonneg Hos Hor).
}
apply (rngl_mul_nonneg_nonneg Hos Hor). {
  now apply (rngl_le_0_sub Hop Hor).
} {
  apply (rngl_opp_nonneg_nonpos Hop Hor).
  now apply rngl_lt_le_incl.
}
Qed.

Theorem rngl_cos_opp : ∀ α, rngl_cos (- α) = rngl_cos α.
Proof. easy. Qed.

Theorem rngl_sin_opp : ∀ α, rngl_sin (- α) = (- rngl_sin α)%L.
Proof. easy. Qed.

Theorem rngl_add_cos_nonneg_when_sin_nonpos :
  ∀ α1 α2,
  (rngl_sin α1 ≤ 0)%L
  → (rngl_sin α2 ≤ 0)%L
  → (rngl_sin (α1 + α2) ≤ 0)%L
  → (0 ≤ rngl_cos α1)%L
  → (0 ≤ rngl_cos α1 + rngl_cos α2)%L.
Proof.
destruct_ac.
intros * Hzs1 Hzs2 Hzs3 Hzc1.
rewrite <- rngl_cos_opp.
rewrite <- (rngl_cos_opp α2).
apply rngl_add_cos_nonneg_when_sin_nonneg. {
  rewrite rngl_sin_opp.
  now apply (rngl_opp_nonneg_nonpos Hop Hor).
} {
  rewrite rngl_sin_opp.
  now apply (rngl_opp_nonneg_nonpos Hop Hor).
} {
  rewrite angle_add_opp_r.
  rewrite <- angle_opp_add_distr.
  rewrite rngl_sin_opp.
  apply (rngl_opp_nonneg_nonpos Hop Hor).
  now rewrite angle_add_comm.
} {
  now rewrite rngl_cos_opp.
}
Qed.

Theorem rngl_sin_add_straight_r :
  ∀ α, (rngl_sin (α + π) = - rngl_sin α)%L.
Proof.
destruct_ac.
intros; cbn.
rewrite (rngl_mul_0_r Hos).
rewrite rngl_add_0_r.
rewrite (rngl_mul_opp_r Hop).
f_equal.
apply rngl_mul_1_r.
Qed.

Theorem rngl_sin_sub_nonneg_sin_le_sin :
  ∀ α1 α2,
  (0 ≤ rngl_sin α1)%L
  → (0 ≤ rngl_cos α1)%L
  → (0 ≤ rngl_sin (α1 - α2))%L
  → (rngl_sin α2 ≤ rngl_sin α1)%L.
Proof.
destruct_ac; intros * Hzs1 Hcs1 Hzs12.
cbn in Hzs12.
rewrite rngl_add_comm in Hzs12.
rewrite (rngl_mul_opp_r Hop) in Hzs12.
rewrite (rngl_add_opp_l Hop) in Hzs12.
apply -> (rngl_le_0_sub Hop Hor) in Hzs12.
apply (rngl_mul_le_mono_nonneg_l Hop Hor (rngl_cos α1)) in Hzs12;
  [ | easy ].
rewrite rngl_mul_assoc in Hzs12.
rewrite fold_rngl_squ in Hzs12.
specialize (cos2_sin2_1 α1) as H1.
apply (rngl_add_move_r Hop) in H1.
rewrite H1 in Hzs12; clear H1.
rewrite (rngl_mul_sub_distr_r Hop) in Hzs12.
rewrite rngl_mul_1_l in Hzs12.
apply (rngl_le_sub_le_add_r Hop Hor) in Hzs12.
rewrite (rngl_mul_comm Hic) in Hzs12.
progress unfold rngl_squ in Hzs12.
do 2 rewrite <- rngl_mul_assoc in Hzs12.
rewrite <- rngl_mul_add_distr_l in Hzs12.
rewrite (rngl_mul_comm Hic (rngl_cos α2)) in Hzs12.
rewrite <- rngl_cos_sub in Hzs12.
eapply (rngl_le_trans Hor); [ apply Hzs12 | ].
apply (rngl_le_0_sub Hop Hor).
rewrite (rngl_sub_mul_r_diag_l Hop).
apply (rngl_mul_nonneg_nonneg Hos Hor); [ easy | ].
apply (rngl_le_0_sub Hop Hor).
apply rngl_cos_bound.
Qed.

Theorem rngl_sin_nonneg_sin_nonneg_add_1_cos_add_add :
  ∀ α1 α2,
  (0 ≤? rngl_sin α1)%L = (0 ≤? rngl_sin α2)%L
  → ((1 + rngl_cos (α1 - α2)) * 2)%L =
      (√((1 + rngl_cos α1) * (1 + rngl_cos α2)) +
       √((1 - rngl_cos α1) * (1 - rngl_cos α2)))²%L.
Proof.
intros * Hzs12.
(* proof borrowed from rngl_sin_nonneg_sin_nonneg_add_1_cos_add_sub
   and it works: perhaps there is a way to unify these two theorems *)
destruct_ac.
assert (Ha12 : ∀ α1 α2, (0 ≤ (1 + rngl_cos α1) * (1 + rngl_cos α2))%L). {
  intros.
  apply (rngl_mul_nonneg_nonneg Hos Hor). {
    apply (rngl_le_sub_le_add_l Hop Hor).
    progress unfold rngl_sub.
    rewrite Hop, rngl_add_0_l.
    apply rngl_cos_bound.
  } {
    apply (rngl_le_sub_le_add_l Hop Hor).
    progress unfold rngl_sub.
    rewrite Hop, rngl_add_0_l.
    apply rngl_cos_bound.
  }
}
assert (Hs12 : ∀ α1 α2, (0 ≤ (1 - rngl_cos α1) * (1 - rngl_cos α2))%L). {
  intros.
  apply (rngl_mul_nonneg_nonneg Hos Hor). {
    apply (rngl_le_add_le_sub_l Hop Hor).
    rewrite rngl_add_0_r.
    apply rngl_cos_bound.
  } {
    apply (rngl_le_add_le_sub_l Hop Hor).
    rewrite rngl_add_0_r.
    apply rngl_cos_bound.
  }
}
rewrite (rngl_squ_add Hic).
rewrite rngl_squ_sqrt; [ | easy ].
rewrite rngl_squ_sqrt; [ | easy ].
rewrite rngl_add_add_swap.
rewrite <- rngl_mul_assoc.
rewrite <- rl_sqrt_mul; [ | easy | easy ].
rewrite rngl_mul_assoc.
rewrite (rngl_mul_mul_swap Hic (1 + rngl_cos α1))%L.
rewrite <- rngl_mul_assoc.
do 2 rewrite (rngl_squ_sub_squ' Hop).
do 2 rewrite rngl_mul_1_r, rngl_mul_1_l.
do 2 rewrite (rngl_add_sub Hos).
rewrite rngl_squ_1.
replace (1 - rngl_cos² α1)%L with (rngl_sin² α1). 2: {
  symmetry.
  apply (rngl_add_sub_eq_l Hos).
  apply cos2_sin2_prop_add_squ.
  apply rngl_cos2_sin2.
}
replace (1 - rngl_cos² α2)%L with (rngl_sin² α2). 2: {
  symmetry.
  apply (rngl_add_sub_eq_l Hos).
  apply cos2_sin2_prop_add_squ.
  apply rngl_cos2_sin2.
}
rewrite rl_sqrt_mul; cycle 1. {
  apply (rngl_squ_nonneg Hos Hto).
} {
  apply (rngl_squ_nonneg Hos Hto).
}
do 2 rewrite (rl_sqrt_squ Hop Hto).
rewrite (rngl_mul_add_distr_l (1 + rngl_cos α1))%L.
rewrite rngl_mul_1_r.
rewrite (rngl_mul_add_distr_r 1 (rngl_cos α1))%L.
rewrite rngl_mul_1_l.
rewrite (rngl_mul_sub_distr_l Hop (1 - rngl_cos α1))%L.
rewrite rngl_mul_1_r.
rewrite (rngl_mul_sub_distr_r Hop 1 (rngl_cos α1))%L.
rewrite rngl_mul_1_l.
rewrite rngl_add_assoc.
rewrite (rngl_add_sub_assoc Hop (1 + _ + _ + _ * _))%L.
rewrite (rngl_add_sub_assoc Hop _ 1 (rngl_cos α1))%L.
rewrite (rngl_sub_sub_distr Hop _ (rngl_cos α2)).
rewrite (rngl_add_add_swap (1 + _ + _))%L.
rewrite (rngl_add_add_swap _ (rngl_cos α2) 1)%L.
rewrite (rngl_add_add_swap _ (rngl_cos α1) 1)%L.
rewrite (rngl_add_sub_swap Hop _ _ (rngl_cos α1)).
rewrite (rngl_add_sub_swap Hop _ _ (rngl_cos α1)).
rewrite (rngl_add_sub Hos).
rewrite (rngl_add_sub_swap Hop _ _ (rngl_cos α2)).
rewrite (rngl_add_sub Hos).
rewrite <- (rngl_add_assoc 2)%L.
rewrite <- (rngl_mul_2_l (rngl_cos α1 * _)%L).
rewrite rngl_add_mul_r_diag_l.
rewrite <- rngl_mul_add_distr_l.
rewrite (rngl_mul_comm Hic).
f_equal.
rewrite <- rngl_add_assoc.
f_equal; cbn.
rewrite (rngl_mul_opp_r Hop).
rewrite (rngl_sub_opp_r Hop).
f_equal.
remember (0 ≤? rngl_sin α2)%L as zs2 eqn:Hzs2.
symmetry in Hzs2.
destruct zs2. {
  apply rngl_leb_le in Hzs2, Hzs12.
  rewrite (rngl_abs_nonneg_eq Hop Hor); [ | easy ].
  rewrite (rngl_abs_nonneg_eq Hop Hor); [ | easy ].
  easy.
} {
  apply (rngl_leb_gt_iff Hto) in Hzs2, Hzs12.
  apply rngl_lt_le_incl in Hzs2, Hzs12.
  rewrite (rngl_abs_nonpos_eq Hop Hto); [ | easy ].
  rewrite (rngl_abs_nonpos_eq Hop Hto); [ | easy ].
  rewrite (rngl_mul_opp_l Hop).
  rewrite (rngl_mul_opp_r Hop).
  symmetry.
  apply (rngl_opp_involutive Hop).
}
Qed.

Theorem rngl_sin_nonneg_sin_neg_sin_add_neg :
  ∀ α1 α2,
  (0 ≤ rngl_sin α1)%L
  → (rngl_sin α2 ≤ 0)%L
  → √((1 + rngl_cos (α1 + α2)) / 2)%L =
     (√((1 - rngl_cos α1) / 2) * √((1 - rngl_cos α2) / 2) +
      √((1 + rngl_cos α1) / 2) * √((1 + rngl_cos α2) / 2))%L.
Proof.
intros * Hzs1 Hzs2.
destruct_ac.
destruct (Nat.eq_dec (rngl_characteristic T) 1) as [Hc1| Hc1]. {
  specialize (rngl_characteristic_1 Hos Hc1) as H1.
  rewrite H1; apply H1.
}
specialize (rngl_0_lt_2 Hos Hc1 Hto) as Hz2.
specialize (rngl_2_neq_0 Hos Hc1 Hto) as H20.
assert (Hze2 : (0 ≤ 2)%L) by now apply rngl_lt_le_incl.
assert (Hz1ac :  ∀ α, (0 ≤ 1 + rngl_cos α)%L). {
  intros.
  apply (rngl_le_sub_le_add_l Hop Hor).
  progress unfold rngl_sub.
  rewrite Hop, rngl_add_0_l.
  apply rngl_cos_bound.
}
assert (Hz1sc : ∀ α, (0 ≤ 1 - rngl_cos α)%L). {
  intros.
  apply (rngl_le_add_le_sub_r Hop Hor).
  rewrite rngl_add_0_l.
  apply rngl_cos_bound.
}
assert (Hs2z : (√2 ≠ 0)%L). {
  intros H.
  apply (f_equal rngl_squ) in H.
  rewrite rngl_squ_sqrt in H; [ | now apply rngl_lt_le_incl ].
  now rewrite (rngl_squ_0 Hos) in H.
}
assert (Ha12 : ∀ α1 α2, (0 ≤ (1 + rngl_cos α1) * (1 + rngl_cos α2))%L). {
  intros.
  apply (rngl_mul_nonneg_nonneg Hos Hor). {
    apply (rngl_le_sub_le_add_l Hop Hor).
    progress unfold rngl_sub.
    rewrite Hop, rngl_add_0_l.
    apply rngl_cos_bound.
  } {
    apply (rngl_le_sub_le_add_l Hop Hor).
    progress unfold rngl_sub.
    rewrite Hop, rngl_add_0_l.
    apply rngl_cos_bound.
  }
}
assert (Hs12 : ∀ α1 α2, (0 ≤ (1 - rngl_cos α1) * (1 - rngl_cos α2))%L). {
  intros.
  apply (rngl_mul_nonneg_nonneg Hos Hor). {
    apply (rngl_le_add_le_sub_l Hop Hor).
    rewrite rngl_add_0_r.
    apply rngl_cos_bound.
  } {
    apply (rngl_le_add_le_sub_l Hop Hor).
    rewrite rngl_add_0_r.
    apply rngl_cos_bound.
  }
}
rewrite (rl_sqrt_div Hop Hiv Hto); [ | easy | easy ].
rewrite (rl_sqrt_div Hop Hiv Hto); [ | easy | easy ].
rewrite (rl_sqrt_div Hop Hiv Hto); [ | easy | easy ].
rewrite (rl_sqrt_div Hop Hiv Hto); [ | easy | easy ].
rewrite (rl_sqrt_div Hop Hiv Hto); [ | easy | easy ].
do 2 rewrite (rngl_div_mul_mul_div Hic Hiv).
do 2 rewrite (rngl_mul_div_assoc Hiv).
rewrite <- rl_sqrt_mul; [ | easy | easy ].
rewrite <- rl_sqrt_mul; [ | easy | easy ].
rewrite (rngl_div_div Hos Hiv); [ | easy | easy ].
rewrite (rngl_div_div Hos Hiv); [ | easy | easy ].
rewrite <- rl_sqrt_mul; [ | easy | easy ].
rewrite fold_rngl_squ.
rewrite (rl_sqrt_squ Hop Hto).
rewrite (rngl_abs_nonneg_eq Hop Hor); [ | easy ].
rewrite <- (rngl_div_add_distr_r Hiv).
apply (rngl_mul_cancel_r Hi1 _ _ 2)%L; [ easy | ].
rewrite (rngl_div_mul Hiv); [ | easy ].
rewrite <- (rngl_abs_nonneg_eq Hop Hor (√_ / _ * _))%L. 2: {
  apply (rngl_mul_nonneg_nonneg Hos Hor); [ | easy ].
  apply (rngl_div_nonneg Hop Hiv Hto). 2: {
    apply rngl_le_neq.
    split; [ now apply rl_sqrt_nonneg | ].
    now apply not_eq_sym.
  }
  now apply rl_sqrt_nonneg.
}
rewrite <- (rngl_abs_nonneg_eq Hop Hor). 2: {
  now apply (rngl_le_0_add Hos Hor); apply rl_sqrt_nonneg.
}
apply (eq_rngl_squ_rngl_abs Hop Hto). {
  rewrite Bool.orb_true_iff; right.
  apply (rngl_has_inv_has_inv_or_pdiv Hiv).
} {
  apply (rngl_mul_comm Hic).
}
rewrite (rngl_squ_mul Hic).
rewrite (rngl_squ_div Hic Hos Hiv); [ | easy ].
rewrite rngl_squ_sqrt; [ | easy ].
rewrite rngl_squ_sqrt; [ | easy ].
progress unfold rngl_squ at 1.
rewrite rngl_mul_assoc.
rewrite (rngl_div_mul Hiv); [ | easy ].
rewrite <- (rngl_squ_opp Hop).
rewrite (rngl_squ_opp Hop).
rewrite (rngl_add_comm (√_))%L.
remember (- α2)%A as α eqn:Hα.
symmetry in Hα.
rewrite <- angle_opp_involutive in Hα.
apply angle_opp_inj in Hα.
subst α2; rename α into α2.
move α2 before α1.
rewrite rngl_sin_opp in Hzs2.
rewrite <- (rngl_opp_0 Hop) in Hzs2.
apply (rngl_opp_le_compat Hop Hor) in Hzs2.
rewrite angle_add_opp_r.
rewrite rngl_cos_opp.
apply rngl_sin_nonneg_sin_nonneg_add_1_cos_add_add.
apply rngl_leb_le in Hzs1, Hzs2.
congruence.
Qed.

Theorem rngl_sin_nonneg_sin_nonneg_add_cos_nonneg :
  ∀ α1 α2,
  (0 ≤ rngl_sin α1)%L
  → (0 ≤ rngl_sin α2)%L
  → (0 ≤ rngl_cos α1 + rngl_cos α2)%L
  → √((1 + rngl_cos (α1 + α2)) / 2)%L =
    (√((1 + rngl_cos α1) / 2) * √((1 + rngl_cos α2) / 2) -
     √((1 - rngl_cos α1) / 2) * √((1 - rngl_cos α2) / 2))%L.
Proof.
intros * Hzs1 Hzs2 Hzc12.
destruct_ac.
destruct (Nat.eq_dec (rngl_characteristic T) 1) as [Hc1| Hc1]. {
  specialize (rngl_characteristic_1 Hos Hc1) as H1.
  rewrite H1.
  apply H1.
}
assert (Hz1ac :  ∀ α, (0 ≤ 1 + rngl_cos α)%L). {
  intros.
  apply (rngl_le_sub_le_add_l Hop Hor).
  progress unfold rngl_sub.
  rewrite Hop, rngl_add_0_l.
  apply rngl_cos_bound.
}
assert (Hz1sc : ∀ α, (0 ≤ 1 - rngl_cos α)%L). {
  intros.
  apply (rngl_le_add_le_sub_r Hop Hor).
  rewrite rngl_add_0_l.
  apply rngl_cos_bound.
}
assert (Ha12 : ∀ α1 α2, (0 ≤ (1 + rngl_cos α1) * (1 + rngl_cos α2))%L). {
  intros.
  apply (rngl_mul_nonneg_nonneg Hos Hor). {
    apply (rngl_le_sub_le_add_l Hop Hor).
    progress unfold rngl_sub.
    rewrite Hop, rngl_add_0_l.
    apply rngl_cos_bound.
  } {
    apply (rngl_le_sub_le_add_l Hop Hor).
    progress unfold rngl_sub.
    rewrite Hop, rngl_add_0_l.
    apply rngl_cos_bound.
  }
}
assert (Hs12 : ∀ α1 α2, (0 ≤ (1 - rngl_cos α1) * (1 - rngl_cos α2))%L). {
  intros.
  apply (rngl_mul_nonneg_nonneg Hos Hor). {
    apply (rngl_le_add_le_sub_l Hop Hor).
    rewrite rngl_add_0_r.
    apply rngl_cos_bound.
  } {
    apply (rngl_le_add_le_sub_l Hop Hor).
    rewrite rngl_add_0_r.
    apply rngl_cos_bound.
  }
}
specialize (rngl_0_lt_2 Hos Hc1 Hto) as Hz2.
specialize (rngl_2_neq_0 Hos Hc1 Hto) as H20.
assert (Hze2 : (0 ≤ 2)%L) by now apply rngl_lt_le_incl.
assert (Hs2z : (√2 ≠ 0)%L). {
  intros H.
  apply (f_equal rngl_squ) in H.
  rewrite rngl_squ_sqrt in H; [ | now apply rngl_lt_le_incl ].
  now rewrite (rngl_squ_0 Hos) in H.
}
rewrite (rl_sqrt_div Hop Hiv Hto); [ | easy | easy ].
rewrite (rl_sqrt_div Hop Hiv Hto); [ | easy | easy ].
rewrite (rl_sqrt_div Hop Hiv Hto); [ | easy | easy ].
rewrite (rl_sqrt_div Hop Hiv Hto); [ | easy | easy ].
rewrite (rl_sqrt_div Hop Hiv Hto); [ | easy | easy ].
do 2 rewrite (rngl_div_mul_mul_div Hic Hiv).
do 2 rewrite (rngl_mul_div_assoc Hiv).
rewrite <- rl_sqrt_mul; [ | easy | easy ].
rewrite <- rl_sqrt_mul; [ | easy | easy ].
rewrite (rngl_div_div Hos Hiv); [ | easy | easy ].
rewrite (rngl_div_div Hos Hiv); [ | easy | easy ].
rewrite <- rl_sqrt_mul; [ | easy | easy ].
rewrite fold_rngl_squ.
rewrite (rl_sqrt_squ Hop Hto).
rewrite (rngl_abs_nonneg_eq Hop Hor); [ | easy ].
rewrite <- (rngl_div_sub_distr_r Hop Hiv).
apply (rngl_mul_cancel_r Hi1 _ _ 2)%L; [ easy | ].
rewrite (rngl_div_mul Hiv); [ | easy ].
rewrite <- (rngl_abs_nonneg_eq Hop Hor (√_ / _ * _))%L. 2: {
  apply (rngl_mul_nonneg_nonneg Hos Hor); [ | easy ].
  apply (rngl_div_nonneg Hop Hiv Hto). 2: {
    apply rngl_le_neq.
    split; [ now apply rl_sqrt_nonneg | ].
    now apply not_eq_sym.
  }
  now apply rl_sqrt_nonneg.
}
rewrite <- (rngl_abs_nonneg_eq Hop Hor). 2: {
  apply (rngl_le_0_sub Hop Hor).
  now apply rngl_add_cos_nonneg_sqrt_mul_le.
}
apply (eq_rngl_squ_rngl_abs Hop Hto Hii). {
  apply (rngl_mul_comm Hic).
}
rewrite (rngl_squ_mul Hic).
rewrite (rngl_squ_div Hic Hos Hiv); [ | easy ].
rewrite rngl_squ_sqrt; [ | easy ].
rewrite rngl_squ_sqrt; [ | easy ].
progress unfold rngl_squ at 1.
rewrite rngl_mul_assoc.
rewrite (rngl_div_mul Hiv); [ | easy ].
rewrite <- (rngl_squ_opp Hop).
rewrite (rngl_squ_opp Hop).
rewrite (rngl_squ_sub Hop Hic).
rewrite rngl_squ_sqrt; [ | easy ].
rewrite rngl_squ_sqrt; [ | easy ].
rewrite <- (rngl_add_sub_swap Hop).
rewrite <- rngl_mul_assoc.
rewrite <- rl_sqrt_mul; [ | easy | easy ].
rewrite rngl_mul_assoc.
rewrite (rngl_mul_mul_swap Hic (1 + rngl_cos α1))%L.
rewrite <- rngl_mul_assoc.
do 2 rewrite (rngl_squ_sub_squ' Hop).
do 2 rewrite rngl_mul_1_r, rngl_mul_1_l.
do 2 rewrite (rngl_add_sub Hos).
rewrite rngl_squ_1.
replace (1 - rngl_cos² α1)%L with (rngl_sin² α1). 2: {
  symmetry.
  apply (rngl_add_sub_eq_l Hos).
  apply cos2_sin2_prop_add_squ.
  apply rngl_cos2_sin2.
}
replace (1 - rngl_cos² α2)%L with (rngl_sin² α2). 2: {
  symmetry.
  apply (rngl_add_sub_eq_l Hos).
  apply cos2_sin2_prop_add_squ.
  apply rngl_cos2_sin2.
}
rewrite rl_sqrt_mul; cycle 1. {
  apply (rngl_squ_nonneg Hos Hto).
} {
  apply (rngl_squ_nonneg Hos Hto).
}
do 2 rewrite (rl_sqrt_squ Hop Hto).
rewrite (rngl_mul_add_distr_l (1 + rngl_cos α1))%L.
rewrite rngl_mul_1_r.
rewrite (rngl_mul_add_distr_r 1 (rngl_cos α1))%L.
rewrite rngl_mul_1_l.
rewrite (rngl_mul_sub_distr_l Hop (1 - rngl_cos α1))%L.
rewrite rngl_mul_1_r.
rewrite (rngl_mul_sub_distr_r Hop 1 (rngl_cos α1))%L.
rewrite rngl_mul_1_l.
rewrite rngl_add_assoc.
rewrite (rngl_add_sub_assoc Hop (1 + _ + _ + _ * _))%L.
rewrite (rngl_add_sub_assoc Hop _ 1 (rngl_cos α1))%L.
rewrite (rngl_sub_sub_distr Hop _ (rngl_cos α2)).
rewrite (rngl_add_add_swap (1 + _ + _))%L.
rewrite (rngl_add_add_swap _ (rngl_cos α2) 1)%L.
rewrite (rngl_add_add_swap _ (rngl_cos α1) 1)%L.
rewrite (rngl_add_sub_swap Hop _ _ (rngl_cos α1)).
rewrite (rngl_add_sub_swap Hop _ _ (rngl_cos α1)).
rewrite (rngl_add_sub Hos).
rewrite (rngl_add_sub_swap Hop _ _ (rngl_cos α2)).
rewrite (rngl_add_sub Hos).
rewrite <- (rngl_add_assoc 2)%L.
rewrite <- (rngl_mul_2_l (rngl_cos α1 * _)%L).
rewrite rngl_add_mul_r_diag_l.
rewrite <- (rngl_mul_sub_distr_l Hop).
rewrite (rngl_mul_comm Hic).
f_equal.
rewrite <- (rngl_add_sub_assoc Hop).
f_equal; cbn.
progress unfold rngl_sub.
rewrite Hop.
f_equal.
f_equal.
rewrite (rngl_abs_nonneg_eq Hop Hor); [ | easy ].
rewrite (rngl_abs_nonneg_eq Hop Hor); [ | easy ].
easy.
Qed.

Theorem rngl_sin_sub_right_l :
  ∀ α, rngl_sin (π/₂ - α) = rngl_cos α.
Proof.
destruct_ac.
intros; cbn.
rewrite (rngl_mul_0_l Hos).
rewrite rngl_add_0_r.
apply rngl_mul_1_l.
Qed.

Theorem rngl_sin_sub_right_r :
  ∀ α, rngl_sin (α - π/₂) = (- rngl_cos α)%L.
Proof.
destruct_ac.
intros; cbn.
rewrite (rngl_mul_0_r Hos).
rewrite rngl_add_0_l.
rewrite (rngl_mul_opp_r Hop).
f_equal.
apply rngl_mul_1_r.
Qed.

Theorem rngl_cos_sub_right_r :
  ∀ α, rngl_cos (α - π/₂) = rngl_sin α.
Proof.
destruct_ac.
intros; cbn.
rewrite (rngl_mul_0_r Hos).
rewrite (rngl_sub_0_l Hop).
rewrite (rngl_mul_opp_r Hop).
rewrite (rngl_opp_involutive Hop).
apply rngl_mul_1_r.
Qed.

Theorem rngl_cos_sub_right_l :
  ∀ α, rngl_cos (π/₂ - α) = rngl_sin α.
Proof.
destruct_ac.
intros; cbn.
rewrite (rngl_mul_0_l Hos).
rewrite rngl_mul_1_l.
rewrite (rngl_sub_opp_r Hop).
apply rngl_add_0_l.
Qed.

Theorem rngl_cos_sub_comm : ∀ α1 α2, rngl_cos (α1 - α2) = rngl_cos (α2 - α1).
Proof.
destruct_ac.
intros; cbn.
rewrite (rngl_mul_comm Hic).
f_equal.
do 2 rewrite (rngl_mul_opp_r Hop).
f_equal.
apply (rngl_mul_comm Hic).
Qed.

Theorem rngl_cos_lt_cos_sub :
  ∀ α1 α2,
  (0 ≤ rngl_sin α1)%L
  → (0 < rngl_sin α2)%L
  → (rngl_cos α1 ≤ rngl_cos α2)%L
  → (rngl_cos α1 < rngl_cos (α2 - α1))%L.
Proof.
destruct_ac.
intros * Hzs1 Hzs2 Hc12z.
destruct (Nat.eq_dec (rngl_characteristic T) 1) as [Hc1| Hc1]. {
  specialize (rngl_characteristic_1 Hos Hc1) as H1.
  rewrite H1 in Hzs2.
  now apply rngl_lt_irrefl in Hzs2.
}
specialize (rngl_0_lt_2 Hos Hc1 Hto) as Hz2.
assert (Hze2 : (0 ≤ 2)%L) by now apply rngl_lt_le_incl.
cbn.
rewrite (rngl_mul_opp_r Hop).
rewrite (rngl_sub_opp_r Hop).
rewrite (rngl_mul_comm Hic (rngl_cos α2)).
rewrite (rngl_mul_comm Hic (rngl_sin α2)).
apply (rngl_lt_sub_lt_add_l Hop Hor).
rewrite (rngl_sub_mul_r_diag_l Hop).
rewrite <- (rngl_abs_nonneg_eq Hop Hor). 2: {
  apply rngl_lt_le_incl in Hzs2.
  now apply (rngl_mul_nonneg_nonneg Hos Hor).
}
destruct (rngl_ltb_dec (rngl_cos α1) 0) as [Hc1z| Hzc1]. {
  apply (rngl_ltb_lt Heo) in Hc1z.
  destruct (rngl_eqb_dec (rngl_cos α2) 1) as [Hc21| Hc21]. {
    apply (rngl_eqb_eq Heo) in Hc21.
    apply eq_rngl_cos_1 in Hc21.
    subst α2.
    now apply rngl_lt_irrefl in Hzs2.
  }
  apply (rngl_eqb_neq Heo) in Hc21.
  apply (rngl_lt_le_trans Hor _ 0). {
    rewrite (rngl_mul_comm Hic).
    apply (rngl_mul_pos_neg Hop Hiq Hor); [ | easy ].
    apply (rngl_lt_0_sub Hop Hor).
    apply rngl_le_neq.
    split; [ apply rngl_cos_bound | easy ].
  }
  apply (rngl_abs_nonneg Hop Hto).
}
apply (rngl_ltb_ge_iff Hto) in Hzc1.
rewrite <- (rngl_abs_nonneg_eq Hop Hor (rngl_cos α1 * _))%L. 2: {
  apply (rngl_mul_nonneg_nonneg Hos Hor); [ easy | ].
  apply (rngl_le_0_sub Hop Hor).
  apply rngl_cos_bound.
}
apply (rngl_squ_lt_abs_lt Hop Hiq Hto).
rewrite (rngl_squ_mul Hic (rngl_sin _)).
specialize (cos2_sin2_1 α1) as H1.
apply (rngl_add_move_l Hop) in H1.
rewrite H1; clear H1.
specialize (cos2_sin2_1 α2) as H1.
apply (rngl_add_move_l Hop) in H1.
rewrite H1; clear H1.
rewrite (rngl_mul_sub_distr_r Hop).
rewrite rngl_mul_1_l.
rewrite (rngl_squ_mul Hic).
apply (rngl_lt_add_lt_sub_l Hop Hor).
rewrite <- rngl_mul_add_distr_l.
rewrite (rngl_squ_sub Hop Hic).
rewrite rngl_squ_1.
rewrite rngl_mul_1_r.
rewrite rngl_add_assoc.
rewrite (rngl_add_sub_assoc Hop).
rewrite <- (rngl_add_sub_swap Hop 1)%L.
rewrite <- (rngl_add_sub_swap Hop).
rewrite (rngl_sub_add Hop).
rewrite (rngl_sub_mul_r_diag_l Hop).
rewrite rngl_mul_assoc.
rewrite (rngl_mul_comm Hic _ 2)%L.
rewrite <- rngl_squ_1 at 4.
rewrite (rngl_squ_sub_squ Hop).
rewrite rngl_mul_1_r, rngl_mul_1_l.
rewrite (rngl_add_sub Hos).
apply (rngl_mul_lt_mono_pos_r Hop Hiq Hto). {
  apply (rngl_lt_0_sub Hop Hor).
  apply rngl_le_neq.
  split; [ now apply rngl_cos_bound | ].
  intros H.
  apply eq_rngl_cos_1 in H.
  subst α2.
  now apply rngl_lt_irrefl in Hzs2.
}
apply (rngl_le_lt_trans Hor _ (2 * rngl_cos² α2))%L. {
  apply (rngl_mul_le_mono_pos_l Hop Hiq Hto); [ easy | ].
  apply (rngl_abs_le_squ_le Hop Hto).
  rewrite (rngl_abs_nonneg_eq Hop Hor); [ | easy ].
  rewrite (rngl_abs_nonneg_eq Hop Hor). 2: {
    now apply (rngl_le_trans Hor _ (rngl_cos α1)).
  }
  easy.
}
apply (rngl_le_lt_trans Hor _ (2 * rngl_cos α2))%L. {
  apply (rngl_mul_le_mono_nonneg_l Hop Hor); [ easy | ].
  rewrite <- (rngl_mul_1_l (rngl_cos α2)) at 2.
  progress unfold rngl_squ.
  apply (rngl_mul_le_mono_nonneg_r Hop Hor). {
    now apply (rngl_le_trans Hor _ (rngl_cos α1)).
  }
  now apply rngl_cos_bound.
}
rewrite rngl_mul_2_l.
apply (rngl_add_lt_mono_r Hos Hor).
apply rngl_le_neq.
split; [ now apply rngl_cos_bound | ].
intros H.
apply eq_rngl_cos_1 in H.
subst α2.
now apply rngl_lt_irrefl in Hzs2.
Qed.

Theorem rngl_cos_le_cos_sub :
  ∀ α1 α2,
  (0 ≤ rngl_sin α1)%L
  → (0 ≤ rngl_sin α2)%L
  → (rngl_cos α1 ≤ rngl_cos α2)%L
  → (rngl_cos α1 ≤ rngl_cos (α2 - α1))%L.
Proof.
destruct_ac.
intros * Hs1 Hs2 Hcc.
apply (rngl_lt_eq_cases Hor) in Hs2.
destruct Hs2 as [Hs2| Hs2]. {
  apply rngl_lt_le_incl.
  now apply rngl_cos_lt_cos_sub.
}
symmetry in Hs2.
apply eq_rngl_sin_0 in Hs2.
destruct Hs2; subst α2. {
  rewrite angle_sub_0_l; cbn.
  apply (rngl_le_refl Hor).
}
rewrite rngl_cos_sub_straight_l.
cbn in Hcc.
apply (rngl_nlt_ge_iff Hto).
intros Hcc1.
apply (rngl_nlt_ge Hor) in Hcc.
apply Hcc; clear Hcc.
apply rngl_le_neq.
split; [ apply rngl_cos_bound | ].
intros H; symmetry in H.
apply eq_rngl_cos_opp_1 in H; subst α1.
apply (rngl_nle_gt Hor) in Hcc1.
apply Hcc1; clear Hcc1; cbn.
rewrite (rngl_opp_involutive Hop).
apply (rngl_opp_1_le_1 Hop Hto).
Qed.

Theorem fold_rl_sqrt : rl_nth_root 2 = rl_sqrt.
Proof. easy. Qed.

Theorem rngl_1_add_cos_div_2_nonneg : ∀ α, (0 ≤ (1 + rngl_cos α) / 2)%L.
Proof.
destruct_ac.
destruct (Nat.eq_dec (rngl_characteristic T) 1) as [Hc1| Hc1]. {
  specialize (rngl_characteristic_1 Hos Hc1) as H1.
  intros.
  rewrite (H1 (_ / _))%L.
  apply (rngl_le_refl Hor).
}
intros.
apply (rngl_mul_le_mono_pos_r Hop Hiq Hto) with (c := 2%L). {
  apply (rngl_0_lt_2 Hos Hc1 Hto).
}
rewrite (rngl_mul_0_l Hos).
rewrite (rngl_div_mul Hiv). 2: {
  apply (rngl_2_neq_0 Hos Hc1 Hto).
}
apply (rngl_le_sub_le_add_l Hop Hor).
rewrite (rngl_sub_0_l Hop).
now apply rngl_cos_bound.
Qed.

Theorem rngl_1_sub_cos_div_2_nonneg : ∀ α, (0 ≤ (1 - rngl_cos α) / 2)%L.
Proof.
destruct_ac.
destruct (Nat.eq_dec (rngl_characteristic T) 1) as [Hc1| Hc1]. {
  specialize (rngl_characteristic_1 Hos Hc1) as H1.
  intros.
  rewrite (H1 (_ / _))%L.
  apply (rngl_le_refl Hor).
}
intros.
apply (rngl_mul_le_mono_pos_r Hop Hiq Hto) with (c := 2%L). {
  apply (rngl_0_lt_2 Hos Hc1 Hto).
}
rewrite (rngl_mul_0_l Hos).
rewrite (rngl_div_mul Hiv). 2: {
  apply (rngl_2_neq_0 Hos Hc1 Hto).
}
apply (rngl_le_0_sub Hop Hor).
now apply rngl_cos_bound.
Qed.

Theorem rngl_sin_add_nonneg :
  ∀ α1 α2,
  (0 ≤ rngl_sin α1)%L
  → (0 ≤ rngl_sin α2)%L
  → (0 ≤ rngl_cos α1)%L
  → (0 ≤ rngl_cos α2)%L
  → (0 ≤ rngl_sin (α1 + α2))%L.
Proof.
destruct_ac.
intros * Hzs1 Hzs2 Hcs1 Hcs2.
cbn.
apply (rngl_le_0_add Hos Hor).
now apply (rngl_mul_nonneg_nonneg Hos Hor).
now apply (rngl_mul_nonneg_nonneg Hos Hor).
Qed.

Theorem rngl_sin_sub_lt_sin_l :
  ∀ α1 α2,
  (0 ≤ rngl_sin α1)%L
  → (0 < rngl_sin α2)%L
  → (0 < rngl_cos α1)%L
  → (rngl_sin (α1 - α2) < rngl_sin α1)%L.
Proof.
destruct_ac.
intros * Hc1z Hzs2 Hzc1.
cbn.
rewrite (rngl_mul_opp_r Hop).
rewrite (rngl_add_opp_r Hop).
apply (rngl_lt_sub_lt_add_r Hop Hor).
eapply (rngl_le_lt_trans Hor _ (rngl_sin α1)). {
  apply (rngl_le_0_sub Hop Hor).
  rewrite (rngl_sub_mul_r_diag_l Hop).
  apply (rngl_mul_nonneg_nonneg Hos Hor); [ easy | ].
  apply (rngl_le_0_sub Hop Hor).
  apply rngl_cos_bound.
}
apply (rngl_lt_add_r Hos Hor).
now apply (rngl_mul_pos_pos Hop Hiq Hor).
Qed.

Theorem quadrant_1_sin_sub_nonneg_cos_le :
  ∀ α1 α2,
  (0 ≤ rngl_sin α1)%L
  → (0 ≤ rngl_sin α2)%L
  → (0 ≤ rngl_cos α2)%L
  → (0 ≤ rngl_sin (α1 - α2))%L
  → (rngl_cos α1 ≤ rngl_cos α2)%L.
Proof.
destruct_ac.
destruct (Nat.eq_dec (rngl_characteristic T) 1) as [Hc1| Hc1]. {
  specialize (rngl_characteristic_1 Hos Hc1) as H1.
  intros.
  do 2 rewrite (H1 (rngl_cos _)).
  apply (rngl_le_refl Hor).
}
intros * Hsz1 Hzs2 Hzc2 Hzs12.
destruct (rngl_eqb_dec (rngl_sin α2) 0) as [Hs2z| Hs2z]. {
  apply (rngl_eqb_eq Heo) in Hs2z.
  apply eq_rngl_sin_0 in Hs2z.
  destruct Hs2z; subst α2; [ apply rngl_cos_bound | ].
  exfalso.
  apply (rngl_nlt_ge Hor) in Hzc2.
  apply Hzc2; clear Hzc2; cbn.
  apply (rngl_opp_1_lt_0 Hop Hc1 Hto).
}
apply (rngl_eqb_neq Heo) in Hs2z.
cbn in Hzs12.
rewrite (rngl_mul_opp_r Hop) in Hzs12.
rewrite (rngl_add_opp_r Hop) in Hzs12.
apply -> (rngl_le_0_sub Hop Hor) in Hzs12.
apply (rngl_lt_eq_cases Hor) in Hzs2.
apply not_eq_sym in Hs2z.
destruct Hzs2 as [Hzs2| Hzs2]; [ | easy ].
clear Hs2z.
apply (rngl_mul_le_mono_pos_r Hop Hiq Hto _ _ (rngl_sin α2) Hzs2) in Hzs12.
rewrite <- rngl_mul_assoc in Hzs12.
rewrite fold_rngl_squ in Hzs12.
specialize (cos2_sin2_1 α2) as H1.
apply (rngl_add_move_l Hop) in H1.
rewrite H1 in Hzs12; clear H1.
rewrite (rngl_mul_sub_distr_l Hop) in Hzs12.
rewrite rngl_mul_1_r in Hzs12.
apply (rngl_le_sub_le_add_l Hop Hor) in Hzs12.
eapply (rngl_le_trans Hor); [ apply Hzs12 | ].
rewrite (rngl_mul_mul_swap Hic).
progress unfold rngl_squ.
rewrite rngl_mul_assoc.
rewrite <- rngl_mul_add_distr_r.
rewrite <- rngl_cos_sub.
rewrite <- rngl_mul_1_l.
apply (rngl_mul_le_mono_nonneg_r Hop Hor); [ easy | ].
apply rngl_cos_bound.
Qed.

Theorem rngl_acos_prop :
  ∀ x, (x² ≤? 1)%L = true → cos2_sin2_prop x √(1 - x²)%L.
Proof.
destruct_ac.
intros * Hx1.
apply rngl_leb_le in Hx1.
progress unfold cos2_sin2_prop.
apply (rngl_eqb_eq Heo).
rewrite rngl_squ_sqrt. 2: {
  apply (rngl_le_add_le_sub_r Hop Hor).
  now rewrite rngl_add_0_l.
}
rewrite rngl_add_comm.
apply (rngl_sub_add Hop).
Qed.

Definition rngl_acos (x : T) :=
  match (rngl_leb_dec x² 1)%L with
  | left Hx1 =>
      {| rngl_cos := x; rngl_sin := √(1 - x²)%L;
         rngl_cos2_sin2 := rngl_acos_prop x Hx1 |}
  | _ =>
      angle_zero
  end.

Definition rngl_asin x := (π/₂ - rngl_acos x)%A.

Arguments rngl_acos x%_L.
Arguments rngl_asin x%_L.

Theorem rngl_cos_acos :
  ∀ x, (-1 ≤ x ≤ 1)%L → rngl_cos (rngl_acos x) = x.
Proof.
destruct_ac.
intros * Hx1.
progress unfold rngl_acos.
destruct (rngl_leb_dec x² 1) as [| H]; [ easy | ].
apply rngl_leb_nle in H.
exfalso; apply H; clear H.
now apply (rngl_squ_le_1_iff Hop Hiq Hto).
Qed.

Theorem rngl_sin_asin : ∀ a, (-1 ≤ a ≤ 1)%L → rngl_sin (rngl_asin a) = a.
Proof.
intros * Ha.
progress unfold rngl_asin.
rewrite rngl_sin_sub_right_l.
now apply rngl_cos_acos.
Qed.

Theorem rngl_sin_acos :
  ∀ x, (-1 ≤ x ≤ 1)%L → rngl_sin (rngl_acos x) = √(1 - x²)%L.
Proof.
destruct_ac.
intros * Hx1.
progress unfold rngl_acos.
destruct (rngl_leb_dec x² 1) as [| H]; [ easy | ].
apply rngl_leb_nle in H.
exfalso; apply H; clear H.
now apply (rngl_squ_le_1_iff Hop Hiq Hto).
Qed.

Theorem rngl_cos_asin :
  ∀ a, (-1 ≤ a ≤ 1)%L → rngl_cos (rngl_asin a) = √(1 - a²).
Proof.
intros * Ha.
progress unfold rngl_asin.
rewrite rngl_cos_sub_right_l.
now apply rngl_sin_acos.
Qed.

End a.

Arguments rngl_acos {T ro rp rl ac} x%_L.
Arguments rngl_asin {T ro rp rl ac} x%_L.
