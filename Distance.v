From Stdlib Require Import Utf8 Arith.

Require Import RingLike.Core.
Require Import RingLike.Real_Like.

Require Import Angle AngleDef.

Section a.

Context {T : Type}.
Context {ro : ring_like_op T}.
Context {rp : ring_like_prop T}.
Context {rl : real_like_prop T}.
Context {ac : angle_ctx T}.

(* euclidean distance *)

Definition angle_eucl_dist θ1 θ2 :=
  rl_modl (rngl_cos θ2 - rngl_cos θ1) (rngl_sin θ2 - rngl_sin θ1).

Theorem angle_eucl_dist_is_sqrt :
  ∀ θ1 θ2, angle_eucl_dist θ1 θ2 = √(2 * (1 - rngl_cos (θ2 - θ1)))%L.
Proof.
destruct_ac.
intros.
progress unfold angle_eucl_dist.
progress unfold rl_modl.
f_equal.
do 2 rewrite (rngl_squ_sub Hop Hic Hon).
rewrite (rngl_add_add_swap).
rewrite <- (rngl_add_sub_swap Hop).
rewrite rngl_add_assoc.
rewrite (rngl_add_sub_assoc Hop).
rewrite cos2_sin2_1.
rewrite rngl_add_comm.
rewrite (rngl_add_sub_assoc Hop).
rewrite rngl_add_assoc.
rewrite <- rngl_add_add_swap.
rewrite cos2_sin2_1.
rewrite (rngl_add_sub_assoc Hop).
rewrite (rngl_sub_sub_swap Hop).
rewrite <- (rngl_sub_add_distr Hos).
do 2 rewrite <- rngl_mul_assoc.
rewrite <- rngl_mul_add_distr_l.
rewrite (rngl_sub_mul_r_diag_l Hon Hop).
rewrite <- rngl_cos_sub.
easy.
Qed.

Theorem angle_eucl_dist_symmetry :
  ∀ θ1 θ2, angle_eucl_dist θ1 θ2 = angle_eucl_dist θ2 θ1.
Proof.
destruct_ac.
intros.
progress unfold angle_eucl_dist.
progress unfold rl_modl.
f_equal; rewrite (rngl_squ_sub_comm Hop).
f_equal; rewrite (rngl_squ_sub_comm Hop).
easy.
Qed.

Theorem angle_eucl_dist_separation :
  ∀ θ1 θ2, angle_eucl_dist θ1 θ2 = 0%L ↔ θ1 = θ2.
Proof.
destruct_ac.
specialize (rngl_has_inv_and_1_has_inv_and_1_or_pdiv Hon Hiv) as Hi1.
specialize (rngl_int_dom_or_inv_1_quo_and_eq_dec Hi1 Hed) as Hid.
intros *.
progress unfold angle_eucl_dist.
progress unfold rl_modl.
split; intros H12. 2: {
  subst θ2.
  do 2 rewrite (rngl_sub_diag Hos).
  rewrite (rngl_squ_0 Hos).
  rewrite rngl_add_0_r.
  apply (rl_sqrt_0 Hon Hop Hor Hii).
}
apply eq_angle_eq.
apply (eq_rl_sqrt_0 Hon Hos) in H12. 2: {
  apply (rngl_add_squ_nonneg Hon Hos Hiq Hor).
}
apply (rngl_eq_add_0 Hos Hor) in H12; cycle 1. {
  apply (rngl_squ_nonneg Hon Hos Hiq Hor).
} {
  apply (rngl_squ_nonneg Hon Hos Hiq Hor).
}
destruct H12 as (Hc, Hs).
apply (eq_rngl_squ_0 Hos) in Hc, Hs; cycle 1. {
  rewrite Bool.orb_true_iff; right.
  rewrite Hi1; cbn.
  apply (rngl_has_eq_dec_or_is_ordered_r Hor).
} {
  rewrite Bool.orb_true_iff; right.
  rewrite Hi1; cbn.
  apply (rngl_has_eq_dec_or_is_ordered_r Hor).
}
apply -> (rngl_sub_move_0_r Hop) in Hc.
apply -> (rngl_sub_move_0_r Hop) in Hs.
now rewrite Hc, Hs.
Qed.

Theorem angle_eucl_dist_triangular :
  ∀ θ1 θ2 θ3,
  (angle_eucl_dist θ1 θ3 ≤ angle_eucl_dist θ1 θ2 + angle_eucl_dist θ2 θ3)%L.
Proof.
intros *.
destruct_ac.
destruct θ1 as (c1, s1, Hcs1).
destruct θ2 as (c2, s2, Hcs2).
destruct θ3 as (c3, s3, Hcs3).
progress unfold angle_eucl_dist.
cbn.
apply (euclidean_distance_triangular Hic Hon Hop Hiv Hor).
Qed.

Theorem angle_eucl_dist_is_dist : is_dist angle_eucl_dist.
Proof.
intros.
split. {
  apply angle_eucl_dist_symmetry.
} {
  apply angle_eucl_dist_separation.
} {
  apply angle_eucl_dist_triangular.
}
Qed.

(* taxicab distance *)

Definition angle_taxi_dist θ1 θ2 :=
  (rngl_abs (rngl_cos θ2 - rngl_cos θ1) +
   rngl_abs (rngl_sin θ2 - rngl_sin θ1))%L.

Theorem angle_taxi_dist_symmetry :
  ∀ θ1 θ2, angle_taxi_dist θ1 θ2 = angle_taxi_dist θ2 θ1.
Proof.
destruct_ac; intros.
progress unfold angle_taxi_dist.
rewrite (rngl_abs_sub_comm Hop Hor).
f_equal.
apply (rngl_abs_sub_comm Hop Hor).
Qed.

Theorem angle_taxi_dist_separation :
  ∀ θ1 θ2, angle_taxi_dist θ1 θ2 = 0%L ↔ θ1 = θ2.
Proof.
destruct_ac; intros.
progress unfold angle_taxi_dist.
split; intros H12. {
  apply (rngl_eq_add_0 Hos Hor) in H12; cycle 1.
  apply (rngl_abs_nonneg Hop Hor).
  apply (rngl_abs_nonneg Hop Hor).
  destruct H12 as (Hcc, Hss).
  apply (eq_rngl_abs_0 Hop) in Hcc, Hss.
  apply -> (rngl_sub_move_0_r Hop) in Hcc.
  apply -> (rngl_sub_move_0_r Hop) in Hss.
  apply eq_angle_eq.
  now rewrite Hcc, Hss.
} {
  subst θ2.
  do 2 rewrite (rngl_sub_diag Hos).
  rewrite (rngl_abs_0 Hop).
  apply rngl_add_0_l.
}
Qed.

Theorem angle_taxi_dist_triangular :
  ∀ θ1 θ2 θ3,
  (angle_taxi_dist θ1 θ3 ≤ angle_taxi_dist θ1 θ2 + angle_taxi_dist θ2 θ3)%L.
Proof.
destruct_ac; intros.
destruct θ1 as (c1, s1, Hcs1).
destruct θ2 as (c2, s2, Hcs2).
destruct θ3 as (c3, s3, Hcs3).
progress unfold angle_taxi_dist.
cbn.
specialize (rngl_abs_triangle Hop Hor) as H1.
Search (rngl_abs _ - rngl_abs _)%L.
rewrite rngl_add_assoc.
rewrite (rngl_add_add_swap (rngl_abs (c2 - c1))).
rewrite <- rngl_add_assoc.
apply (rngl_add_le_mono Hos Hor). {
  eapply (rngl_le_trans Hor); [ | apply H1 ].
  rewrite rngl_add_comm.
  rewrite (rngl_add_sub_assoc Hop).
  rewrite (rngl_sub_add Hop).
  apply (rngl_le_refl Hor).
} {
  eapply (rngl_le_trans Hor); [ | apply H1 ].
  rewrite rngl_add_comm.
  rewrite (rngl_add_sub_assoc Hop).
  rewrite (rngl_sub_add Hop).
  apply (rngl_le_refl Hor).
}
Qed.

Theorem angle_taxi_dist_is_dist : is_dist angle_taxi_dist.
Proof.
split. {
  apply angle_taxi_dist_symmetry.
} {
  apply angle_taxi_dist_separation.
} {
  apply angle_taxi_dist_triangular.
}
Qed.

(* *)

Definition angle_eucl_distance :=
  {| d_dist := angle_eucl_dist; d_prop := angle_eucl_dist_is_dist |}.

Definition angle_taxi_distance :=
  {| d_dist := angle_taxi_dist; d_prop := angle_taxi_dist_is_dist |}.

Definition angle_lim := is_limit_when_seq_tends_to_inf angle_eucl_dist.

Theorem angle_eucl_dist_opp_opp :
  ∀ θ1 θ2, angle_eucl_dist (- θ1) (- θ2) = angle_eucl_dist θ1 θ2.
Proof.
destruct_ac.
intros.
progress unfold angle_eucl_dist.
progress unfold rl_modl.
cbn.
f_equal.
f_equal.
rewrite (rngl_sub_opp_r Hop).
rewrite rngl_add_comm.
rewrite (rngl_add_opp_r Hop).
rewrite <- (rngl_opp_sub_distr Hop).
apply (rngl_squ_opp Hop).
Qed.

Theorem angle_eucl_dist_sub_l_diag :
  ∀ θ Δθ, angle_eucl_dist (θ - Δθ) θ = angle_eucl_dist Δθ 0.
Proof.
destruct_ac.
intros.
progress unfold angle_eucl_dist.
progress unfold rl_modl.
remember (θ - Δθ)%A as x; cbn; subst x.
do 4 rewrite (rngl_squ_sub Hop Hic Hon).
rewrite (rngl_squ_1 Hon).
rewrite (rngl_mul_1_r Hon).
rewrite (rngl_squ_0 Hos).
rewrite (rngl_mul_0_r Hos).
rewrite (rngl_mul_0_l Hos).
rewrite (rngl_sub_diag Hos).
rewrite rngl_add_0_l.
rewrite rngl_add_assoc.
rewrite (rngl_add_sub_assoc Hop).
rewrite rngl_add_add_swap.
rewrite <- (rngl_add_sub_swap Hop (rngl_cos² θ)).
rewrite cos2_sin2_1.
rewrite <- (rngl_add_sub_swap Hop).
rewrite <- rngl_add_assoc.
rewrite cos2_sin2_1.
rewrite <- (rngl_add_sub_swap Hop 1)%L.
do 2 rewrite <- rngl_mul_assoc.
rewrite (rngl_sub_mul_r_diag_l Hon Hop).
rewrite <- (rngl_mul_sub_distr_l Hop).
rewrite <- (rngl_sub_add_distr Hos).
remember (θ - Δθ)%A as x.
replace (_ * _ + _ * _)%L with (rngl_cos (θ - x))%A. 2: {
  cbn.
  rewrite (rngl_mul_opp_r Hop).
  now rewrite rngl_sub_opp_r.
}
subst x.
rewrite angle_sub_sub_distr.
rewrite angle_sub_diag.
rewrite angle_add_0_l.
rewrite <- rngl_add_assoc.
rewrite cos2_sin2_1.
rewrite <- (rngl_add_sub_swap Hop).
now rewrite (rngl_sub_mul_r_diag_l Hon Hop).
Qed.

Theorem angle_eucl_dist_move_0_l :
  ∀ θ1 θ2, angle_eucl_dist θ1 θ2 = angle_eucl_dist (θ2 - θ1) 0.
Proof.
destruct_ac.
intros.
replace θ1 with (θ2 - (θ2 - θ1))%A. 2: {
  rewrite angle_sub_sub_distr.
  rewrite angle_sub_diag.
  apply angle_add_0_l.
}
rewrite angle_eucl_dist_sub_l_diag.
rewrite angle_sub_sub_distr.
rewrite angle_sub_diag.
f_equal; symmetry.
apply angle_add_0_l.
Qed.

Theorem angle_eucl_dist_move_0_r :
  ∀ θ1 θ2, angle_eucl_dist θ1 θ2 = angle_eucl_dist (θ1 - θ2) 0.
Proof.
destruct_ac.
intros.
rewrite angle_eucl_dist_move_0_l.
rewrite <- angle_eucl_dist_opp_opp.
rewrite angle_opp_0.
f_equal.
apply angle_opp_sub_distr.
Qed.

Theorem angle_eucl_dist_0_r_cos_sin :
  ∀ θ, ((angle_eucl_dist θ 0)² = (1 - rngl_cos θ)² + rngl_sin² θ)%L.
Proof.
destruct_ac.
intros.
progress unfold angle_eucl_dist.
progress unfold rl_modl; cbn.
rewrite (rngl_sub_0_l Hop).
rewrite (rngl_squ_opp Hop).
apply (rngl_squ_sqrt Hon).
apply (rngl_le_0_add Hos Hor);
apply (rngl_squ_nonneg Hon Hos Hiq Hor).
Qed.

Theorem angle_eucl_dist_straight_r_cos_sin :
  ∀ θ,
  ((angle_eucl_dist θ π)² = (1 + rngl_cos θ)² + rngl_sin² θ)%L.
Proof.
destruct_ac.
intros.
progress unfold angle_eucl_dist.
progress unfold rl_modl; cbn.
rewrite (rngl_sub_0_l Hop).
rewrite (rngl_squ_opp Hop).
rewrite <- (rngl_opp_add_distr Hop).
rewrite (rngl_squ_opp Hop).
rewrite (rngl_add_comm 1).
apply (rngl_squ_sqrt Hon).
apply (rngl_le_0_add Hos Hor);
apply (rngl_squ_nonneg Hon Hos Hiq Hor).
Qed.

Theorem rngl_cos_angle_eucl_dist_0_r :
  ∀ θ, (rngl_cos θ = 1 - (angle_eucl_dist θ 0)² / 2)%L.
Proof.
destruct_ac.
specialize (rngl_has_inv_and_1_has_inv_and_1_or_pdiv Hon Hiv) as Hi1.
destruct (Nat.eq_dec (rngl_characteristic T) 1) as [Hc1| Hc1]. {
  specialize (rngl_characteristic_1 Hon Hos Hc1) as H1.
  intros.
  rewrite H1; apply H1.
}
intros.
specialize (angle_eucl_dist_0_r_cos_sin θ) as H1.
rewrite (rngl_squ_sub Hop Hic Hon) in H1.
rewrite (rngl_squ_1 Hon) in H1.
rewrite (rngl_mul_1_r Hon) in H1.
rewrite <- rngl_add_assoc in H1.
rewrite cos2_sin2_1 in H1.
rewrite <- (rngl_add_sub_swap Hop) in H1.
rewrite (rngl_sub_mul_r_diag_l Hon Hop) in H1.
symmetry in H1.
apply (rngl_mul_move_l Hic Hi1) in H1. 2: {
  apply (rngl_2_neq_0 Hon Hos Hiq Hc1 Hor).
}
now apply (rngl_sub_move_l Hop) in H1.
Qed.

Theorem rngl_cos_angle_eucl_dist_straight_r :
  ∀ θ, (rngl_cos θ = (angle_eucl_dist θ π)² / 2 - 1)%L.
Proof.
destruct_ac.
specialize (rngl_has_inv_and_1_has_inv_and_1_or_pdiv Hon Hiv) as Hi1.
destruct (Nat.eq_dec (rngl_characteristic T) 1) as [Hc1| Hc1]. {
  specialize (rngl_characteristic_1 Hon Hos Hc1) as H1.
  intros.
  rewrite H1; apply H1.
}
intros.
specialize (angle_eucl_dist_straight_r_cos_sin θ) as H1.
rewrite (rngl_squ_add Hic Hon) in H1.
rewrite (rngl_squ_1 Hon) in H1.
rewrite (rngl_mul_1_r Hon) in H1.
rewrite <- rngl_add_assoc in H1.
rewrite cos2_sin2_1 in H1.
rewrite <- rngl_add_add_swap in H1.
rewrite (rngl_add_mul_r_diag_l Hon) in H1.
symmetry in H1.
apply (rngl_mul_move_l Hic Hi1) in H1. 2: {
  apply (rngl_2_neq_0 Hon Hos Hiq Hc1 Hor).
}
now apply (rngl_add_move_l Hop) in H1.
Qed.

Theorem angle_eucl_dist_diag : ∀ θ, angle_eucl_dist θ θ = 0%L.
Proof.
intros.
apply (dist_diag angle_eucl_dist_is_dist).
Qed.

Theorem angle_eucl_dist_nonneg : ∀ θ1 θ2, (0 ≤ angle_eucl_dist θ1 θ2)%L.
Proof.
destruct_ac.
intros.
apply (dist_nonneg Hon Hop Hiv Hor angle_eucl_dist_is_dist).
Qed.

Theorem angle_taxi_dist_nonneg : ∀ θ1 θ2, (0 ≤ angle_taxi_dist θ1 θ2)%L.
Proof.
destruct_ac.
intros.
apply (dist_nonneg Hon Hop Hiv Hor angle_taxi_dist_is_dist).
Qed.

Theorem angle_lim_const :
  ∀ θ1 θ2, angle_lim (λ _, θ1) θ2 → θ2 = θ1.
Proof.
destruct_ac.
destruct (Nat.eq_dec (rngl_characteristic T) 1) as [Hc1| Hc1]. {
  intros.
  specialize (rngl_characteristic_1_angle_0 Hc1) as H1.
  rewrite (H1 θ1); apply H1.
}
intros * H1.
progress unfold angle_lim in H1.
progress unfold is_limit_when_seq_tends_to_inf in H1.
apply angle_eucl_dist_separation.
rewrite angle_eucl_dist_symmetry.
specialize (angle_eucl_dist_nonneg θ1 θ2) as Hzx.
cbn in H1.
remember (angle_eucl_dist θ1 θ2) as x eqn:Hx.
clear θ1 θ2 Hx.
specialize (proj1 (rngl_lt_eq_cases Hor _ x) Hzx) as H3.
destruct H3 as [H3| H3]; [ | easy ].
clear Hzx; exfalso.
specialize (H1 (x / 2)%L).
assert (H : (0 < x / 2)%L). {
  apply (rngl_div_pos Hon Hop Hiv Hor); [ easy | ].
  apply (rngl_0_lt_2 Hon Hos Hiq Hc1 Hor).
}
specialize (H1 H); clear H.
destruct H1 as (N, HN).
specialize (HN N (Nat.le_refl _)).
apply rngl_nle_gt in HN.
apply HN; clear HN.
apply (rngl_le_div_l Hon Hop Hiv Hor).
apply (rngl_0_lt_2 Hon Hos Hiq Hc1 Hor).
rewrite (rngl_mul_2_r Hon).
apply (rngl_le_add_l Hos Hor).
now apply (rngl_lt_le_incl Hor).
Qed.

End a.
