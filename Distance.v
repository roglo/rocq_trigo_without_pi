From Stdlib Require Import Utf8.

Require Import RingLike.Core.
Require Import RingLike.RealLike.

Require Import Angle.

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
specialize (rngl_int_dom_or_inv_1_or_pdiv_r Hon Hiq) as Hii.
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

End a.
