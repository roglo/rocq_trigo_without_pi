(* Ltac tactics to change angles, typically to make them belonging to
   the first quadrant (sin > 0 and cos > 0) where reflexion is easier
   to do. *)

Require Import RingLike.Core.
Require Import Angle AngleDef.

Ltac change_angle_add_r θ a :=
  remember (θ + a)%A as θ' eqn:Hθ';
  apply angle_sub_move_r in Hθ';
  subst θ; rename θ' into θ.

Ltac change_angle_sub_r θ a :=
  remember (θ - a)%A as θ' eqn:Hθ';
  apply angle_add_move_r in Hθ';
  subst θ; rename θ' into θ.

Ltac change_angle_sub_l θ a :=
  remember (a - θ)%A as θ' eqn:Hθ';
  apply angle_sub_move_l in Hθ';
  subst θ; rename θ' into θ.

Ltac change_angle_opp θ :=
  remember (- θ)%A as θ' eqn:Hθ';
  apply (f_equal angle_opp) in Hθ';
  rewrite angle_opp_involutive in Hθ';
  subst θ; rename θ' into θ.

Ltac sin_cos_add_sub_right_hyp T H :=
  set (Hop' := ac_op);
  repeat rewrite -> (angle_add_assoc _ _ π/₂) in H;
  repeat rewrite -> (angle_add_sub_assoc _ π/₂) in H;
  repeat rewrite -> (angle_add_sub_assoc _ _ π/₂) in H;
  repeat rewrite (angle_add_add_swap _ π/₂) in H;
  repeat rewrite (angle_add_sub_swap _ π/₂) in H;
  repeat rewrite <- (angle_add_sub_swap _ _ π/₂) in H;
  repeat rewrite <- (angle_sub_sub_distr π/₂) in H;
  repeat rewrite -> (angle_sub_sub_distr _ π/₂) in H;
  repeat rewrite <- (angle_sub_add_distr π/₂) in H;
  repeat rewrite -> (angle_sub_add_distr _ _ π/₂) in H;
  repeat rewrite -> (angle_add_comm (_ - π/₂))%A in H;
  repeat rewrite -> (angle_add_sub_assoc _ _ π/₂)%A in H;
  set (Hto' := ac_to);
  assert (Hos' : rngl_has_opp_or_psub T = true) by
    apply (rngl_has_opp_has_opp_or_psub Hop');
  repeat rewrite rngl_sin_add_right_r in H;
  repeat rewrite rngl_cos_add_right_r in H;
  repeat rewrite rngl_sin_sub_right_r in H;
  repeat rewrite -> rngl_cos_sub_right_r in H;
  repeat rewrite rngl_sin_add_right_l in H;
  repeat rewrite rngl_cos_add_right_l in H;
  repeat rewrite rngl_sin_sub_right_l in H;
  repeat rewrite rngl_cos_sub_right_l in H;
  repeat rewrite -> (rngl_add_opp_l Hop') in H;
  repeat rewrite -> (rngl_add_opp_r Hop') in H;
  try
    (remember rngl_cos as c; apply -> (rngl_le_sub_0 Hop' Hto') in H;
     subst c);
  try
    (remember rngl_cos as c; apply -> (rngl_le_0_sub Hop' Hto') in H;
     subst c);
  try apply <- (rngl_opp_le_compat Hop' Hto') in H;
  try apply -> (rngl_opp_nonneg_nonpos Hop' Hto') in H;
  try apply -> (rngl_opp_nonpos_nonneg Hop' Hto') in H;
  try apply -> (rngl_opp_neg_pos Hop' Hto') in H;
  try apply -> (rngl_opp_pos_neg Hop' Hto') in H;
  try apply -> (rngl_le_opp_l Hop' Hto') in H;
  try apply -> (rngl_le_opp_r Hop' Hto') in H;
  try apply -> (rngl_lt_opp_l Hop' Hto') in H;
  repeat rewrite (rngl_opp_involutive Hop') in H;
  clear Hop' Hos' Hto'.

Ltac sin_cos_add_sub_straight_hyp T H :=
  set (Hop' := ac_op);
  repeat rewrite angle_add_sub_assoc in H;
  repeat rewrite <- (angle_sub_sub_distr π) in H;
  repeat rewrite -> (angle_sub_sub_distr _ π) in H;
  repeat rewrite -> (angle_sub_sub_distr _ _ π) in H;
  repeat rewrite -> (angle_add_add_swap _ π) in H;
  repeat rewrite <- (angle_add_sub_swap _ _ π) in H;
  repeat rewrite -> (angle_add_sub_swap _ π) in H;
  repeat rewrite -> (angle_sub_sub_swap _ π) in H;
  set (Hto' := ac_to);
  assert (Hos' : rngl_has_opp_or_psub T = true) by
    apply (rngl_has_opp_has_opp_or_psub Hop');
  repeat rewrite rngl_sin_add_straight_r in H;
  repeat rewrite rngl_cos_add_straight_r in H;
  repeat rewrite rngl_sin_sub_straight_r in H;
  repeat rewrite -> rngl_sin_sub_straight_l in H;
  repeat rewrite -> rngl_cos_sub_straight_l in H;
  repeat rewrite -> rngl_cos_sub_straight_r in H;
  repeat rewrite (rngl_add_opp_l Hop') in H;
  repeat rewrite <- (rngl_opp_add_distr Hop') in H;
  try apply -> (rngl_opp_nonpos_nonneg Hop' Hto') in H;
  try apply -> (rngl_opp_nonneg_nonpos Hop' Hto') in H;
  try apply -> (rngl_opp_neg_pos Hop' Hto') in H;
  try apply -> (rngl_opp_pos_neg Hop' Hto') in H;
  try apply -> (rngl_le_opp_r Hop' Hto') in H;
  try apply <- (rngl_opp_lt_compat Hop' Hto') in H;
  repeat rewrite (rngl_opp_involutive Hop') in H;
  try apply -> (rngl_lt_opp_l Hop' Hto') in H;
  try apply -> (rngl_opp_pos_neg Hop' Hto') in H;
  clear Hop' Hos' Hto'.

Ltac sin_cos_opp_hyp T H :=
  set (Hop' := ac_op);
  set (Hto' := ac_to);
  repeat rewrite -> rngl_sin_opp in H;
  repeat rewrite -> rngl_cos_opp in H;
  repeat rewrite -> angle_add_assoc in H;
  repeat rewrite -> angle_add_opp_r in H;
  repeat rewrite -> angle_add_opp_l in H;
  repeat rewrite -> angle_sub_opp_r in H;
  repeat rewrite <- angle_opp_add_distr in H;
  repeat rewrite -> rngl_sin_opp in H;
  repeat rewrite -> rngl_cos_opp in H;
  repeat rewrite (rngl_leb_0_opp Hop' Hto') in H;
  try apply -> (rngl_opp_neg_pos Hop' Hto') in H;
  clear Hop' Hto'.

Ltac sin_cos_add_sub_right_goal T :=
  set (Hop' := ac_op);
  repeat rewrite angle_add_assoc;
  repeat rewrite -> angle_add_sub_assoc;
  repeat rewrite (angle_add_add_swap _ π/₂);
  repeat rewrite (angle_add_sub_swap _ π/₂);
  repeat rewrite <- (angle_add_sub_swap _ _ π/₂);
  repeat rewrite <- (angle_sub_sub_distr π/₂);
  repeat rewrite -> angle_sub_add_distr;
  set (Hto' := ac_to);
  assert (Hos' : rngl_has_opp_or_psub T = true) by
    apply (rngl_has_opp_has_opp_or_psub Hop');
  repeat rewrite -> rngl_sin_sub_right_l;
  repeat rewrite -> rngl_cos_sub_right_l;
  repeat rewrite rngl_sin_add_right_r;
  repeat rewrite rngl_cos_add_right_r;
  repeat rewrite -> rngl_sin_sub_right_r;
  repeat rewrite rngl_cos_sub_right_r;
  repeat rewrite -> (rngl_add_opp_r Hop');
  repeat rewrite (rngl_opp_involutive Hop');
  try apply -> (rngl_opp_le_compat Hop' Hto');
  try apply <- (rngl_opp_nonpos_nonneg Hop' Hto');
  try apply <- (rngl_opp_nonneg_nonpos Hop' Hto');
  try apply <- (rngl_opp_neg_pos Hop' Hto');
  repeat rewrite -> (rngl_add_opp_r Hop');
  try apply <- (rngl_le_opp_l Hop' Hto');
  try apply <- (rngl_le_opp_r Hop' Hto');
  try apply <- (rngl_lt_opp_l Hop' Hto');
  try apply <- (rngl_lt_0_sub Hop' Hto');
  try (remember rngl_cos as c; apply <- (rngl_le_sub_0 Hop' Hto'); subst c);
  try (remember rngl_cos as c; apply <- (rngl_le_0_sub Hop' Hto'); subst c);
  clear Hop' Hto' Hos'.

Ltac sin_cos_add_sub_straight_goal T :=
  set (Hop' := ac_op);
  repeat rewrite -> angle_add_sub_assoc;
  repeat rewrite -> (angle_add_add_swap _ π);
  repeat rewrite <- (angle_add_sub_swap _ _ π);
  repeat rewrite -> (angle_add_sub_swap _ π);
  repeat rewrite -> (angle_sub_sub_swap _ π);
  repeat rewrite <- (angle_sub_sub_distr π);
  set (Hto' := ac_to);
  repeat rewrite -> rngl_sin_sub_straight_l;
  repeat rewrite -> rngl_cos_sub_straight_l;
  repeat rewrite rngl_sin_add_straight_r;
  repeat rewrite rngl_cos_add_straight_r;
  repeat rewrite rngl_sin_sub_straight_r;
  repeat rewrite rngl_cos_sub_straight_r;
  repeat rewrite (rngl_opp_involutive Hop');
  try apply <- (rngl_opp_nonpos_nonneg Hop' Hto');
  try apply <- (rngl_opp_nonneg_nonpos Hop' Hto');
  try apply <- (rngl_opp_neg_pos Hop' Hto');
  try apply <- (rngl_le_opp_l Hop' Hto');
  repeat rewrite -> (rngl_add_opp_r Hop');
  try apply <- (rngl_lt_opp_l Hop' Hto');
  try apply <- (rngl_le_opp_r Hop' Hto');
  try apply <- (rngl_lt_opp_r Hop' Hto');
  try apply <- (rngl_le_0_sub Hop' Hto');
  clear Hop' Hto'.

Ltac sin_cos_opp_goal T :=
  repeat rewrite angle_add_opp_l;
  repeat rewrite angle_add_opp_r;
  repeat rewrite angle_sub_opp_r.
