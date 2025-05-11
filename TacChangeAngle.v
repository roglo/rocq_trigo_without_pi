(* Ltac tactics to change angles, typically to make them belonging to
   the first quadrant (sin > 0 and cos > 0) where reflexion is easier
   to do. *)

Require Import RingLike.Core.
Require Import Angle.

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
  set (Hon' := ac_on);
  set (Hop' := ac_op);
  repeat rewrite -> (angle_add_assoc _ _ angle_right) in H;
  repeat rewrite -> (angle_add_sub_assoc _ angle_right) in H;
  repeat rewrite -> (angle_add_sub_assoc _ _ angle_right) in H;
  repeat rewrite (angle_add_add_swap _ angle_right) in H;
  repeat rewrite (angle_add_sub_swap _ angle_right) in H;
  repeat rewrite <- (angle_add_sub_swap _ _ angle_right) in H;
  repeat rewrite <- (angle_sub_sub_distr angle_right) in H;
  repeat rewrite -> (angle_sub_sub_distr _ angle_right) in H;
  repeat rewrite <- (angle_sub_add_distr angle_right) in H;
  repeat rewrite -> (angle_sub_add_distr _ _ angle_right) in H;
  repeat rewrite -> (angle_add_comm (_ - angle_right))%A in H;
  repeat rewrite -> (angle_add_sub_assoc _ _ angle_right)%A in H;
  set (Hor' := ac_or);
  assert (Hos' : rngl_has_opp_or_subt T = true) by
    apply (rngl_has_opp_has_opp_or_subt Hop');
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
    (remember rngl_cos as c; apply -> (rngl_le_sub_0 Hop' Hor') in H;
     subst c);
  try
    (remember rngl_cos as c; apply -> (rngl_le_0_sub Hop' Hor') in H;
     subst c);
  try apply <- (rngl_opp_le_compat Hop' Hor') in H;
  try apply -> (rngl_opp_nonneg_nonpos Hop' Hor') in H;
  try apply -> (rngl_opp_nonpos_nonneg Hop' Hor') in H;
  try apply -> (rngl_opp_neg_pos Hop' Hor') in H;
  try apply -> (rngl_opp_pos_neg Hop' Hor') in H;
  try apply -> (rngl_le_opp_l Hop' Hor') in H;
  try apply -> (rngl_le_opp_r Hop' Hor') in H;
  try apply -> (rngl_lt_opp_l Hop' Hor') in H;
  repeat rewrite (rngl_opp_involutive Hop') in H;
  clear Hon' Hop' Hos' Hor'.

Ltac sin_cos_add_sub_straight_hyp T H :=
  set (Hon' := ac_on);
  set (Hop' := ac_op);
  repeat rewrite angle_add_sub_assoc in H;
  repeat rewrite <- (angle_sub_sub_distr angle_straight) in H;
  repeat rewrite -> (angle_sub_sub_distr _ angle_straight) in H;
  repeat rewrite -> (angle_sub_sub_distr _ _ angle_straight) in H;
  repeat rewrite -> (angle_add_add_swap _ angle_straight) in H;
  repeat rewrite <- (angle_add_sub_swap _ _ angle_straight) in H;
  repeat rewrite -> (angle_add_sub_swap _ angle_straight) in H;
  repeat rewrite -> (angle_sub_sub_swap _ angle_straight) in H;
  set (Hor' := ac_or);
  assert (Hos' : rngl_has_opp_or_subt T = true) by
    apply (rngl_has_opp_has_opp_or_subt Hop');
  repeat rewrite rngl_sin_add_straight_r in H;
  repeat rewrite rngl_cos_add_straight_r in H;
  repeat rewrite rngl_sin_sub_straight_r in H;
  repeat rewrite -> rngl_sin_sub_straight_l in H;
  repeat rewrite -> rngl_cos_sub_straight_l in H;
  repeat rewrite -> rngl_cos_sub_straight_r in H;
  repeat rewrite (rngl_add_opp_l Hop') in H;
  repeat rewrite <- (rngl_opp_add_distr Hop') in H;
  try apply -> (rngl_opp_nonpos_nonneg Hop' Hor') in H;
  try apply -> (rngl_opp_nonneg_nonpos Hop' Hor') in H;
  try apply -> (rngl_opp_neg_pos Hop' Hor') in H;
  try apply -> (rngl_opp_pos_neg Hop' Hor') in H;
  try apply -> (rngl_le_opp_r Hop' Hor') in H;
  try apply <- (rngl_opp_lt_compat Hop' Hor') in H;
  repeat rewrite (rngl_opp_involutive Hop') in H;
  try apply -> (rngl_lt_opp_l Hop' Hor') in H;
  try apply -> (rngl_opp_pos_neg Hop' Hor') in H;
  clear Hon' Hop' Hos' Hor'.

Ltac sin_cos_opp_hyp T H :=
  set (Hop' := ac_op);
  set (Hor' := ac_or);
  repeat rewrite -> rngl_sin_opp in H;
  repeat rewrite -> rngl_cos_opp in H;
  repeat rewrite -> angle_add_assoc in H;
  repeat rewrite -> angle_add_opp_r in H;
  repeat rewrite -> angle_add_opp_l in H;
  repeat rewrite -> angle_sub_opp_r in H;
  repeat rewrite <- angle_opp_add_distr in H;
  repeat rewrite -> rngl_sin_opp in H;
  repeat rewrite -> rngl_cos_opp in H;
  repeat rewrite (rngl_leb_0_opp Hop' Hor') in H;
  try apply -> (rngl_opp_neg_pos Hop' Hor') in H;
  clear Hop' Hor'.

Ltac sin_cos_add_sub_right_goal T :=
  set (Hon' := ac_on);
  set (Hop' := ac_op);
  repeat rewrite angle_add_assoc;
  repeat rewrite -> angle_add_sub_assoc;
  repeat rewrite (angle_add_add_swap _ angle_right);
  repeat rewrite (angle_add_sub_swap _ angle_right);
  repeat rewrite <- (angle_add_sub_swap _ _ angle_right);
  repeat rewrite <- (angle_sub_sub_distr angle_right);
  repeat rewrite -> angle_sub_add_distr;
  set (Hor' := ac_or);
  assert (Hos' : rngl_has_opp_or_subt T = true) by
    apply (rngl_has_opp_has_opp_or_subt Hop');
  repeat rewrite -> rngl_sin_sub_right_l;
  repeat rewrite -> rngl_cos_sub_right_l;
  repeat rewrite rngl_sin_add_right_r;
  repeat rewrite rngl_cos_add_right_r;
  repeat rewrite -> rngl_sin_sub_right_r;
  repeat rewrite rngl_cos_sub_right_r;
  repeat rewrite -> (rngl_add_opp_r Hop');
  repeat rewrite (rngl_opp_involutive Hop');
  try apply -> (rngl_opp_le_compat Hop' Hor');
  try apply <- (rngl_opp_nonpos_nonneg Hop' Hor');
  try apply <- (rngl_opp_nonneg_nonpos Hop' Hor');
  try apply <- (rngl_opp_neg_pos Hop' Hor');
  repeat rewrite -> (rngl_add_opp_r Hop');
  try apply <- (rngl_le_opp_l Hop' Hor');
  try apply <- (rngl_le_opp_r Hop' Hor');
  try apply <- (rngl_lt_opp_l Hop' Hor');
  try apply <- (rngl_lt_0_sub Hop' Hor');
  try (remember rngl_cos as c; apply <- (rngl_le_sub_0 Hop' Hor'); subst c);
  try (remember rngl_cos as c; apply <- (rngl_le_0_sub Hop' Hor'); subst c);
  clear Hon' Hop' Hor' Hos'.

Ltac sin_cos_add_sub_straight_goal T :=
  set (Hon' := ac_on);
  set (Hop' := ac_op);
  repeat rewrite -> angle_add_sub_assoc;
  repeat rewrite -> (angle_add_add_swap _ angle_straight);
  repeat rewrite <- (angle_add_sub_swap _ _ angle_straight);
  repeat rewrite -> (angle_add_sub_swap _ angle_straight);
  repeat rewrite -> (angle_sub_sub_swap _ angle_straight);
  repeat rewrite <- (angle_sub_sub_distr angle_straight);
  set (Hor' := ac_or);
  repeat rewrite -> rngl_sin_sub_straight_l;
  repeat rewrite -> rngl_cos_sub_straight_l;
  repeat rewrite rngl_sin_add_straight_r;
  repeat rewrite rngl_cos_add_straight_r;
  repeat rewrite rngl_sin_sub_straight_r;
  repeat rewrite rngl_cos_sub_straight_r;
  repeat rewrite (rngl_opp_involutive Hop');
  try apply <- (rngl_opp_nonpos_nonneg Hop' Hor');
  try apply <- (rngl_opp_nonneg_nonpos Hop' Hor');
  try apply <- (rngl_opp_neg_pos Hop' Hor');
  try apply <- (rngl_le_opp_l Hop' Hor');
  repeat rewrite -> (rngl_add_opp_r Hop');
  try apply <- (rngl_lt_opp_l Hop' Hor');
  try apply <- (rngl_le_opp_r Hop' Hor');
  try apply <- (rngl_lt_opp_r Hop' Hor');
  try apply <- (rngl_le_0_sub Hop' Hor');
  clear Hon' Hop' Hor'.

Ltac sin_cos_opp_goal T :=
  repeat rewrite angle_add_opp_l;
  repeat rewrite angle_add_opp_r;
  repeat rewrite angle_sub_opp_r.
