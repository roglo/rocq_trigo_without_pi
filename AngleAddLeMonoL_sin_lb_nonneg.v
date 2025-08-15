From Stdlib Require Import Utf8 Arith.

Require Import RingLike.Core.
Require Import Angle TrigoWithoutPiExt.
Require Import Angle_order.
Require Import AngleAddOverflowLe.
Require Import TacChangeAngle.
Require Import AngleAddLeMonoL_prop.

Section a.

Context {T : Type}.
Context {ro : ring_like_op T}.
Context {rp : ring_like_prop T}.
Context {ac : angle_ctx T}.

Theorem angle_add_le_mono_l_sin_lb_nonneg :
  ∀ θ1 θ2 θ3,
  (0 ≤ rngl_sin (θ1 + θ2))%L
  → angle_add_overflow θ1 θ3 = false
  → (θ2 ≤ θ3)%A
  → (θ1 + θ2 ≤ θ1 + θ3)%A.
Proof.
destruct_ac.
specialize (rngl_int_dom_or_inv_1_quo Hiv Hon) as Hii.
specialize (rngl_has_inv_and_1_has_inv_and_1_or_quot Hon Hiv) as Hi1.
specialize (rngl_int_dom_or_inv_1_quo_and_eq_dec Hi1 Hed) as Hid.
specialize (rngl_has_eq_dec_or_is_ordered_r Hor) as Heo.
destruct (Nat.eq_dec (rngl_characteristic T) 1) as [Hc1| Hc1]. {
  specialize (rngl_characteristic_1 Hon Hos Hc1) as H1.
  intros * Hzs12 Haov13 H23.
  progress unfold angle_leb.
  rewrite (H1 (rngl_sin (θ1 + θ2))).
  rewrite (rngl_leb_refl Hor).
  rewrite (H1 (rngl_sin (θ1 + θ3))).
  rewrite (rngl_leb_refl Hor).
  do 2 rewrite (H1 (rngl_cos _)).
  apply (rngl_leb_refl Hor).
}
intros * Hzs12 Haov13 H23.
progress unfold angle_leb in H23.
progress unfold angle_leb.
remember (0 ≤? rngl_sin θ2)%L as zs2 eqn:Hzs2.
remember (0 ≤? rngl_sin θ3)%L as zs3 eqn:Hzs3.
remember (0 ≤? rngl_sin (θ1 + θ3))%L as zs13 eqn:Hzs13.
symmetry in Hzs2, Hzs3, Hzs13.
move H23 at bottom.
apply rngl_leb_le in Hzs12.
rewrite Hzs12.
destruct zs13; [ | easy ].
apply rngl_leb_le in Hzs12, Hzs13.
apply rngl_leb_le.
destruct zs2. 2: {
  destruct zs3; [ easy | ].
  apply (rngl_leb_gt Hor) in Hzs2, Hzs3.
  apply rngl_leb_le in H23.
  assert (Haov12 : angle_add_overflow θ1 θ2 = false). {
    apply (angle_add_overflow_le _ θ3); [ | easy ].
    progress unfold angle_leb.
    apply (rngl_leb_gt Hor) in Hzs2, Hzs3.
    rewrite Hzs2, Hzs3.
    now apply rngl_leb_le.
  }
  destruct (rngl_lt_dec Hor (rngl_cos θ3) 0)%L as [Hc3z| Hzc3]. {
    exfalso.
    apply Bool.not_true_iff_false in Haov13.
    apply Haov13.
    now apply angle_add_le_mono_l_lemma_11.
  }
  apply (rngl_nlt_ge_iff Hor) in Hzc3.
  clear - ac Hor Hon Hop Hiv Hos Hzs13 Hzs12 Haov13 Haov12 H23 Hzc3 Hzs3 Hzs2.
  specialize (rngl_int_dom_or_inv_1_quo Hiv Hon) as Hii.
  generalize Hzs13; intros Hzs1.
  apply rngl_sin_add_nonneg_sin_nonneg in Hzs1; try easy.
  change_angle_add_r θ3 angle_right.
  progress sin_cos_add_sub_right_hyp T H23.
  progress sin_cos_add_sub_right_hyp T Hzc3.
  progress sin_cos_add_sub_right_hyp T Hzs3.
  progress sin_cos_add_sub_right_hyp T Hzs13.
  progress sin_cos_add_sub_right_goal T.
  destruct (rngl_le_dec Hor (rngl_cos θ2) 0)%L as [Hc2z| Hzc2]. {
    exfalso.
    change_angle_add_r θ2 angle_straight.
    progress sin_cos_add_sub_straight_hyp T H23.
    progress sin_cos_add_sub_straight_hyp T Hzs2.
    progress sin_cos_add_sub_straight_hyp T Hzs12.
    progress sin_cos_add_sub_straight_hyp T Hc2z.
    destruct (rngl_lt_dec Hor 0 (rngl_cos θ1))%L as [Hzc1| Hc1z]. {
      clear - ac θ1 θ2 θ3 Hzc1 Hzs2 Hc2z Hzc3 Hzs3 Hzs12 Hzs13 Hor.
      destruct (rngl_le_dec Hor 0 (rngl_sin θ1))%L as [Hzs1| Hs1z]. {
        apply rngl_nlt_ge in Hzs12.
        apply Hzs12; clear Hzs12.
        now apply rngl_sin_add_pos_1.
      }
      apply (rngl_nle_gt_iff Hor) in Hs1z.
      change_angle_add_r θ1 angle_right.
      progress sin_cos_add_sub_right_hyp T Hzc1.
      progress sin_cos_add_sub_right_hyp T Hs1z.
      progress sin_cos_add_sub_right_hyp T Hzs13.
      progress sin_cos_add_sub_right_hyp T Hzs12.
      apply rngl_nlt_ge in Hzs13.
      apply Hzs13; clear Hzs13.
      apply (rngl_lt_le_incl Hor) in Hs1z.
      now apply rngl_sin_add_pos_2.
    }
    apply (rngl_nlt_ge_iff Hor) in Hc1z.
    apply Bool.not_true_iff_false in Haov12.
    apply Haov12.
    clear - Hon Hos Hor Hop Hzs2 Hzs1 Hc1z Hzs12 Hc2z.
    destruct (Nat.eq_dec (rngl_characteristic T) 1) as [Hc1| Hc1]. {
      specialize (rngl_characteristic_1 Hon Hos Hc1) as H1.
      rewrite (H1 (rngl_sin _)) in Hzs2.
      now apply (rngl_lt_irrefl Hor) in Hzs2.
    }
    change_angle_sub_r θ1 angle_right.
    progress sin_cos_add_sub_right_hyp T Hzs1.
    progress sin_cos_add_sub_right_hyp T Hc1z.
    progress sin_cos_add_sub_right_hyp T Hzs12.
    rewrite <- angle_add_overflow_equiv2.
    progress unfold angle_add_overflow2.
    rewrite angle_add_sub_assoc.
    rewrite angle_add_add_swap.
    rewrite angle_add_sub_swap.
    rewrite <- angle_sub_sub_distr.
    rewrite angle_straight_sub_right.
    progress unfold angle_ltb.
    rewrite rngl_sin_sub_right_r.
    generalize Hzs12; intros H.
    apply (rngl_opp_le_compat Hop Hor) in H.
    rewrite (rngl_opp_0 Hop) in H.
    apply rngl_leb_le in H.
    rewrite H; clear H.
    rewrite rngl_sin_add_right_r.
    apply rngl_leb_le in Hzs1.
    rewrite Hzs1.
    apply rngl_leb_le in Hzs1.
    rewrite rngl_cos_sub_right_r.
    rewrite rngl_cos_add_right_r.
    apply rngl_ltb_lt.
    apply (rngl_lt_opp_l Hop Hor).
    apply (rngl_le_neq Hor).
    split. {
      cbn.
      rewrite rngl_add_assoc.
      rewrite (rngl_add_mul_r_diag_l Hon).
      apply (rngl_add_nonneg_nonneg Hor).
      apply (rngl_mul_nonneg_nonneg Hos Hor); [ easy | ].
      apply (rngl_le_opp_l Hop Hor).
      apply rngl_cos_bound.
      apply (rngl_mul_nonneg_nonneg Hos Hor); [ easy | ].
      now apply (rngl_lt_le_incl Hor).
    }
    intros H; symmetry in H.
    apply (rngl_add_move_0_r Hop) in H.
    generalize Hc1z; intros H1.
    rewrite H in H1.
    apply (rngl_opp_nonneg_nonpos Hop Hor) in H1.
    apply rngl_nlt_ge in H1.
    apply H1; clear H1.
    apply (rngl_le_neq Hor).
    split. {
      apply (rngl_lt_le_incl Hor) in Hzs2.
      now apply rngl_sin_add_nonneg.
    }
    intros H1; symmetry in H1.
    apply (eq_rngl_sin_0) in H1.
    destruct H1 as [H1| H1]. {
      apply angle_add_move_l in H1.
      rewrite angle_sub_0_l in H1.
      subst θ2.
      cbn in Hzs2.
      apply (rngl_opp_pos_neg Hop Hor) in Hzs2.
      now apply rngl_nlt_ge in Hzs2.
    }
    apply angle_add_move_l in H1.
    subst θ2.
    rewrite rngl_cos_sub_straight_l in Hc2z.
    apply (rngl_opp_nonneg_nonpos Hop Hor) in Hc2z.
    apply (rngl_le_antisymm Hor) in Hc2z; [ | easy ].
    symmetry in Hc2z.
    apply (eq_rngl_cos_0) in Hc2z.
    destruct Hc2z; subst θ1. {
      rewrite angle_straight_sub_right in H.
      rewrite angle_right_add_right in H.
      cbn in H.
      rewrite (rngl_opp_0 Hop) in H.
      now apply (rngl_1_eq_0_iff Hon Hos) in H.
    }
    apply rngl_nlt_ge in Hc1z.
    apply Hc1z; cbn.
    apply (rngl_opp_1_lt_0 Hon Hop Hor Hc1).
  }
  apply (rngl_nle_gt_iff Hor) in Hzc2.
  change_angle_add_r θ2 angle_right.
  progress sin_cos_add_sub_right_hyp T H23.
  progress sin_cos_add_sub_right_hyp T Hzs2.
  progress sin_cos_add_sub_right_hyp T Hzs12.
  progress sin_cos_add_sub_right_hyp T Hzc2.
  progress sin_cos_add_sub_right_goal T.
  destruct (rngl_le_dec Hor 0 (rngl_cos θ1)) as [Hzc1| Hc1z]. 2: {
    apply (rngl_nle_gt_iff Hor) in Hc1z.
    apply (rngl_nlt_ge_iff Hor).
    intros Hs123.
    rewrite <- angle_add_overflow_equiv2 in Haov12.
    progress unfold angle_add_overflow2 in Haov12.
    apply Bool.not_true_iff_false in Haov12.
    apply Haov12; clear Haov12.
    rewrite angle_add_sub_assoc.
    progress unfold angle_ltb.
    rewrite rngl_sin_sub_right_r.
    generalize Hzs12; intros H.
    apply (rngl_opp_le_compat Hop Hor) in H.
    rewrite (rngl_opp_0 Hop) in H.
    apply rngl_leb_le in H.
    rewrite H; clear H.
    apply rngl_leb_le in Hzs1.
    rewrite Hzs1.
    apply rngl_leb_le in Hzs1.
    apply rngl_ltb_lt.
    rewrite rngl_cos_sub_right_r.
    change_angle_sub_r θ1 angle_right.
    progress sin_cos_add_sub_right_hyp T Hzs1.
    progress sin_cos_add_sub_right_hyp T Hzs13.
    progress sin_cos_add_sub_right_hyp T Hzs12.
    progress sin_cos_add_sub_right_hyp T Hs123.
    progress sin_cos_add_sub_right_hyp T Hc1z.
    progress sin_cos_add_sub_right_goal T.
    cbn.
    rewrite (rngl_add_sub_assoc Hop).
    rewrite rngl_add_comm.
    rewrite <- (rngl_add_sub_assoc Hop).
    rewrite (rngl_sub_mul_r_diag_l Hon Hop).
    apply (rngl_add_nonneg_pos Hor).
    apply (rngl_mul_nonneg_nonneg Hos Hor); [ easy | ].
    now apply (rngl_lt_le_incl Hor).
    apply (rngl_mul_pos_pos Hos Hor Hii); [ easy | ].
    apply (rngl_lt_0_sub Hop Hor).
    apply (rngl_le_neq Hor).
    split; [ apply rngl_sin_bound | ].
    intros H.
    apply (eq_rngl_sin_1) in H.
    subst θ2.
    now apply (rngl_lt_irrefl Hor) in Hzs2.
  }
  apply (rngl_lt_le_incl Hor) in Hzs2.
  clear - ac Hor Hop Hzs1 Hzs3 Hzc3 Hzc1 Hzc2 Hzs2 Hzs13 Hzs12 Haov13 H23.
  apply rngl_cos_cos_sin_sin_neg_sin_le_cos_le_iff; try easy. {
    apply (rngl_lt_le_incl Hor) in Hzs3.
    now apply rngl_sin_add_nonneg.
  } {
    apply (rngl_lt_le_incl Hor) in Hzc2.
    now apply rngl_sin_add_nonneg.
  }
  apply angle_add_le_mono_l_lemma_3; try easy. {
    apply angle_add_overflow_le with (θ2 := (θ3 - angle_right)%A);
      try easy.
    progress unfold angle_leb.
    apply rngl_leb_le in Hzc3.
    rewrite Hzc3.
    apply rngl_leb_le in Hzc3.
    rewrite rngl_sin_sub_right_r.
    generalize Hzs3; intros H.
    apply (rngl_opp_lt_compat Hop Hor) in H.
    rewrite (rngl_opp_0 Hop) in H.
    apply rngl_nle_gt in H.
    apply rngl_leb_nle in H.
    now rewrite H.
  } {
    now apply (rngl_lt_le_incl Hor).
  } {
    apply (rngl_lt_le_incl Hor) in Hzc2.
    now apply rngl_sin_add_nonneg.
  } {
    apply (rngl_lt_le_incl Hor) in Hzs3.
    now apply rngl_sin_add_nonneg.
  }
  apply rngl_cos_cos_sin_sin_nonneg_sin_le_cos_le_iff; try easy.
  now apply (rngl_lt_le_incl Hor).
  now apply (rngl_lt_le_incl Hor).
}
apply rngl_leb_le in Hzs2.
destruct zs3. {
  apply rngl_leb_le in Hzs3, H23.
  now apply angle_add_le_mono_l_lemma_3.
}
clear H23.
apply (rngl_leb_gt Hor) in Hzs3.
destruct (rngl_lt_dec Hor (rngl_cos θ3) 0)%L as [Hc3z| Hzc3]. {
  exfalso.
  apply Bool.not_true_iff_false in Haov13.
  apply Haov13.
  now apply angle_add_le_mono_l_lemma_11.
}
apply (rngl_nlt_ge_iff Hor) in Hzc3.
generalize Hzs13; intros Hzs1.
apply rngl_sin_add_nonneg_sin_nonneg in Hzs1; [ | easy ].
change_angle_add_r θ3 angle_right.
progress sin_cos_add_sub_right_hyp T Hzs3.
progress sin_cos_add_sub_right_hyp T Hzc3.
progress sin_cos_add_sub_right_hyp T Hzs13.
progress sin_cos_add_sub_right_goal T.
destruct (rngl_le_dec Hor (rngl_cos θ2) 0)%L as [Hc2z| Hzc2]. 2: {
  apply (rngl_nle_gt_iff Hor) in Hzc2.
  move Hzc2 after Hzs3.
  apply (rngl_nlt_ge_iff Hor).
  intros H123.
  rewrite <- angle_add_overflow_equiv2 in Haov13.
  progress unfold angle_add_overflow2 in Haov13.
  apply Bool.not_true_iff_false in Haov13.
  apply Haov13; clear Haov13.
  rewrite angle_add_sub_assoc.
  progress unfold angle_ltb.
  rewrite rngl_sin_sub_right_r.
  generalize Hzs13; intros H.
  apply (rngl_opp_le_compat Hop Hor) in H.
  rewrite (rngl_opp_0 Hop) in H.
  apply rngl_leb_le in H.
  rewrite H; clear H.
  apply rngl_leb_le in Hzs1.
  rewrite Hzs1.
  apply rngl_leb_le in Hzs1.
  rewrite rngl_cos_sub_right_r.
  apply rngl_ltb_lt.
  change_angle_sub_l θ3 angle_right.
  progress sin_cos_add_sub_right_hyp T Hzs3.
  progress sin_cos_add_sub_right_hyp T Hzs13.
  progress sin_cos_add_sub_right_hyp T Hzc3.
  progress sin_cos_add_sub_right_hyp T H123.
  progress sin_cos_add_sub_right_goal T.
  rewrite rngl_cos_sub_comm in H123 |-*.
  destruct (rngl_le_dec Hor 0 (rngl_cos θ1))%L as [Hzc1| Hc1z]. {
    destruct (rngl_eq_dec Heo 0 (rngl_sin (θ1 - θ3)))
        as [Hzs1s3| Hs1s3z]. {
      symmetry in Hzs1s3.
      apply (eq_rngl_sin_0) in Hzs1s3.
      destruct Hzs1s3 as [H| H]. {
        apply -> (angle_sub_move_0_r) in H.
        subst θ3.
        rewrite angle_sub_diag in H123 |-*.
        cbn.
        apply (rngl_le_neq Hor).
        split; [ apply rngl_cos_bound | ].
        intros H.
        apply (eq_rngl_cos_1) in H.
        subst θ1.
        now apply (rngl_lt_irrefl Hor) in Hzs3.
      }
      apply angle_sub_move_l in H.
      subst θ3.
      rewrite rngl_sin_sub_straight_r in Hzs3.
      apply (rngl_opp_pos_neg Hop Hor) in Hzs3.
      now apply rngl_nle_gt in Hzs3.
    }
    apply not_eq_sym in Hs1s3z.
    apply rngl_cos_lt_cos_sub; try easy.
    apply rngl_cos_cos_sin_sin_nonneg_sin_le_cos_le_iff; try easy.
    now apply (rngl_lt_le_incl Hor).
    now apply rngl_sin_sub_nonneg_sin_le_sin.
  }
  apply (rngl_nle_gt_iff Hor) in Hc1z.
  change_angle_sub_r θ1 angle_right.
  progress sin_cos_add_sub_right_hyp T Hzs13.
  progress sin_cos_add_sub_right_hyp T Hzs12.
  progress sin_cos_add_sub_right_hyp T Hc1z.
  progress sin_cos_add_sub_right_hyp T H123.
  progress sin_cos_add_sub_right_hyp T Hzs1.
  progress sin_cos_add_sub_right_goal T.
  destruct (rngl_eq_dec Heo (rngl_cos θ3) 1) as [Hc31| Hc31]. {
    apply (eq_rngl_cos_1) in Hc31.
    subst θ3.
    now apply (rngl_lt_irrefl Hor) in Hzs3.
  }
  cbn.
  rewrite rngl_add_assoc.
  rewrite (rngl_mul_opp_r Hop).
  rewrite (rngl_add_opp_r Hop).
  rewrite (rngl_add_sub_swap Hop).
  rewrite (rngl_sub_mul_r_diag_r Hon Hop).
  apply (rngl_add_pos_nonneg Hor).
  apply (rngl_mul_pos_pos Hos Hor Hii); [ | easy ].
  apply (rngl_lt_0_sub Hop Hor).
  apply (rngl_le_neq Hor).
  split; [ | easy ].
  apply rngl_cos_bound.
  apply (rngl_mul_nonneg_nonneg Hos Hor); [ | easy ].
  now apply (rngl_lt_le_incl Hor).
}
change_angle_sub_r θ2 angle_right.
progress sin_cos_add_sub_right_hyp T Hzs2.
progress sin_cos_add_sub_right_hyp T Hc2z.
progress sin_cos_add_sub_right_hyp T Hzs12.
progress sin_cos_add_sub_right_goal T.
destruct (rngl_le_dec Hor 0 (rngl_cos θ1))%L as [Hzc1| Hc1z]. 2: {
  apply (rngl_nle_gt_iff Hor) in Hc1z.
  destruct (rngl_le_dec Hor (rngl_sin θ1) 0)%L as [Hs1z| Hs1z]. {
    apply (rngl_add_nonpos_nonpos Hor); cbn.
    apply (rngl_add_nonpos_nonpos Hor); cbn.
    apply (rngl_mul_nonpos_nonneg Hop Hor); [ easy | ].
    now apply (rngl_lt_le_incl Hor).
    apply (rngl_mul_nonpos_nonneg Hop Hor); [ | easy ].
    now apply (rngl_lt_le_incl Hor).
    apply (rngl_add_nonpos_nonpos Hor); cbn.
    now apply (rngl_mul_nonpos_nonneg Hop Hor).
    apply (rngl_mul_nonpos_nonneg Hop Hor); [ | easy ].
    now apply (rngl_lt_le_incl Hor).
  }
  exfalso.
  apply (rngl_nle_gt_iff Hor) in Hs1z.
  clear Hzs1.
  change_angle_sub_r θ1 angle_right.
  progress sin_cos_add_sub_right_hyp T Hs1z.
  progress sin_cos_add_sub_right_hyp T Hc1z.
  progress sin_cos_add_sub_right_hyp T Hzs13.
  progress sin_cos_add_sub_right_hyp T Hzs12.
  apply rngl_nlt_ge in Hzs12.
  apply Hzs12; clear Hzs12.
  apply (rngl_le_neq Hor).
  split. {
    apply (rngl_lt_le_incl Hor) in Hs1z, Hc1z.
    now apply rngl_sin_add_nonneg.
  }
  intros H; symmetry in H.
  apply (eq_rngl_sin_0) in H.
  destruct H as [H| H]. {
    apply angle_add_move_l in H.
    rewrite angle_sub_0_l in H.
    subst θ2.
    cbn in Hc2z.
    apply (rngl_opp_nonneg_nonpos Hop Hor) in Hc2z.
    now apply rngl_nlt_ge in Hc2z.
  }
  apply angle_add_move_l in H.
  subst θ2.
  rewrite rngl_cos_sub_straight_l in Hzs2.
  apply (rngl_opp_nonneg_nonpos Hop Hor) in Hzs2.
  now apply rngl_nlt_ge in Hzs2.
}
exfalso.
rename θ2 into θ.
rename θ3 into θ2.
rename θ into θ3.
rewrite <- angle_add_overflow_equiv2 in Haov13.
progress unfold angle_add_overflow2 in Haov13.
apply Bool.not_true_iff_false in Haov13.
apply Haov13; clear Haov13.
rewrite angle_add_sub_assoc.
progress unfold angle_ltb.
rewrite rngl_sin_sub_right_r.
generalize Hzs13; intros H.
apply (rngl_opp_le_compat Hop Hor) in H.
rewrite (rngl_opp_0 Hop) in H.
apply rngl_leb_le in H.
rewrite H; clear H.
apply rngl_leb_le in Hzs1.
rewrite Hzs1.
apply rngl_leb_le in Hzs1.
apply rngl_ltb_lt.
rewrite rngl_cos_sub_right_r.
change_angle_sub_l θ2 angle_right.
progress sin_cos_add_sub_right_hyp T Hzc3.
progress sin_cos_add_sub_right_hyp T Hzs13.
progress sin_cos_add_sub_right_hyp T Hzs3.
progress sin_cos_add_sub_right_goal T.
rewrite rngl_cos_sub_comm.
apply (rngl_le_neq Hor).
split. {
  rewrite rngl_cos_sub_comm.
  apply quadrant_1_sin_sub_nonneg_cos_le; try easy. {
    cbn.
    rewrite (rngl_mul_opp_r Hop).
    rewrite (rngl_sub_opp_r Hop).
    apply (rngl_add_nonneg_nonneg Hor).
    now apply (rngl_mul_nonneg_nonneg Hos Hor).
    apply (rngl_mul_nonneg_nonneg Hos Hor); [ easy | ].
    now apply (rngl_lt_le_incl Hor).
  } {
    rewrite angle_sub_sub_distr.
    rewrite angle_sub_diag.
    rewrite angle_add_0_l.
    now apply (rngl_lt_le_incl Hor).
  }
}
intros H.
apply rngl_cos_eq in H.
destruct H. {
  apply rngl_nlt_ge in Hzs13.
  apply Hzs13; clear Hzs13.
  rewrite rngl_sin_sub_anticomm.
  rewrite <- H.
  apply (rngl_opp_neg_pos Hop Hor).
  apply (rngl_le_neq Hor).
  split; [ easy | ].
  intros H1; symmetry in H1.
  apply (eq_rngl_sin_0) in H1.
  move H1 at top.
  destruct H1; subst θ1. {
    rewrite angle_sub_0_r in H.
    subst θ2.
    now apply (rngl_lt_irrefl Hor) in Hzs3.
  }
  apply angle_add_move_r in H.
  rewrite angle_straight_add_straight in H.
  subst θ2.
  now apply (rngl_lt_irrefl Hor) in Hzs3.
}
rewrite angle_opp_sub_distr in H.
apply angle_sub_move_l in H.
rewrite angle_sub_diag in H.
subst θ2.
now apply (rngl_lt_irrefl Hor) in Hzs3.
Qed.

End a.
