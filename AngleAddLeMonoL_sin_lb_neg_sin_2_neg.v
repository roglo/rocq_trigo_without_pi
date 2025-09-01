From Stdlib Require Import Utf8 Arith.

Require Import RingLike.Core.
Require Import Angle TrigoWithoutPiExt.
Require Import Angle_order.
Require Import AngleAddOverflowLe.
Require Import TacChangeAngle.
Require Export AngleAddLeMonoL_prop.

Section a.

Context {T : Type}.
Context {ro : ring_like_op T}.
Context {rp : ring_like_prop T}.
Context {ac : angle_ctx T}.

Theorem angle_add_le_mono_l_sin_lb_neg_sin_2_neg :
  ∀ θ1 θ2 θ3,
  (rngl_sin (θ1 + θ2) < 0)%L
  → (rngl_sin θ2 < 0)%L
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
  intros * Hzs12 Hzs2 Haov13 H23.
  progress unfold angle_leb.
  rewrite (H1 (rngl_sin (θ1 + θ2))).
  rewrite (rngl_leb_refl Hor).
  rewrite (H1 (rngl_sin (θ1 + θ3))).
  rewrite (rngl_leb_refl Hor).
  do 2 rewrite (H1 (rngl_cos _)).
  apply (rngl_leb_refl Hor).
}
intros * Hzs12 Hzs2 Haov13 H23.
progress unfold angle_leb in H23.
progress unfold angle_leb.
remember (0 ≤? rngl_sin θ3)%L as zs3 eqn:Hzs3.
remember (0 ≤? rngl_sin (θ1 + θ3))%L as zs13 eqn:Hzs13.
symmetry in Hzs3, Hzs13.
move H23 at bottom.
apply (rngl_leb_gt Hor) in Hzs12, Hzs2.
rewrite Hzs12.
rewrite Hzs2 in H23.
apply (rngl_leb_gt Hor) in Hzs12, Hzs2.
destruct zs3; [ easy | ].
apply (rngl_leb_gt Hor) in Hzs3.
apply rngl_leb_le in H23.
destruct zs13. {
  exfalso.
  apply rngl_leb_le in Hzs13.
  apply Bool.not_true_iff_false in Haov13.
  apply Haov13; clear Haov13.
  destruct (rngl_eq_dec Heo (rngl_sin θ1) (rngl_sin (- θ3))) as [Hs13| Hs13]. {
    apply (rngl_opp_lt_compat Hop Hor) in Hzs3.
    rewrite (rngl_opp_0 Hop) in Hzs3.
    rewrite rngl_sin_opp in Hs13.
    rewrite <- Hs13 in Hzs3.
    rewrite <- rngl_sin_opp in Hs13.
    clear θ2 Hzs2 Hzs12 H23.
    rename θ3 into θ2.
    rename Hzs3 into Hzs1.
    rename Hzs13 into Hzs12.
    rename Hs13 into Hs12.
    apply Bool.not_false_iff_true.
    intros Haov.
    apply rngl_sin_add_nonneg_angle_add_not_overflow_sin_nonneg in Haov;
        try easy. {
      cbn in Hs12.
      apply (rngl_add_move_0_r Hop) in Hs12.
      rewrite rngl_add_comm in Hs12.
      apply (rngl_add_move_0_r Hop) in Hs12.
      rewrite Hs12 in Haov.
      apply (rngl_opp_nonneg_nonpos Hop Hor) in Haov.
      now apply rngl_nlt_ge in Haov.
    }
    now apply (rngl_lt_le_incl Hor) in Hzs1.
  }
  (* perhaps a lemma; faut réfléchir *)
  clear - ac Hzs13 Hor θ2 H23 Hzs12 Hzs2 Heo Hop Hzs3 Hon Hs13 Hc1 Hii Hos.
  rewrite <- angle_add_overflow_equiv2.
  progress unfold angle_add_overflow2.
  progress unfold angle_ltb.
  generalize Hzs13; intros H.
  apply rngl_leb_le in H.
  rewrite H; clear H.
  destruct (rngl_lt_dec Hor (rngl_sin θ1) 0) as [Hs1z| Hzs1]. {
    apply rngl_nle_gt in Hs1z.
    apply rngl_leb_nle in Hs1z.
    now rewrite Hs1z.
  }
  apply (rngl_nlt_ge_iff Hor) in Hzs1.
  generalize Hzs1; intros H.
  apply rngl_leb_le in H.
  rewrite H; clear H.
  apply rngl_ltb_lt.
  destruct (rngl_lt_dec Hor 0 (rngl_cos θ2)) as [Hzc2| Hc2z]. {
    assert (Hzc3 : (0 < rngl_cos θ3)%L). {
      now apply (rngl_lt_le_trans Hor _ (rngl_cos θ2)).
    }
    change_angle_add_r θ2 angle_right.
    progress sin_cos_add_sub_right_hyp T Hzs2.
    progress sin_cos_add_sub_right_hyp T Hzs12.
    progress sin_cos_add_sub_right_hyp T H23.
    progress sin_cos_add_sub_right_hyp T Hzc2.
    cbn in Hs13.
    change_angle_add_r θ3 angle_right.
    progress sin_cos_add_sub_right_hyp T Hs13.
    progress sin_cos_add_sub_right_hyp T Hzs3.
    progress sin_cos_add_sub_right_hyp T H23.
    progress sin_cos_add_sub_right_hyp T Hzs13.
    progress sin_cos_add_sub_right_hyp T Hzc3.
    progress sin_cos_add_sub_right_goal T.
    destruct (rngl_le_dec Hor (rngl_cos θ1) 0) as [Hc1z| Hzc1]. {
      exfalso.
      apply (rngl_lt_le_incl Hor) in Hzs2, Hzc2.
      change_angle_sub_r θ1 angle_right.
      progress sin_cos_add_sub_right_hyp T Hzs12.
      progress sin_cos_add_sub_right_hyp T Hzs1.
      progress sin_cos_add_sub_right_hyp T Hzs13.
      progress sin_cos_add_sub_right_hyp T Hc1z.
      apply rngl_nle_gt in Hzs12.
      apply Hzs12; clear Hzs12.
      now apply rngl_sin_add_nonneg.
    } {
      apply (rngl_nle_gt_iff Hor) in Hzc1.
      change_angle_sub_l θ3 angle_right.
      progress sin_cos_add_sub_right_hyp T Hzs3.
      progress sin_cos_add_sub_right_hyp T Hzs13.
      progress sin_cos_add_sub_right_hyp T Hs13.
      progress sin_cos_add_sub_right_hyp T H23.
      progress sin_cos_add_sub_right_hyp T Hzc3.
      progress sin_cos_add_sub_right_goal T.
      destruct (rngl_eq_dec Heo (rngl_sin θ1) 0) as [Hs1z| Hs1z]. {
        apply (eq_rngl_sin_0) in Hs1z.
        destruct Hs1z; subst θ1. {
          rewrite angle_sub_0_l in Hzs13.
          cbn in Hzs13.
          apply (rngl_opp_nonneg_nonpos Hop Hor) in Hzs13.
          now apply rngl_nlt_ge in Hzs13.
        } {
          exfalso.
          apply rngl_nle_gt in Hzc1.
          apply Hzc1; clear Hzc1.
          apply (rngl_opp_1_le_0 Hon Hop Hor).
        }
      }
      rewrite rngl_cos_sub_comm.
      apply rngl_cos_lt_cos_sub; try easy.
      apply (rngl_lt_le_incl Hor).
      apply quadrant_1_sin_sub_pos_cos_lt; try easy. {
        apply not_eq_sym in Hs1z.
        now apply (rngl_le_neq Hor).
      } {
        now apply (rngl_lt_le_incl Hor) in Hzc3.
      } {
        apply (rngl_le_neq Hor).
        split; [ easy | ].
        intros H; symmetry in H.
        apply (eq_rngl_sin_0) in H.
        destruct H as [H| H]. {
          apply angle_sub_move_l in H.
          rewrite angle_sub_0_r in H.
          now subst θ3.
        }
        apply angle_sub_move_l in H.
        subst θ3.
        progress sin_cos_add_sub_straight_hyp T Hzs3.
        now apply rngl_nle_gt in Hzs3.
      }
    }
  }
  apply (rngl_nlt_ge_iff Hor) in Hc2z.
  change_angle_add_r θ2 angle_straight.
  progress sin_cos_add_sub_straight_hyp T Hzs2.
  progress sin_cos_add_sub_straight_hyp T Hzs12.
  progress sin_cos_add_sub_straight_hyp T H23.
  progress sin_cos_add_sub_straight_hyp T Hc2z.
  destruct (rngl_le_dec Hor 0 (rngl_cos θ3)) as [Hzc3| Hc3z]. 2: {
    apply (rngl_nle_gt_iff Hor) in Hc3z.
    cbn in Hs13.
    change_angle_add_r θ3 angle_straight.
    progress sin_cos_add_sub_straight_hyp T Hzs3.
    progress sin_cos_add_sub_straight_hyp T Hs13.
    progress sin_cos_add_sub_straight_hyp T H23.
    progress sin_cos_add_sub_straight_hyp T Hzs13.
    progress sin_cos_add_sub_straight_hyp T Hc3z.
    progress sin_cos_add_sub_straight_goal T.
    rewrite (rngl_add_opp_l Hop) in H23.
    apply -> (rngl_le_sub_0 Hop Hor) in H23.
    move Hzs2 after Hzs1; move Hzs3 after Hzs2.
    destruct (rngl_lt_dec Hor 0 (rngl_cos θ1)) as [Hzc1| Hc1z]. {
      exfalso.
      apply rngl_nlt_ge in Hzs13.
      apply Hzs13; clear Hzs13.
      apply (rngl_lt_le_incl Hor) in Hc3z.
      now apply (rngl_sin_add_pos_1).
    }
    apply (rngl_nlt_ge_iff Hor) in Hc1z.
    change_angle_sub_r θ1 angle_right.
    progress sin_cos_add_sub_right_hyp T Hs13.
    progress sin_cos_add_sub_right_hyp T Hzs12.
    progress sin_cos_add_sub_right_hyp T Hzs1.
    progress sin_cos_add_sub_right_hyp T Hzs13.
    progress sin_cos_add_sub_right_hyp T Hc1z.
    progress sin_cos_add_sub_right_goal T.
    move Hzs1 before Hc2z.
    rewrite <- (rngl_opp_add_distr Hop).
    apply (rngl_opp_neg_pos Hop Hor).
    rewrite rngl_add_comm.
    destruct (rngl_eq_dec Heo (rngl_sin θ1) 0) as [Hs1z| Hs1z]. {
      apply (eq_rngl_sin_0) in Hs1z.
      destruct Hs1z; subst θ1. {
        rewrite angle_add_0_l in Hzs13.
        now apply rngl_nlt_ge in Hzs13.
      }
      exfalso.
      apply rngl_nlt_ge in Hzs1.
      apply Hzs1; clear Hzs1.
      apply (rngl_opp_1_lt_0 Hon Hop Hiq Hor Hc1).
    }
    apply (rngl_lt_eq_cases Hor) in Hc1z.
    apply not_eq_sym in Hs1z.
    destruct Hc1z as [Hc1z| H]; [ | easy ].
    apply (rngl_add_nonneg_pos Hos Hor); [ | easy ].
    apply (rngl_lt_le_incl Hor) in Hc1z, Hzs3, Hc3z.
    now apply rngl_sin_add_nonneg.
  }
  clear θ2 Hzs2 Hzs12 H23 Hc2z.
  rename θ3 into θ2.
  rename Hzs3 into Hs2z.
  rename Hzs13 into Hzs12.
  rename Hs13 into Hs12.
  rename Hzc3 into Hzc2.
  cbn in Hs12.
  change_angle_add_r θ2 angle_right.
  progress sin_cos_add_sub_right_hyp T Hs2z.
  progress sin_cos_add_sub_right_hyp T Hs12.
  progress sin_cos_add_sub_right_hyp T Hzs12.
  progress sin_cos_add_sub_right_hyp T Hzc2.
  progress sin_cos_add_sub_right_goal T.
  destruct (rngl_lt_dec Hor (rngl_cos θ1) 0) as [Hc1z| Hzc1]. {
    change_angle_sub_r θ1 angle_right.
    progress sin_cos_add_sub_right_hyp T Hs12.
    progress sin_cos_add_sub_right_hyp T Hzs12.
    progress sin_cos_add_sub_right_hyp T Hzs1.
    progress sin_cos_add_sub_right_hyp T Hc1z.
    progress sin_cos_add_sub_right_goal T.
    cbn.
    rewrite (rngl_add_sub_assoc Hop).
    rewrite (rngl_add_sub_swap Hop).
    rewrite (rngl_sub_mul_r_diag_l Hon Hop).
    apply (rngl_lt_0_add Hos Hor). {
      apply (rngl_mul_pos_pos Hos Hor Hii); [ easy | ].
      apply (rngl_lt_0_sub Hop Hor).
      apply (rngl_le_neq Hor).
      split; [ apply rngl_sin_bound | ].
      intros H.
      apply (eq_rngl_sin_1) in H.
      subst θ2.
      now apply (rngl_lt_irrefl Hor) in Hs2z.
    }
    apply (rngl_lt_le_incl Hor) in Hs2z.
    now apply (rngl_mul_nonneg_nonneg Hon Hos Hiq Hor).
  }
  apply (rngl_nlt_ge_iff Hor) in Hzc1.
  change_angle_sub_l θ2 angle_right.
  progress sin_cos_add_sub_right_hyp T Hs2z.
  progress sin_cos_add_sub_right_hyp T Hs12.
  progress sin_cos_add_sub_right_hyp T Hzs12.
  progress sin_cos_add_sub_right_hyp T Hzc2.
  progress sin_cos_add_sub_right_goal T.
  destruct (rngl_lt_dec Hor (rngl_cos θ1) (rngl_cos θ2))
      as [Hc12| Hc12]. {
    rewrite rngl_cos_sub_comm.
    apply (rngl_lt_le_incl Hor) in Hc12.
    now apply rngl_cos_lt_cos_sub.
  } {
    apply (rngl_nlt_ge_iff Hor) in Hc12.
    exfalso.
    apply rngl_nlt_ge in Hzs12.
    apply Hzs12; clear Hzs12.
    rewrite rngl_sin_sub_anticomm.
    apply (rngl_lt_opp_l Hop Hor).
    rewrite rngl_add_0_r.
    apply (rngl_le_neq Hor).
    split. {
      apply rngl_sin_sub_nonneg; try easy.
      now apply (rngl_lt_le_incl Hor) in Hs2z.
    }
    intros H; symmetry in H.
    apply (eq_rngl_sin_0) in H.
    destruct H as [H| H]. {
      apply angle_sub_move_r in H.
      rewrite angle_add_0_l in H.
      now subst θ2.
    }
    apply angle_sub_move_r in H.
    subst θ2.
    rewrite rngl_sin_add_straight_l in Hs2z.
    apply (rngl_opp_pos_neg Hop Hor) in Hs2z.
    now apply rngl_nle_gt in Hs2z.
  }
}
apply rngl_leb_le.
apply (rngl_leb_gt Hor) in Hzs13.
assert (Haov12 : angle_add_overflow θ1 θ2 = false). {
  apply (angle_add_overflow_le _ θ3); [ | easy ].
  progress unfold angle_leb.
  apply (rngl_leb_gt Hor) in Hzs2, Hzs3.
  rewrite Hzs2, Hzs3.
  now apply rngl_leb_le.
}
change_angle_add_r θ2 angle_straight.
progress sin_cos_add_sub_straight_hyp T Hzs2.
progress sin_cos_add_sub_straight_hyp T H23.
progress sin_cos_add_sub_straight_hyp T Hzs12.
progress sin_cos_add_sub_straight_goal T.
change_angle_add_r θ3 angle_straight.
progress sin_cos_add_sub_straight_hyp T H23.
progress sin_cos_add_sub_straight_hyp T Hzs13.
progress sin_cos_add_sub_straight_hyp T Hzs3.
progress sin_cos_add_sub_straight_goal T.
rewrite (rngl_add_opp_l Hop) in H23.
apply -> (rngl_le_sub_0 Hop Hor) in H23.
apply angle_add_le_mono_l_lemma_3; try easy; cycle 1.
now apply (rngl_lt_le_incl Hor).
now apply (rngl_lt_le_incl Hor).
now apply (rngl_lt_le_incl Hor).
now apply (rngl_lt_le_incl Hor).
(**)
destruct (rngl_lt_dec Hor 0 (rngl_sin θ1)) as [Hzs1'| Hs1z']. {
  rewrite angle_add_overflow_comm.
  apply (rngl_lt_le_incl Hor) in Hzs3, Hzs13.
  rewrite angle_add_comm in Hzs13.
  now apply rngl_sin_add_nonneg_angle_add_not_overflow.
}
apply (rngl_nlt_ge_iff Hor) in Hs1z'.
(**)
rewrite <- angle_add_overflow_equiv2 in Haov13.
progress unfold angle_add_overflow2 in Haov13.
progress unfold angle_ltb in Haov13.
rewrite <- angle_add_overflow_equiv2.
progress unfold angle_add_overflow2.
progress unfold angle_ltb.
progress sin_cos_add_sub_straight_hyp T Haov13.
generalize Hzs13; intros H.
apply (rngl_lt_le_incl Hor) in H.
apply rngl_leb_le in H.
rewrite H; clear H.
generalize Hzs13; intros H.
apply (rngl_opp_lt_compat Hop Hor) in H.
rewrite (rngl_opp_0 Hop) in H.
apply rngl_nle_gt in H.
apply rngl_leb_nle in H.
rewrite H in Haov13; clear H.
destruct (rngl_le_dec Hor 0 (rngl_sin θ1)) as [Hzs1| Hs1z]. {
  generalize Hzs1; intros H.
  apply rngl_leb_le in H.
  rewrite H in Haov13 |-*; clear H.
  clear Haov13.
  apply rngl_ltb_ge.
  apply (rngl_le_antisymm Hor) in Hzs1; [ | easy ].
  clear Hs1z'.
  apply eq_rngl_sin_0 in Hzs1.
  destruct Hzs1; subst θ1; [ apply rngl_cos_bound | ].
  rewrite rngl_sin_add_straight_l in Hzs12.
  apply (rngl_opp_pos_neg Hop Hor) in Hzs12.
  apply (rngl_lt_le_incl Hor) in Hzs12.
  now apply rngl_nlt_ge in Hzs12.
}
apply (rngl_nle_gt_iff Hor) in Hs1z.
exfalso.
generalize Hs1z; intros H.
apply rngl_nle_gt in H.
apply rngl_leb_nle in H.
rewrite H in Haov13; clear H.
apply (rngl_ltb_ge_iff Hor) in Haov13.
apply (rngl_le_opp_r Hop Hor) in Haov13.
move Hzs2 at bottom; move Hzs3 at bottom.
destruct (rngl_le_dec Hor 0 (rngl_cos θ1)) as [Hzs1| Hc1z]. {
  change_angle_add_r θ1 angle_right.
  progress sin_cos_add_sub_right_hyp T Hzs12.
  progress sin_cos_add_sub_right_hyp T Haov13.
  progress sin_cos_add_sub_right_hyp T Hs1z.
  progress sin_cos_add_sub_right_hyp T Hzs13.
  progress sin_cos_add_sub_right_hyp T Hzs1.
  move Hs1z at bottom.
  destruct (rngl_le_dec Hor 0 (rngl_cos θ3)) as [Hzc3| Hc3z]. {
    apply rngl_nlt_ge in Haov13.
    apply Haov13; clear Haov13.
    apply (rngl_add_nonneg_pos Hos Hor); [ easy | ].
    now apply (rngl_sin_add_pos_1).
  }
  apply (rngl_nle_gt_iff Hor) in Hc3z.
  change_angle_sub_r θ3 angle_right.
  progress sin_cos_add_sub_right_hyp T Hzs13.
  progress sin_cos_add_sub_right_hyp T H23.
  progress sin_cos_add_sub_right_hyp T Haov13.
  progress sin_cos_add_sub_right_hyp T Hzs3.
  progress sin_cos_add_sub_right_hyp T Hc3z.
  destruct (rngl_le_dec Hor 0 (rngl_cos θ2)) as [Hzc2| Hc2z]. {
    apply Bool.not_true_iff_false in Haov12.
    apply Haov12; clear Haov12.
    (* perhaps a lemma *)
    clear - ac Hop Hos Hzs12 Hs1z Hor Hzs1 Hzs2 Hzc2.
    rewrite <- angle_add_overflow_equiv2.
    progress unfold angle_add_overflow2.
    rewrite angle_add_sub_assoc.
    rewrite <- angle_add_sub_swap.
    progress unfold angle_ltb.
    rewrite rngl_sin_sub_straight_r.
    do 2 rewrite rngl_sin_sub_right_r.
    rewrite (rngl_opp_involutive Hop).
    generalize Hzs12; intros H.
    apply rngl_nle_gt in H.
    apply rngl_leb_nle in H.
    rewrite H; clear H.
    generalize Hs1z; intros H.
    apply (rngl_opp_lt_compat Hop Hor) in H.
    rewrite (rngl_opp_0 Hop) in H.
    apply rngl_nle_gt in H.
    apply rngl_leb_nle in H.
    rewrite H; clear H.
    rewrite rngl_cos_sub_straight_r.
    do 2 rewrite rngl_cos_sub_right_r.
    apply rngl_ltb_lt.
    apply (rngl_lt_opp_l Hop Hor).
    apply (rngl_lt_0_add Hos Hor); [ | easy ].
    now apply (rngl_sin_add_pos_1).
  }
  apply (rngl_nle_gt_iff Hor) in Hc2z.
  change_angle_sub_r θ2 angle_right.
  progress sin_cos_add_sub_right_hyp T Hzs12.
  progress sin_cos_add_sub_right_hyp T H23.
  progress sin_cos_add_sub_right_hyp T Hzs2.
  progress sin_cos_add_sub_right_hyp T Hc2z.
  apply Bool.not_true_iff_false in Haov12.
  apply Haov12; clear Haov12.
  rewrite angle_add_sub_swap.
  rewrite <- angle_sub_sub_distr.
  rewrite angle_straight_sub_right.
  (* perhaps a lemma *)
  rewrite <- angle_add_overflow_equiv2.
  progress unfold angle_add_overflow2.
  rewrite angle_add_sub_assoc.
  rewrite <- angle_add_sub_swap.
  rewrite <- angle_sub_add_distr.
  rewrite angle_right_add_right.
  progress unfold angle_ltb.
  rewrite rngl_sin_sub_straight_r.
  rewrite rngl_sin_sub_right_r.
  generalize Hzs12; intros H.
  apply (rngl_opp_lt_compat Hop Hor) in H.
  rewrite (rngl_opp_0 Hop) in H.
  apply rngl_nle_gt in H.
  apply rngl_leb_nle in H.
  rewrite H; clear H.
  generalize Hs1z; intros H.
  apply (rngl_opp_lt_compat Hop Hor) in H.
  rewrite (rngl_opp_0 Hop) in H.
  apply rngl_nle_gt in H.
  apply rngl_leb_nle in H.
  rewrite H; clear H.
  rewrite rngl_cos_sub_straight_r.
  rewrite rngl_cos_sub_right_r.
  apply rngl_ltb_lt.
  apply (rngl_lt_opp_l Hop Hor).
  cbn.
  rewrite <- (rngl_add_sub_swap Hop).
  rewrite <- (rngl_add_sub_assoc Hop).
  rewrite (rngl_sub_mul_r_diag_l Hon Hop).
  apply (rngl_lt_0_add Hos Hor). {
    now apply (rngl_mul_pos_pos Hos Hor Hii).
  }
  apply (rngl_mul_nonneg_nonneg Hon Hos Hiq Hor); [ easy | ].
  apply (rngl_le_0_sub Hop Hor).
  apply rngl_sin_bound.
}
apply (rngl_nle_gt_iff Hor) in Hc1z.
change_angle_add_r θ1 angle_straight.
progress sin_cos_add_sub_straight_hyp T Hzs12.
progress sin_cos_add_sub_straight_hyp T Haov13.
progress sin_cos_add_sub_straight_hyp T Hs1z.
progress sin_cos_add_sub_straight_hyp T Hzs13.
progress sin_cos_add_sub_straight_hyp T Hc1z.
move Hs1z at bottom.
destruct (rngl_le_dec Hor 0 (rngl_cos θ3)) as [Hzc3| Hc3z]. {
  exfalso.
  apply rngl_nle_gt in Hzs13.
  apply Hzs13; clear Hzs13.
  apply rngl_sin_add_nonneg; try easy.
  now apply (rngl_lt_le_incl Hor).
  now apply (rngl_lt_le_incl Hor).
  now apply (rngl_lt_le_incl Hor).
}
apply (rngl_nle_gt_iff Hor) in Hc3z.
change_angle_sub_r θ3 angle_right.
progress sin_cos_add_sub_right_hyp T Hzs13.
progress sin_cos_add_sub_right_hyp T H23.
progress sin_cos_add_sub_right_hyp T Haov13.
progress sin_cos_add_sub_right_hyp T Hzs3.
progress sin_cos_add_sub_right_hyp T Hc3z.
destruct (rngl_le_dec Hor 0 (rngl_cos θ2)) as [Hzc2| Hc2z]. {
  exfalso.
  apply rngl_nle_gt in Hzs12.
  apply Hzs12; clear Hzs12.
  apply rngl_sin_add_nonneg; try easy.
  now apply (rngl_lt_le_incl Hor).
  now apply (rngl_lt_le_incl Hor).
  now apply (rngl_lt_le_incl Hor).
}
apply (rngl_nle_gt_iff Hor) in Hc2z.
change_angle_sub_r θ2 angle_right.
progress sin_cos_add_sub_right_hyp T Hzs12.
progress sin_cos_add_sub_right_hyp T H23.
progress sin_cos_add_sub_right_hyp T Hzs2.
progress sin_cos_add_sub_right_hyp T Hc2z.
rewrite angle_add_sub_swap in Haov12.
rewrite <- angle_sub_sub_distr in Haov12.
rewrite angle_straight_sub_right in Haov12.
apply Bool.not_true_iff_false in Haov12.
apply Haov12; clear Haov12.
(* perhaps a lemma *)
rewrite <- angle_add_overflow_equiv2.
progress unfold angle_add_overflow2.
rewrite angle_add_sub_assoc.
rewrite <- angle_add_sub_swap.
rewrite angle_sub_sub_swap.
progress unfold angle_ltb.
do 2 rewrite rngl_sin_sub_straight_r.
rewrite rngl_sin_sub_right_r.
rewrite (rngl_opp_involutive Hop).
generalize Hzs12; intros H.
apply rngl_nle_gt in H.
apply rngl_leb_nle in H.
rewrite H; clear H.
generalize Hs1z; intros H.
apply (rngl_opp_lt_compat Hop Hor) in H.
rewrite (rngl_opp_0 Hop) in H.
apply rngl_nle_gt in H.
apply rngl_leb_nle in H.
rewrite H; clear H.
do 2 rewrite rngl_cos_sub_straight_r.
rewrite rngl_cos_sub_right_r.
apply rngl_ltb_lt.
apply -> (rngl_opp_lt_compat Hop Hor).
change_angle_sub_l θ2 angle_right.
progress sin_cos_add_sub_right_hyp T Hzs12.
progress sin_cos_add_sub_right_hyp T H23.
progress sin_cos_add_sub_right_hyp T Hzs2.
progress sin_cos_add_sub_right_hyp T Hc2z.
progress sin_cos_add_sub_right_goal T.
rewrite rngl_cos_sub_comm.
apply rngl_cos_lt_cos_sub; try easy.
now apply (rngl_lt_le_incl Hor).
apply (rngl_lt_le_incl Hor).
apply quadrant_1_sin_sub_pos_cos_lt; try easy.
now apply (rngl_lt_le_incl Hor).
now apply (rngl_lt_le_incl Hor).
now apply (rngl_lt_le_incl Hor).
Qed.

End a.
