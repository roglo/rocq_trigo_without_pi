From Stdlib Require Import Utf8 Arith.

Require Import RingLike.Core.
Require Import AngleDef Angle TrigoWithoutPiExt.
Require Import Angle_order.
Require Import AngleAddOverflowLe.
Require Import AngleAddOverflowEquiv.
Require Import TacChangeAngle.
Require Export AngleAddLeMonoL_prop.

Section a.

Context {T : Type}.
Context {ro : ring_like_op T}.
Context {rp : ring_like_prop T}.
Context {ac : angle_ctx T}.

Theorem rngl_cos_add_nonneg_cos_add_nonneg :
  ∀ θ1 θ2 θ3,
  (0 ≤ rngl_sin θ1)%L
  → (0 ≤ rngl_sin θ2)%L
  → (0 ≤ rngl_sin θ3)%L
  → (0 ≤ rngl_cos θ1)%L
  → (0 ≤ rngl_cos θ2)%L
  → (0 ≤ rngl_cos θ3)%L
  → (rngl_sin θ2 ≤ rngl_sin θ3)%L
  → (0 ≤ rngl_cos (θ1 + θ3))%L
  → (0 ≤ rngl_cos (θ1 + θ2))%L.
Proof.
destruct_ac.
intros * Hzs1 Hzs2 Hzs3 Hzc1 Hzc2 Hzc3 H23 Hzc13.
eapply (rngl_le_trans Hor); [ apply Hzc13 | cbn ].
apply (rngl_sub_le_compat Hop Hor). {
  apply (rngl_mul_le_mono_nonneg_l Hon Hop Hiq Hor); [ easy | ].
  generalize H23; intros H32.
  now apply rngl_cos_cos_sin_sin_nonneg_sin_le_cos_le_iff in H32.
}
now apply (rngl_mul_le_mono_nonneg_l Hon Hop Hiq Hor).
Qed.

Theorem angle_add_overflow_straight_straight :
  rngl_characteristic T ≠ 1 →
  angle_add_overflow angle_straight angle_straight = true.
Proof.
destruct_ac.
intros Hc1.
rewrite <- angle_add_overflow_equiv2.
progress unfold angle_add_overflow2.
rewrite angle_straight_add_straight.
progress unfold angle_ltb; cbn.
rewrite (rngl_leb_refl Hor).
apply rngl_ltb_lt.
apply (rngl_opp_1_lt_1 Hon Hop Hiq Hor Hc1).
Qed.

Theorem angle_add_le_mono_l_sin_lb_neg_sin_2_nonneg :
  ∀ θ1 θ2 θ3,
  (rngl_sin (θ1 + θ2) < 0)%L
  → (0 ≤ rngl_sin θ2)%L
  → angle_add_overflow θ1 θ3 = false
  → (θ2 ≤ θ3)%A
  → (θ1 + θ2 ≤ θ1 + θ3)%A.
Proof.
destruct_ac.
specialize (rngl_int_dom_or_inv_1_quo Hiv Hon) as Hii.
specialize (rngl_has_inv_and_1_has_inv_and_1_or_pdiv Hon Hiv) as Hi1.
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
apply (rngl_leb_gt Hor) in Hzs12.
rewrite Hzs12.
apply (rngl_leb_gt Hor) in Hzs12.
apply rngl_leb_le in Hzs2.
rewrite Hzs2 in H23.
apply rngl_leb_le in Hzs2.
destruct zs3. {
  apply rngl_leb_le in Hzs3, H23.
  destruct zs13. {
    exfalso.
    apply rngl_leb_le in Hzs13.
    apply rngl_nle_gt in Hzs12.
    apply Hzs12; clear Hzs12.
    apply (rngl_nlt_ge_iff Hor).
    intros Hzs12.
    generalize Hzs13; intros Hzs1.
    apply rngl_sin_add_nonneg_sin_nonneg in Hzs1; try easy.
    move Hzs1 after Hzs2.
    destruct (rngl_le_dec Hor 0 (rngl_cos θ2)) as [Hzc2| Hc2z]. 2: {
      apply (rngl_nle_gt_iff Hor) in Hc2z.
      change_angle_sub_r θ2 angle_right.
      progress sin_cos_add_sub_right_hyp T Hzs2.
      progress sin_cos_add_sub_right_hyp T H23.
      progress sin_cos_add_sub_right_hyp T Hc2z.
      progress sin_cos_add_sub_right_hyp T Hzs12.
      destruct (rngl_le_dec Hor 0 (rngl_cos θ3)) as [Hzc3| Hc3z]. {
        apply rngl_nlt_ge in H23.
        apply H23; clear H23.
        now apply (rngl_add_nonneg_pos Hos Hor).
      }
      apply (rngl_nle_gt_iff Hor) in Hc3z.
      change_angle_sub_r θ3 angle_right.
      progress sin_cos_add_sub_right_hyp T Hzs13.
      progress sin_cos_add_sub_right_hyp T H23.
      progress sin_cos_add_sub_right_hyp T Hzs3.
      progress sin_cos_add_sub_right_hyp T Hc3z.
      apply rngl_nle_gt in Hzs12.
      apply Hzs12; clear Hzs12.
      destruct (rngl_le_dec Hor 0 (rngl_cos θ1)) as [Hzc1| Hc1z]. {
        apply (rngl_lt_le_incl Hor) in Hc2z, Hc3z.
        now apply rngl_cos_add_nonneg_cos_add_nonneg with (θ3 := θ3).
      }
      exfalso.
      apply (rngl_nle_gt_iff Hor) in Hc1z.
      rewrite angle_add_comm in Hzs13.
      apply rngl_nle_gt in Hc1z.
      apply Hc1z; clear Hc1z.
      apply (rngl_lt_le_incl Hor).
      rewrite angle_add_overflow_comm in Haov13.
      clear - ac Hc1 Haov13 Hc3z Hzs1 Hzs3 Hzs13 Hor Hop Hiq Hon Hos.
      rename θ1 into θ2; rename θ3 into θ1.
      rename Hzs1 into Hzs2.
      rename Hzs13 into Hzs12.
      rename Hc3z into Hc1z.
      rename Haov13 into Haov12.
      (* a lemma, perhaps? *)
      apply (rngl_nle_gt_iff Hor).
      intros Hc2z.
      change_angle_sub_r θ2 angle_right.
      progress sin_cos_add_sub_right_hyp T Hzs2.
      progress sin_cos_add_sub_right_hyp T Hzs12.
      progress sin_cos_add_sub_right_hyp T Hc2z.
      apply rngl_nlt_ge in Hzs12.
      apply Hzs12; clear Hzs12.
      apply (rngl_le_neq Hor).
      split. {
        apply (rngl_lt_le_incl Hor) in Hc1z.
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
      apply (rngl_le_antisymm Hor) in Hzs2; [ | easy ].
      symmetry in Hzs2.
      apply (eq_rngl_cos_0) in Hzs2.
      destruct Hzs2; subst θ1. {
        rewrite <- angle_add_overflow_equiv2 in Haov12.
        progress unfold angle_add_overflow2 in Haov12.
        apply Bool.not_true_iff_false in Haov12.
        apply Haov12; clear Haov12.
        rewrite angle_right_add_right.
        rewrite angle_sub_add.
        rewrite angle_straight_add_straight.
        progress unfold angle_ltb; cbn.
        rewrite (rngl_leb_refl Hor).
        apply rngl_ltb_lt.
        apply (rngl_opp_1_lt_1 Hon Hop Hiq Hor Hc1).
      }
      rewrite angle_sub_opp_r in Hc2z.
      rewrite rngl_sin_add_right_r in Hc2z.
      apply rngl_nlt_ge in Hc2z.
      apply Hc2z; clear Hc2z; cbn.
      apply (rngl_opp_1_lt_0 Hon Hop Hiq Hor Hc1).
    }
    move Hzc2 after Hzs3.
    apply rngl_nle_gt in Hzs12.
    apply Hzs12; clear Hzs12.
    rename θ3 into θ.
    rename θ2 into θ3.
    rename θ into θ2.
    rename Hzs13 into Hzs12.
    rename Hzc2 into Hzc3.
    rename Hzs3 into H.
    rename Hzs2 into Hzs3.
    rename H into Hzs2.
    rename Haov13 into Haov12.
    apply (rngl_nlt_ge_iff Hor).
    intros Hzs13.
    destruct (rngl_le_dec Hor 0 (rngl_cos θ1)) as [Hzc1| Hc1z]. {
      apply rngl_nle_gt in Hzs13.
      apply Hzs13; clear Hzs13.
      now apply rngl_sin_add_nonneg.
    }
    apply (rngl_nle_gt_iff Hor) in Hc1z.
    change_angle_sub_r θ1 angle_right.
    progress sin_cos_add_sub_right_hyp T Hzs1.
    progress sin_cos_add_sub_right_hyp T Hc1z.
    progress sin_cos_add_sub_right_hyp T Hzs13.
    progress sin_cos_add_sub_right_hyp T Hzs12.
    destruct (rngl_le_dec Hor 0 (rngl_cos θ2)) as [Hzc2| Hc2z]. {
      apply (rngl_lt_le_incl Hor) in Hc1z.
      apply rngl_nle_gt in Hzs13.
      apply Hzs13; clear Hzs13.
      apply rngl_cos_add_nonneg_cos_add_nonneg with (θ3 := θ2); try easy.
      now apply rngl_cos_cos_sin_sin_nonneg_sin_le_cos_le_iff.
    }
    apply (rngl_nle_gt_iff Hor) in Hc2z.
    change_angle_sub_r θ2 angle_right.
    progress sin_cos_add_sub_right_hyp T Hzs2.
    progress sin_cos_add_sub_right_hyp T H23.
    progress sin_cos_add_sub_right_hyp T Hc2z.
    progress sin_cos_add_sub_right_hyp T Hzs12.
    destruct (rngl_lt_dec Hor 0 (rngl_cos θ1)) as [H| H]. {
      apply rngl_nlt_ge in Hzs12.
      apply Hzs12; clear Hzs12.
      apply (rngl_lt_le_incl Hor) in Hc1z.
      now apply rngl_sin_add_pos_1.
    }
    apply (rngl_nlt_ge_iff Hor) in H.
    apply (rngl_le_antisymm Hor) in H; [ | easy ].
    symmetry in H.
    apply (eq_rngl_cos_0) in H.
    destruct H; subst θ1. {
      rewrite rngl_sin_add_right_l in Hzs12.
      apply (rngl_le_antisymm Hor) in Hzs12; [ | easy ].
      symmetry in Hzs12.
      apply (eq_rngl_cos_0) in Hzs12.
      destruct Hzs12; subst θ2. {
        rewrite angle_right_add_right in Haov12.
        now rewrite angle_add_overflow_straight_straight in Haov12.
      }
      apply rngl_nle_gt in Hc2z.
      apply Hc2z; cbn.
      apply (rngl_opp_1_le_0 Hon Hop Hiq Hor).
    }
    apply rngl_nlt_ge in Hc1z.
    apply Hc1z.
    apply (rngl_opp_1_le_0 Hon Hop Hiq Hor).
  }
  apply (rngl_leb_gt Hor) in Hzs13.
  apply rngl_leb_le.
  destruct (rngl_lt_dec Hor 0 (rngl_cos θ3)) as [Hzc3| Hc3z]. {
    assert (Hzc2 : (0 < rngl_cos θ2)%L). {
      eapply (rngl_lt_le_trans Hor); [ apply Hzc3 | apply H23 ].
    }
    destruct (rngl_lt_dec Hor 0 (rngl_sin θ1)) as [Hzs1| Hs1z]. {
      destruct (rngl_le_dec Hor 0 (rngl_cos θ1)) as [Hzc1| Hc1z]. {
        exfalso.
        apply rngl_nle_gt in Hzs12.
        apply Hzs12; clear Hzs12.
        apply (rngl_lt_le_incl Hor) in Hzc2, Hzs1.
        now apply rngl_sin_add_nonneg.
      }
      apply (rngl_nle_gt_iff Hor) in Hc1z.
      change_angle_sub_l θ1 angle_straight.
      progress sin_cos_add_sub_straight_hyp T Hzs13.
      progress sin_cos_add_sub_straight_hyp T Hzs12.
      progress sin_cos_add_sub_straight_hyp T Hc1z.
      progress sin_cos_add_sub_straight_hyp T Hzs1.
      progress sin_cos_add_sub_straight_goal T.
      rewrite rngl_sin_sub_anticomm in Hzs13, Hzs12.
      apply (rngl_opp_neg_pos Hop Hor) in Hzs13, Hzs12.
      do 2 rewrite (rngl_cos_sub_comm θ1).
      destruct (rngl_eq_dec Heo (rngl_sin θ2) (rngl_sin θ3)) as
        [Hes23| Hes23]. {
        apply rngl_sin_eq in Hes23.
        destruct Hes23; subst θ2; [ apply (rngl_le_refl Hor) | ].
        rewrite rngl_cos_sub_straight_l in H23.
        rewrite <- angle_sub_add_distr in Hzs12 |-*.
        rewrite rngl_sin_sub_straight_l in Hzs12.
        rewrite rngl_cos_sub_straight_l in Hzc2 |-*.
        apply (rngl_opp_pos_neg Hop Hor) in Hzc2.
        apply (rngl_le_opp_r Hop Hor).
        cbn.
        rewrite (rngl_mul_opp_r Hop).
        rewrite (rngl_sub_opp_r Hop).
        rewrite (rngl_add_sub_assoc Hop).
        rewrite rngl_add_add_swap.
        rewrite (rngl_add_sub Hos).
        rewrite <- rngl_mul_add_distr_r.
        apply (rngl_mul_nonpos_nonneg Hon Hop Hiq Hor); [ | ].
        apply (rngl_lt_le_incl Hor) in Hzc2.
        now apply (rngl_add_nonpos_nonpos Hos Hor).
        now apply (rngl_lt_le_incl Hor).
      }
      apply (rngl_nlt_ge_iff Hor).
      intros H.
      apply (rngl_lt_le_incl Hor) in H.
      apply rngl_sin_sub_nonneg in H; try easy. {
        rewrite angle_sub_sub_distr in H.
        rewrite angle_sub_sub_swap in H.
        rewrite angle_sub_add in H.
        apply rngl_nlt_ge in H.
        apply H; clear H.
        cbn.
        rewrite rngl_add_comm.
        eapply (rngl_le_lt_trans Hor). {
          apply (rngl_add_le_mono_l Hos Hor).
          apply (rngl_mul_le_mono_nonneg_l Hon Hop Hiq Hor); [ easy | ].
          apply H23.
        }
        rewrite (rngl_mul_comm Hic).
        rewrite <- rngl_mul_add_distr_r.
        rewrite (rngl_add_opp_l Hop).
        rewrite (rngl_mul_comm Hic).
        apply (rngl_mul_pos_neg Hon Hop Hiq Hor); [ easy | ].
        apply (rngl_lt_sub_0 Hop Hor).
        apply (rngl_le_neq Hor).
        split; [ | easy ].
        apply rngl_cos_cos_sin_sin_nonneg_sin_le_cos_le_iff; try easy.
        now apply (rngl_lt_le_incl Hor).
        now apply (rngl_lt_le_incl Hor).
      }
      now apply (rngl_lt_le_incl Hor).
      now apply (rngl_lt_le_incl Hor).
    }
    apply (rngl_nlt_ge_iff Hor) in Hs1z.
    destruct (rngl_le_dec Hor (rngl_cos θ1) 0) as [Hzc1| Hc1z]. {
      cbn.
      apply (rngl_sub_le_compat Hop Hor).
      now apply (rngl_mul_le_mono_nonpos_l Hon Hop Hiq Hor).
      apply (rngl_mul_le_mono_nonpos_l Hon Hop Hiq Hor); [ easy | ].
      apply rngl_cos_cos_sin_sin_nonneg_sin_le_cos_le_iff; try easy.
      now apply (rngl_lt_le_incl Hor).
      now apply (rngl_lt_le_incl Hor).
    }
    apply (rngl_nle_gt_iff Hor) in Hc1z.
    change_angle_add_r θ1 angle_right.
    progress sin_cos_add_sub_right_hyp T Hzs13.
    progress sin_cos_add_sub_right_hyp T Hzs12.
    progress sin_cos_add_sub_right_hyp T Hc1z.
    progress sin_cos_add_sub_right_hyp T Hs1z.
    progress sin_cos_add_sub_right_goal T.
    assert (Hs12 : (0 ≤ rngl_sin (θ1 + θ2))%L). {
      apply (rngl_lt_le_incl Hor) in Hc1z, Hzc2.
      now apply rngl_sin_add_nonneg.
    }
    assert (Hs13 : (0 ≤ rngl_sin (θ1 + θ3))%L). {
      apply (rngl_lt_le_incl Hor) in Hc1z, Hzc3.
      now apply rngl_sin_add_nonneg.
    }
    apply rngl_cos_cos_sin_sin_nonneg_sin_le_cos_le_iff; try easy.
    now apply (rngl_lt_le_incl Hor).
    now apply (rngl_lt_le_incl Hor).
    apply angle_add_le_mono_l_lemma_3; try easy.
    clear - ac Hs13 Hzs3 Hc1z.
    rewrite angle_add_overflow_comm.
    rewrite angle_add_comm in Hs13.
    now apply rngl_sin_add_nonneg_angle_add_not_overflow.
  }
  apply (rngl_nlt_ge_iff Hor) in Hc3z.
  rename H23 into Hc32.
  rename Hzs13 into Hs13z.
  rename Hzs12 into Hs12z.
  change_angle_sub_r θ3 angle_right.
  progress sin_cos_add_sub_right_hyp T Hc32.
  progress sin_cos_add_sub_right_hyp T Hc3z.
  progress sin_cos_add_sub_right_hyp T Hzs3.
  progress sin_cos_add_sub_right_hyp T Hs13z.
  progress sin_cos_add_sub_right_goal T.
  destruct (rngl_le_dec Hor 0 (rngl_cos θ2)) as [Hzc2| Hc2z]. {
    destruct (rngl_le_dec Hor 0 (rngl_sin θ1)) as [Hzs1| Hs1z]. {
      destruct (rngl_le_dec Hor 0 (rngl_cos θ1)) as [Hzc1| Hc1z]. {
        exfalso.
        apply rngl_nle_gt in Hs12z.
        apply Hs12z; clear Hs12z.
        now apply rngl_sin_add_nonneg.
      }
      apply (rngl_nle_gt_iff Hor) in Hc1z.
      change_angle_sub_r θ1 angle_right.
      progress sin_cos_add_sub_right_hyp T Hzs1.
      progress sin_cos_add_sub_right_hyp T Hc1z.
      progress sin_cos_add_sub_right_hyp T Hs13z.
      progress sin_cos_add_sub_right_hyp T Hs12z.
      progress sin_cos_add_sub_right_goal T.
      rewrite -> (rngl_add_comm (- _))%L.
      progress sin_cos_add_sub_right_goal T.
      destruct (rngl_le_dec Hor (rngl_cos (θ1 + θ3)) 0) as [H| Hzs13]. {
        eapply (rngl_le_trans Hor); [ apply H | ].
        apply (rngl_lt_le_incl Hor) in Hc1z.
        now apply rngl_sin_add_nonneg.
      }
      apply (rngl_nle_gt_iff Hor) in Hzs13.
      change_angle_sub_l θ2 angle_right.
      progress sin_cos_add_sub_right_hyp T Hzs2.
      progress sin_cos_add_sub_right_hyp T Hzc2.
      progress sin_cos_add_sub_right_hyp T Hs12z.
      progress sin_cos_add_sub_right_goal T.
      apply quadrant_1_sin_sub_nonneg_cos_le; try easy.
      now apply (rngl_lt_le_incl Hor).
      now apply (rngl_lt_le_incl Hor).
      apply (rngl_lt_le_incl Hor) in Hc1z.
      now apply rngl_cos_sub_nonneg.
      rewrite angle_sub_sub_distr.
      rewrite angle_add_sub_swap.
      rewrite angle_sub_diag.
      rewrite angle_add_0_l.
      now apply rngl_sin_add_nonneg.
    }
    apply (rngl_nle_gt_iff Hor) in Hs1z.
    destruct (rngl_le_dec Hor 0 (rngl_cos θ1)) as [Hzc1| Hc1z]. {
      exfalso.
      apply rngl_nle_gt in Hs13z.
      apply Hs13z; clear Hs13z.
      now apply rngl_cos_add_nonneg.
    }
    apply (rngl_nle_gt_iff Hor) in Hc1z.
    change_angle_add_r θ1 angle_straight.
    progress sin_cos_add_sub_straight_hyp T Hs1z.
    progress sin_cos_add_sub_straight_hyp T Hc1z.
    progress sin_cos_add_sub_straight_hyp T Hs13z.
    progress sin_cos_add_sub_straight_hyp T Hs12z.
    progress sin_cos_add_sub_straight_goal T.
    rewrite <- (rngl_opp_add_distr Hop).
    rewrite rngl_add_comm.
    apply (rngl_opp_nonpos_nonneg Hop Hor).
    change_angle_sub_l θ3 angle_right.
    progress sin_cos_add_sub_right_hyp T Hzs3.
    progress sin_cos_add_sub_right_hyp T Hc3z.
    progress sin_cos_add_sub_right_hyp T Hs13z.
    progress sin_cos_add_sub_right_goal T.
    rewrite rngl_sin_sub_anticomm in Hs13z.
    rewrite rngl_cos_sub_comm.
    progress sin_cos_add_sub_right_hyp T Hs13z.
    apply rngl_add_cos_nonneg_when_sin_nonneg; try easy.
    now apply (rngl_lt_le_incl Hor).
    now apply (rngl_lt_le_incl Hor).
    rewrite angle_add_assoc.
    rewrite angle_sub_add.
    now apply rngl_sin_add_nonneg.
    apply (rngl_lt_le_incl Hor) in Hs1z, Hc1z.
    now apply rngl_cos_sub_nonneg.
  }
  apply (rngl_nle_gt_iff Hor) in Hc2z.
  change_angle_sub_r θ2 angle_right.
  progress sin_cos_add_sub_right_hyp T Hzs2.
  progress sin_cos_add_sub_right_hyp T Hc2z.
  progress sin_cos_add_sub_right_hyp T Hc32.
  progress sin_cos_add_sub_right_hyp T Hs12z.
  progress sin_cos_add_sub_right_goal T.
  rewrite rngl_add_comm.
  rewrite (rngl_add_opp_r Hop).
  progress sin_cos_add_sub_right_goal T.
  destruct (rngl_eq_dec Heo (rngl_cos θ2) 0) as [H| Hc2ez]. {
    apply (eq_rngl_cos_0) in H.
    destruct H; subst θ2. {
      cbn in Hc32.
      specialize (rngl_sin_bound θ3) as H.
      apply (rngl_le_antisymm Hor) in Hc32; [ clear H | easy ].
      apply (eq_rngl_sin_1) in Hc32.
      subst θ3.
      apply (rngl_le_refl Hor).
    }
    exfalso.
    apply rngl_nle_gt in Hc2z.
    apply Hc2z; cbn.
    apply (rngl_opp_1_le_0 Hon Hop Hiq Hor).
  }
  assert (H : (0 < rngl_cos θ2)%L). {
    apply not_eq_sym in Hc2ez.
    now apply (rngl_le_neq Hor).
  }
  move H before Hzs2; clear Hzs2.
  rename H into Hzs2; clear Hc2ez.
  destruct (rngl_eq_dec Heo (rngl_cos θ3) 0) as [H| Hc3ez]. {
    apply (eq_rngl_cos_0) in H.
    destruct H; subst θ3. 2: {
      exfalso.
      apply rngl_nlt_ge in Hc3z.
      apply Hc3z; cbn.
      apply (rngl_opp_1_lt_0 Hon Hop Hiq Hor Hc1).
    }
    clear Hc3z Hc32 Hzs3.
    rewrite rngl_sin_add_right_r.
    rewrite rngl_cos_add_right_r in Hs13z.
    apply (rngl_opp_neg_pos Hop Hor) in Hs13z.
    destruct (rngl_le_dec Hor 0 (rngl_cos θ1)) as [Hzc1| Hc1z]. {
      apply (rngl_lt_le_incl Hor) in Hzs2, Hc2z, Hs13z, Hs12z.
      change_angle_sub_l θ2 angle_right.
      progress sin_cos_add_sub_right_hyp T Hzs2.
      progress sin_cos_add_sub_right_hyp T Hc2z.
      progress sin_cos_add_sub_right_hyp T Hs12z.
      progress sin_cos_add_sub_right_goal T.
      apply rngl_cos_cos_sin_sin_nonneg_sin_le_cos_le_iff; try easy.
      apply rngl_cos_sub_nonneg; try easy.
      apply rngl_sin_sub_nonneg_sin_le_sin; try easy.
      rewrite angle_sub_sub_distr.
      rewrite angle_sub_diag.
      now rewrite angle_add_0_l.
    }
    apply (rngl_nle_gt_iff Hor) in Hc1z.
    apply (rngl_lt_le_incl Hor) in Hzs2, Hc2z, Hs13z, Hc1z.
    change_angle_sub_r θ1 angle_right.
    progress sin_cos_add_sub_right_hyp T Hc1z.
    progress sin_cos_add_sub_right_hyp T Hs12z.
    progress sin_cos_add_sub_right_hyp T Hs13z.
    progress sin_cos_add_sub_right_goal T.
    change_angle_sub_l θ2 angle_right.
    progress sin_cos_add_sub_right_hyp T Hzs2.
    progress sin_cos_add_sub_right_goal T.
    apply rngl_sin_sub_nonneg_sin_le_sin; try easy.
    rewrite angle_sub_sub_distr.
    rewrite angle_sub_diag.
    now rewrite angle_add_0_l.
  }
  assert (H : (0 < rngl_cos θ3)%L). {
    apply not_eq_sym in Hc3ez.
    now apply (rngl_le_neq Hor).
  }
  move H before Hzs3; clear Hzs3.
  rename H into Hzs3; clear Hc3ez.
  destruct (rngl_le_dec Hor 0 (rngl_sin θ1)) as [Hzs1| Hs1z]. {
    destruct (rngl_le_dec Hor 0 (rngl_cos θ1)) as [Hzc1| Hc1z]. {
      apply (rngl_lt_le_incl Hor) in Hzs2, Hc2z, Hzs3, Hs12z, Hs13z.
      assert (Hzs12 : (0 ≤ rngl_sin (θ1 + θ2))%L). {
        now apply rngl_sin_add_nonneg.
      }
      assert (Hzs13 : (0 ≤ rngl_sin (θ1 + θ3))%L). {
        now apply rngl_sin_add_nonneg.
      }
      apply rngl_cos_cos_sin_sin_neg_sin_le_cos_le_iff; try easy.
      apply angle_add_le_mono_l_lemma_1; try easy; cycle 1.
      apply rngl_cos_cos_sin_sin_nonneg_sin_le_cos_le_iff; try easy.
      (* pas l'air de marcher avec le truc habituel *)
      (* (rngl_sin_add_nonneg_angle_add_not_overflow) *)
      clear - ac Hzs13 Hzs1 Hor Hs13z Hzs13 Hzc1.
      rewrite <- angle_add_overflow_equiv2.
      progress unfold angle_add_overflow2.
      progress unfold angle_ltb.
      generalize Hzs13; intros H.
      apply rngl_leb_le in H.
      rewrite H; clear H.
      generalize Hzs1; intros H.
      apply rngl_leb_le in H.
      rewrite H; clear H.
      apply rngl_ltb_ge.
      now apply (rngl_le_trans Hor _ 0).
    }
    apply (rngl_nle_gt_iff Hor) in Hc1z.
    apply (rngl_lt_le_incl Hor) in Hzs2, Hc2z, Hzs3, Hs12z, Hs13z.
    apply (rngl_lt_le_incl Hor) in Hc1z.
    change_angle_sub_r θ1 angle_right.
    progress sin_cos_add_sub_right_hyp T Hzs1.
    progress sin_cos_add_sub_right_hyp T Hc1z.
    progress sin_cos_add_sub_right_hyp T Hs13z.
    progress sin_cos_add_sub_right_hyp T Hs12z.
    progress sin_cos_add_sub_right_goal T.
    apply angle_add_le_mono_l_lemma_1; try easy; cycle 1.
    apply rngl_cos_cos_sin_sin_nonneg_sin_le_cos_le_iff; try easy.
    rewrite <- angle_add_overflow_equiv2.
    progress unfold angle_add_overflow2.
    progress unfold angle_ltb.
    generalize Hs13z; intros H.
    apply rngl_leb_le in H.
    rewrite H; clear H.
    generalize Hc1z; intros H.
    apply rngl_leb_le in H.
    rewrite H; clear H.
    apply rngl_ltb_ge.
    now apply quadrant_1_rngl_cos_add_le_cos_l.
  }
  apply (rngl_nle_gt_iff Hor) in Hs1z.
  apply (rngl_lt_le_incl Hor) in Hzs2, Hc2z.
  destruct (rngl_le_dec Hor 0 (rngl_cos θ1)) as [Hzc1| Hc1z]. {
    exfalso.
    apply rngl_nle_gt in Hs12z.
    apply Hs12z; clear Hs12z.
    now apply rngl_cos_add_nonneg.
  }
  apply (rngl_nle_gt_iff Hor) in Hc1z.
  apply (rngl_lt_le_incl Hor) in Hzs3, Hs13z.
  change_angle_add_r θ1 angle_straight.
  progress sin_cos_add_sub_straight_hyp T Hs1z.
  progress sin_cos_add_sub_straight_hyp T Hc1z.
  progress sin_cos_add_sub_straight_hyp T Hs13z.
  progress sin_cos_add_sub_straight_hyp T Hs12z.
  progress sin_cos_add_sub_straight_goal T.
  apply (rngl_lt_le_incl Hor) in Hc1z, Hs1z.
  apply (rngl_lt_le_incl Hor) in Hs12z.
  apply rngl_cos_cos_sin_sin_nonneg_sin_le_cos_le_iff; try easy.
  apply rngl_sin_add_nonneg; try easy.
  apply rngl_sin_add_nonneg; try easy.
  apply angle_add_le_mono_l_lemma_3; try easy; cycle 1.
  apply rngl_sin_add_nonneg; try easy.
  apply rngl_sin_add_nonneg; try easy.
  apply rngl_cos_cos_sin_sin_nonneg_sin_le_cos_le_iff; try easy.
  rewrite <- angle_add_overflow_equiv2.
  progress unfold angle_add_overflow2.
  progress unfold angle_ltb.
  generalize Hs1z; intros H.
  apply (rngl_sin_add_nonneg θ3) in H; try easy.
  rewrite angle_add_comm in H.
  apply rngl_leb_le in H.
  rewrite H; clear H.
  apply rngl_leb_le in Hs1z.
  rewrite Hs1z.
  apply rngl_leb_le in Hs1z.
  apply rngl_ltb_ge.
  now apply quadrant_1_rngl_cos_add_le_cos_l.
}
clear H23.
apply (rngl_leb_gt Hor) in Hzs3.
destruct zs13. {
  exfalso.
  apply rngl_leb_le in Hzs13.
  apply rngl_nle_gt in Hzs12.
  apply Hzs12; clear Hzs12.
  destruct (rngl_le_dec Hor 0 (rngl_cos θ2)) as [Hzc2| Hc2z]. {
    destruct (rngl_le_dec Hor 0 (rngl_sin θ1)) as [Hzs1| Hs1z]. {
      destruct (rngl_le_dec Hor 0 (rngl_cos θ1)) as [Hzc1| Hc1z]. {
        now apply rngl_sin_add_nonneg.
      }
      apply (rngl_nle_gt_iff Hor) in Hc1z.
      exfalso.
      apply (Bool.not_true_iff_false) in Haov13.
      apply Haov13; clear Haov13.
      rewrite <- angle_add_overflow_equiv2.
      progress unfold angle_add_overflow2.
      progress unfold angle_ltb.
      generalize Hzs13; intros H.
      apply rngl_leb_le in H.
      rewrite H; clear H.
      apply rngl_leb_le in Hzs1.
      rewrite Hzs1.
      apply rngl_leb_le in Hzs1.
      apply rngl_ltb_lt.
      change_angle_sub_r θ1 angle_right.
      progress sin_cos_add_sub_right_hyp T Hzs1.
      progress sin_cos_add_sub_right_hyp T Hzs13.
      progress sin_cos_add_sub_right_hyp T Hc1z.
      progress sin_cos_add_sub_right_goal T.
      rewrite -> (rngl_add_opp_r Hop).
      apply <- (rngl_lt_0_sub Hop Hor).
      change_angle_add_r θ3 angle_right.
      progress sin_cos_add_sub_right_hyp T Hzs3.
      progress sin_cos_add_sub_right_goal T.
      destruct (rngl_eq_dec Heo (rngl_sin θ3) 1) as [Hs21| Hs21]. {
        apply (eq_rngl_sin_1) in Hs21.
        subst θ3.
        now apply (rngl_lt_irrefl Hor) in Hzs3.
      }
      cbn.
      rewrite <- (rngl_add_sub_swap Hop).
      rewrite <- (rngl_add_sub_assoc Hop).
      rewrite (rngl_sub_mul_r_diag_l Hon Hop).
      apply (rngl_add_nonneg_pos Hos Hor).
      apply (rngl_mul_nonneg_nonneg Hon Hos Hiq Hor); [ easy | ].
      now apply (rngl_lt_le_incl Hor).
      apply (rngl_mul_pos_pos Hon Hop Hiq Hor); [ easy | ].
      apply (rngl_lt_0_sub Hop Hor).
      apply (rngl_le_neq Hor).
      split; [ | easy ].
      apply rngl_sin_bound.
    }
    apply (rngl_nle_gt_iff Hor) in Hs1z.
    destruct (rngl_le_dec Hor 0 (rngl_cos θ1)) as [Hzc1| Hc1z]. 2: {
      apply (rngl_nle_gt_iff Hor) in Hc1z.
      rewrite angle_add_overflow_comm in Haov13; try easy.
      exfalso.
      apply Bool.not_true_iff_false in Haov13.
      apply Haov13; clear Haov13.
      apply angle_add_le_mono_l_lemma_11; try easy.
      now rewrite angle_add_comm.
    }
    change_angle_add_r θ1 angle_right.
    progress sin_cos_add_sub_right_hyp T Hs1z.
    progress sin_cos_add_sub_right_hyp T Hzs13.
    progress sin_cos_add_sub_right_hyp T Hzc1.
    progress sin_cos_add_sub_right_goal T.
    destruct (rngl_lt_dec Hor (rngl_cos θ3) 0) as [Hc3z| Hzc3]. {
      apply (rngl_nlt_ge_iff Hor).
      intros Hzc12.
      apply Bool.not_true_iff_false in Haov13.
      apply Haov13; clear Haov13.
      apply angle_add_le_mono_l_lemma_11; try easy.
      rewrite <- angle_add_sub_swap.
      rewrite rngl_sin_sub_right_r.
      now apply (rngl_opp_nonneg_nonpos Hop Hor).
    }
    apply (rngl_nlt_ge_iff Hor) in Hzc3.
    exfalso.
    apply Bool.not_true_iff_false in Haov13.
    apply Haov13; clear Haov13.
    rename θ3 into θ.
    rename θ2 into θ3.
    rename θ into θ2.
    change_angle_add_r θ2 angle_right.
    progress sin_cos_add_sub_right_hyp T Hzs13.
    rewrite <- angle_add_overflow_equiv2.
    progress unfold angle_add_overflow2.
    progress unfold angle_ltb.
    rewrite rngl_sin_sub_right_r.
    rewrite angle_add_sub_assoc.
    rewrite <- angle_add_sub_swap.
    rewrite rngl_sin_sub_right_r.
    rewrite rngl_cos_sub_right_r.
    generalize Hzs13; intros H.
    apply (rngl_opp_le_compat Hop Hor) in H.
    rewrite (rngl_opp_0 Hop) in H.
    apply rngl_leb_le in H.
    rewrite H; clear H.
    generalize Hs1z; intros H.
    apply (rngl_opp_lt_compat Hop Hor) in H.
    rewrite (rngl_opp_0 Hop) in H.
    apply rngl_nle_gt in H.
    apply rngl_leb_nle in H.
    now rewrite H.
  }
  apply (rngl_nle_gt_iff Hor) in Hc2z.
  change_angle_sub_r θ2 angle_right.
  progress sin_cos_add_sub_right_hyp T Hzs2.
  progress sin_cos_add_sub_right_hyp T Hc2z.
  progress sin_cos_add_sub_right_goal T.
  destruct (rngl_le_dec Hor (rngl_sin θ1) 0) as [Hs1z| Hzs1]. {
    destruct (rngl_le_dec Hor 0 (rngl_cos θ1)) as [Hzc1| Hc1z]. {
      rewrite angle_add_comm.
      rewrite <- angle_sub_opp_r.
      apply (rngl_lt_le_incl Hor) in Hc2z.
      apply (rngl_opp_le_compat Hop Hor) in Hs1z.
      rewrite (rngl_opp_0 Hop) in Hs1z.
      rewrite <- rngl_sin_opp in Hs1z.
      now apply rngl_cos_sub_nonneg.
    }
    apply (rngl_nle_gt_iff Hor) in Hc1z.
    change_angle_add_r θ1 angle_straight.
    progress sin_cos_add_sub_straight_hyp T Hs1z.
    progress sin_cos_add_sub_straight_hyp T Hc1z.
    progress sin_cos_add_sub_straight_hyp T Hzs13.
    progress sin_cos_add_sub_straight_goal T.
    exfalso.
    apply Bool.not_true_iff_false in Haov13.
    apply Haov13; clear Haov13.
    rename θ2 into θ.
    rename θ3 into θ2.
    rename θ into θ3.
    rewrite <- angle_add_overflow_equiv2.
    progress unfold angle_add_overflow2.
    rewrite <- angle_add_sub_swap.
    progress unfold angle_ltb.
    do 2 rewrite rngl_sin_sub_straight_r.
    generalize Hzs13; intros H.
    apply (rngl_opp_le_compat Hop Hor) in H.
    rewrite (rngl_opp_0 Hop) in H.
    apply rngl_leb_le in H.
    rewrite H; clear H.
    generalize Hs1z; intros H.
    apply (rngl_lt_eq_cases Hor) in H.
    destruct H as [H| H]. {
      apply (rngl_opp_lt_compat Hop Hor) in H.
      rewrite (rngl_opp_0 Hop) in H.
      apply rngl_nle_gt in H.
      apply rngl_leb_nle in H.
      now rewrite H.
    }
    do 2 rewrite rngl_cos_sub_straight_r.
    rewrite <- H.
    rewrite (rngl_opp_0 Hop).
    rewrite (rngl_leb_refl Hor).
    apply rngl_ltb_lt.
    apply -> (rngl_opp_lt_compat Hop Hor).
    symmetry in H.
    apply (eq_rngl_sin_0) in H.
    destruct H; subst θ1. {
      rewrite angle_add_0_l; cbn.
      apply (rngl_le_neq Hor).
      split; [ apply rngl_cos_bound | ].
      intros H.
      apply (eq_rngl_cos_1) in H.
      subst θ2.
      now apply (rngl_lt_irrefl Hor) in Hzs3.
    }
    rewrite rngl_sin_add_straight_l in Hzs13.
    apply (rngl_opp_nonpos_nonneg Hop Hor) in Hzs13.
    now apply rngl_nlt_ge in Hzs13.
  }
  apply (rngl_nle_gt_iff Hor) in Hzs1.
  destruct (rngl_le_dec Hor 0 (rngl_cos θ3)) as [Hzc3| Hc3z]. {
    apply (rngl_nlt_ge_iff Hor).
    intros Hc12z.
    apply Bool.not_true_iff_false in Haov13.
    apply Haov13; clear Haov13.
    rename θ2 into θ.
    rename θ3 into θ2.
    rename θ into θ3.
    rewrite <- angle_add_overflow_equiv2.
    progress unfold angle_add_overflow2.
    progress unfold angle_ltb.
    generalize Hzs13; intros H.
    apply rngl_leb_le in H.
    rewrite H; clear H.
    generalize Hzs1; intros H.
    apply (rngl_lt_le_incl Hor) in H.
    apply rngl_leb_le in H.
    rewrite H; clear H.
    apply rngl_ltb_lt.
    destruct (rngl_le_dec Hor (rngl_cos θ1) 0) as [Hc1z| Hzc1]. 2: {
      apply (rngl_nle_gt_iff Hor) in Hzc1.
      apply (rngl_lt_le_incl Hor) in Hzs1, Hzc1.
      now apply quadrant_1_quadrant_4_cos_lt_cos_add.
    }
    change_angle_add_r θ2 angle_right.
    progress sin_cos_add_sub_right_hyp T Hzs3.
    progress sin_cos_add_sub_right_goal T.
    change_angle_sub_r θ1 angle_right.
    progress sin_cos_add_sub_right_hyp T Hc1z.
    progress sin_cos_add_sub_right_hyp T Hzs1.
    progress sin_cos_add_sub_right_goal T.
    cbn.
    rewrite (rngl_add_sub_assoc Hop).
    rewrite rngl_add_comm.
    rewrite <- (rngl_add_sub_assoc Hop).
    rewrite (rngl_sub_mul_r_diag_l Hon Hop).
    apply (rngl_lt_0_add Hos Hor).
    now apply (rngl_mul_pos_pos Hon Hop Hiq Hor).
    apply (rngl_mul_nonneg_nonneg Hon Hos Hiq Hor); [ easy | ].
    apply (rngl_le_0_sub Hop Hor).
    apply rngl_sin_bound.
  }
  apply (rngl_nle_gt_iff Hor) in Hc3z.
  change_angle_add_r θ3 angle_straight.
  progress sin_cos_add_sub_straight_hyp T Hzs13.
  progress sin_cos_add_sub_straight_hyp T Hc3z.
  progress sin_cos_add_sub_straight_hyp T Hzs3.
  destruct (rngl_lt_dec Hor 0 (rngl_cos θ1)) as [Hzc1| Hc1z]. {
    exfalso.
    apply rngl_nlt_ge in Hzs13.
    apply Hzs13; clear Hzs13.
    apply (rngl_sin_add_pos_1); try easy.
    now apply (rngl_lt_le_incl Hor).
    now apply (rngl_lt_le_incl Hor).
  }
  apply (rngl_nlt_ge_iff Hor) in Hc1z.
  exfalso.
  change_angle_sub_r θ1 angle_right.
  progress sin_cos_add_sub_right_hyp T Hzs13.
  progress sin_cos_add_sub_right_hyp T Hzs1.
  progress sin_cos_add_sub_right_hyp T Hc1z.
  apply Bool.not_true_iff_false in Haov13.
  apply Haov13; clear Haov13.
  apply angle_add_le_mono_l_lemma_11; try easy.
  rewrite rngl_sin_sub_straight_r.
  now apply (rngl_opp_neg_pos Hop Hor).
  rewrite rngl_cos_sub_straight_r.
  now apply (rngl_opp_neg_pos Hop Hor).
  rewrite angle_add_sub_assoc.
  rewrite angle_add_add_swap.
  rewrite angle_add_sub_swap.
  rewrite <- angle_sub_sub_distr.
  rewrite angle_straight_sub_right.
  rewrite rngl_sin_sub_right_r.
  now apply (rngl_opp_nonneg_nonpos Hop Hor).
}
apply (rngl_leb_gt Hor) in Hzs13.
apply rngl_leb_le.
destruct (rngl_le_dec Hor 0 (rngl_cos θ3)) as [Hzc3| Hc3z]. {
  change_angle_add_r θ3 angle_right.
  progress sin_cos_add_sub_right_hyp T Hzs3.
  progress sin_cos_add_sub_right_hyp T Hzc3.
  progress sin_cos_add_sub_right_hyp T Hzs13.
  progress sin_cos_add_sub_right_goal T.
  destruct (rngl_le_dec Hor (rngl_cos θ2) 0)%L as [Hc2z| Hzc2]. 2: {
    apply (rngl_nle_gt_iff Hor) in Hzc2.
    exfalso.
    destruct (rngl_le_dec Hor 0 (rngl_sin θ1)) as [Hzs1| Hs1z]. {
      destruct (rngl_le_dec Hor (rngl_cos θ1) 0) as [Hc1z| Hzc1]. {
        apply rngl_nle_gt in Hzs13.
        apply Hzs13; clear Hzs13.
        change_angle_sub_r θ1 angle_right.
        progress sin_cos_add_sub_right_hyp T Hzs12.
        progress sin_cos_add_sub_right_hyp T Hc1z.
        progress sin_cos_add_sub_right_hyp T Hzs1.
        progress sin_cos_add_sub_right_goal T.
        apply rngl_sin_add_nonneg; try easy.
        now apply (rngl_lt_le_incl Hor).
      } {
        apply (rngl_nle_gt_iff Hor) in Hzc1.
        apply rngl_nle_gt in Hzs12.
        apply Hzs12; clear Hzs12.
        apply rngl_sin_add_nonneg; try easy.
        now apply (rngl_lt_le_incl Hor).
        now apply (rngl_lt_le_incl Hor).
      }
    } {
      apply (rngl_nle_gt_iff Hor) in Hs1z.
      destruct (rngl_le_dec Hor (rngl_cos θ1) 0) as [Hc1z| Hzc1]. {
        change_angle_add_r θ1 angle_straight.
        progress sin_cos_add_sub_straight_hyp T Hzs12.
        progress sin_cos_add_sub_straight_hyp T Hzs13.
        progress sin_cos_add_sub_straight_hyp T Hc1z.
        progress sin_cos_add_sub_straight_hyp T Hs1z.
        apply Bool.not_true_iff_false in Haov13.
        apply Haov13; clear Haov13.
        rewrite <- angle_add_overflow_equiv2.
        progress unfold angle_add_overflow2.
        rewrite angle_add_sub_assoc.
        rewrite <- angle_add_sub_swap.
        rewrite angle_sub_sub_swap.
        progress unfold angle_ltb.
        do 2 rewrite rngl_sin_sub_straight_r.
        rewrite rngl_sin_sub_right_r.
        rewrite (rngl_opp_involutive Hop).
        generalize Hzs13; intros H.
        apply rngl_nle_gt in H.
        apply rngl_leb_nle in H.
        rewrite H; clear H.
        generalize Hs1z; intros H.
        apply (rngl_opp_lt_compat Hop Hor) in H.
        rewrite (rngl_opp_0 Hop) in H.
        apply rngl_nle_gt in H.
        apply rngl_leb_nle in H.
        rewrite H; clear H.
        apply rngl_ltb_lt.
        progress sin_cos_add_sub_straight_goal T.
        progress sin_cos_add_sub_right_goal T.
        apply (rngl_lt_0_sub Hop Hor).
        change_angle_sub_l θ3 angle_right.
        progress sin_cos_add_sub_right_hyp T Hzs3.
        progress sin_cos_add_sub_right_hyp T Hzs13.
        progress sin_cos_add_sub_right_hyp T Hzc3.
        progress sin_cos_add_sub_right_goal T.
        rewrite rngl_cos_sub_comm.
        apply rngl_cos_lt_cos_sub; try easy.
        now apply (rngl_lt_le_incl Hor).
        apply (rngl_lt_le_incl Hor).
        apply quadrant_1_sin_sub_pos_cos_lt; try easy.
        now apply (rngl_lt_le_incl Hor).
        now apply (rngl_lt_le_incl Hor).
      } {
        apply (rngl_nle_gt_iff Hor) in Hzc1.
        change_angle_add_r θ1 angle_right.
        progress sin_cos_add_sub_right_hyp T Hzs12.
        progress sin_cos_add_sub_right_hyp T Hzs13.
        progress sin_cos_add_sub_right_hyp T Hzc1.
        progress sin_cos_add_sub_right_hyp T Hs1z.
        apply Bool.not_true_iff_false in Haov13.
        apply Haov13; clear Haov13.
        rewrite <- angle_add_overflow_equiv2.
        progress unfold angle_add_overflow2.
        rewrite angle_add_sub_assoc.
        rewrite <- angle_add_sub_swap.
        rewrite <- angle_sub_add_distr.
        rewrite angle_right_add_right.
        progress unfold angle_ltb.
        rewrite rngl_sin_sub_straight_r.
        rewrite rngl_sin_sub_right_r.
        generalize Hzs13; intros H.
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
        apply (rngl_lt_le_incl Hor) in Hzc1.
        apply (rngl_lt_0_add Hos Hor).
        now apply (rngl_mul_pos_pos Hon Hop Hiq Hor).
        apply (rngl_mul_nonneg_nonneg Hon Hos Hiq Hor); [ easy | ].
        apply (rngl_le_0_sub Hop Hor).
        apply rngl_sin_bound.
      }
    }
  }
  change_angle_sub_r θ2 angle_right.
  progress sin_cos_add_sub_right_hyp T Hzs2.
  progress sin_cos_add_sub_right_hyp T Hc2z.
  progress sin_cos_add_sub_right_goal T.
  destruct (rngl_le_dec Hor 0 (rngl_sin θ1)) as [Hzs1| Hs1z]. {
    destruct (rngl_le_dec Hor 0 (rngl_cos θ1)) as [Hzc1| Hc1z]. {
      apply (rngl_le_0_add Hos Hor).
      now apply rngl_sin_add_nonneg.
      apply rngl_sin_add_nonneg; try easy.
      now apply (rngl_lt_le_incl Hor).
    }
    exfalso.
    apply rngl_nle_gt in Hzs13.
    apply Hzs13; clear Hzs13.
    apply (rngl_nle_gt_iff Hor) in Hc1z.
    change_angle_sub_r θ1 angle_right.
    progress sin_cos_add_sub_right_hyp T Hc1z.
    progress sin_cos_add_sub_right_hyp T Hzs1.
    progress sin_cos_add_sub_right_goal T.
    apply rngl_sin_add_nonneg; try easy.
    now apply (rngl_lt_le_incl Hor).
    now apply (rngl_lt_le_incl Hor).
  }
  apply (rngl_nle_gt_iff Hor) in Hs1z.
  destruct (rngl_le_dec Hor 0 (rngl_cos θ1)) as [Hzc1| Hc1z]. {
    exfalso.
    change_angle_add_r θ1 angle_right.
    progress sin_cos_add_sub_right_hyp T Hzs13.
    progress sin_cos_add_sub_right_hyp T Hzc1.
    progress sin_cos_add_sub_right_hyp T Hs1z.
    apply Bool.not_true_iff_false in Haov13.
    apply Haov13; clear Haov13.
    rewrite <- angle_add_overflow_equiv2.
    progress unfold angle_add_overflow2.
    rewrite angle_add_sub_assoc.
    rewrite <- angle_add_sub_swap.
    rewrite <- angle_sub_add_distr.
    rewrite angle_right_add_right.
    progress unfold angle_ltb.
    rewrite rngl_sin_sub_straight_r.
    rewrite rngl_sin_sub_right_r.
    generalize Hzs13; intros H.
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
    apply (rngl_lt_0_add Hos Hor).
    now apply (rngl_mul_pos_pos Hon Hop Hiq Hor).
    apply (rngl_mul_nonneg_nonneg Hon Hos Hiq Hor); [ easy | ].
    apply (rngl_le_0_sub Hop Hor).
    apply rngl_sin_bound.
  }
  apply (rngl_nle_gt_iff Hor) in Hc1z.
  exfalso.
  change_angle_add_r θ1 angle_straight.
  progress sin_cos_add_sub_straight_hyp T Hzs13.
  progress sin_cos_add_sub_straight_hyp T Hc1z.
  progress sin_cos_add_sub_straight_hyp T Hs1z.
  apply Bool.not_true_iff_false in Haov13.
  apply Haov13; clear Haov13.
  rewrite <- angle_add_overflow_equiv2.
  progress unfold angle_add_overflow2.
  rewrite angle_add_sub_assoc.
  rewrite <- angle_add_sub_swap.
  rewrite angle_sub_sub_swap.
  progress unfold angle_ltb.
  do 2 rewrite rngl_sin_sub_straight_r.
  rewrite rngl_sin_sub_right_r.
  rewrite (rngl_opp_involutive Hop).
  generalize Hzs13; intros H.
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
  change_angle_sub_l θ3 angle_right.
  progress sin_cos_add_sub_right_hyp T Hzs3.
  progress sin_cos_add_sub_right_hyp T Hzs13.
  progress sin_cos_add_sub_right_hyp T Hzc3.
  progress sin_cos_add_sub_right_goal T.
  rewrite rngl_cos_sub_comm.
  apply rngl_cos_lt_cos_sub; try easy.
  now apply (rngl_lt_le_incl Hor).
  apply (rngl_lt_le_incl Hor) in Hc1z, Hzs3, Hs1z.
  apply (rngl_lt_le_incl Hor).
  apply quadrant_1_sin_sub_pos_cos_lt; try easy.
}
apply (rngl_nle_gt_iff Hor) in Hc3z.
change_angle_add_r θ3 angle_straight.
progress sin_cos_add_sub_straight_hyp T Hzs3.
progress sin_cos_add_sub_straight_hyp T Hc3z.
progress sin_cos_add_sub_straight_hyp T Hzs13.
progress sin_cos_add_sub_straight_goal T.
destruct (rngl_le_dec Hor 0 (rngl_cos θ2)) as [Hzc2| Hc2z]. {
  apply (rngl_lt_le_incl Hor) in Hc3z.
  destruct (rngl_le_dec Hor 0 (rngl_sin θ1)) as [Hzs1| Hs1z]. {
    destruct (rngl_le_dec Hor 0 (rngl_cos θ1)) as [Hzc1| Hc1z]. {
      exfalso.
      apply rngl_nle_gt in Hzs12.
      apply Hzs12; clear Hzs12.
      now apply rngl_sin_add_nonneg.
    } {
      apply (rngl_nle_gt_iff Hor) in Hc1z.
      apply (rngl_lt_le_incl Hor) in Hzs3.
      change_angle_sub_r θ1 angle_right.
      progress sin_cos_add_sub_right_hyp T Hzs12.
      progress sin_cos_add_sub_right_hyp T Hzs13.
      progress sin_cos_add_sub_right_hyp T Hc1z.
      progress sin_cos_add_sub_right_hyp T Hzs1.
      progress sin_cos_add_sub_right_goal T.
      apply (rngl_le_opp_l Hop Hor).
      apply (rngl_lt_le_incl Hor) in Hc1z.
      apply (rngl_le_0_add Hos Hor).
      now apply rngl_sin_add_nonneg.
      now apply rngl_sin_add_nonneg.
    }
  } {
    apply (rngl_nle_gt_iff Hor) in Hs1z.
    exfalso.
    destruct (rngl_le_dec Hor 0 (rngl_cos θ1)) as [Hzc1| Hc1z]. {
      change_angle_add_r θ1 angle_right.
      progress sin_cos_add_sub_right_hyp T Hzs12.
      progress sin_cos_add_sub_right_hyp T Hzs13.
      progress sin_cos_add_sub_right_hyp T Hzc1.
      progress sin_cos_add_sub_right_hyp T Hs1z.
      apply Bool.not_true_iff_false in Haov13.
      apply Haov13; clear Haov13.
      rewrite <- angle_add_overflow_equiv2.
      progress unfold angle_add_overflow2.
      progress sin_cos_add_sub_straight_goal T.
      progress sin_cos_add_sub_right_goal T.
      progress unfold angle_ltb.
      rewrite rngl_sin_sub_straight_r.
      rewrite rngl_sin_sub_right_r.
      rewrite (rngl_opp_involutive Hop).
      generalize Hzs13; intros H.
      apply rngl_nle_gt in H.
      apply rngl_leb_nle in H.
      rewrite H; clear H.
      rewrite rngl_sin_sub_right_r.
      generalize Hs1z; intros H.
      apply (rngl_opp_lt_compat Hop Hor) in H.
      rewrite (rngl_opp_0 Hop) in H.
      apply rngl_nle_gt in H.
      apply rngl_leb_nle in H.
      rewrite H; clear H.
      apply rngl_ltb_lt.
      progress sin_cos_add_sub_straight_goal T.
      progress sin_cos_add_sub_right_goal T.
      apply (rngl_lt_0_add Hos Hor); [ | easy ].
      now apply (rngl_sin_add_pos_1).
    } {
      apply (rngl_nle_gt_iff Hor) in Hc1z.
      change_angle_add_r θ1 angle_straight.
      progress sin_cos_add_sub_straight_hyp T Hzs12.
      progress sin_cos_add_sub_straight_hyp T Hzs13.
      progress sin_cos_add_sub_straight_hyp T Hc1z.
      progress sin_cos_add_sub_straight_hyp T Hs1z.
      apply rngl_nle_gt in Hzs13.
      apply Hzs13; clear Hzs13.
      apply (rngl_lt_le_incl Hor) in Hs1z, Hzs3, Hc1z.
      now apply rngl_sin_add_nonneg.
    }
  }
}
apply (rngl_nle_gt_iff Hor) in Hc2z.
apply (rngl_lt_le_incl Hor) in Hc2z, Hzs3, Hc3z.
change_angle_sub_r θ2 angle_right.
progress sin_cos_add_sub_right_hyp T Hzs2.
progress sin_cos_add_sub_right_hyp T Hzs12.
progress sin_cos_add_sub_right_hyp T Hc2z.
progress sin_cos_add_sub_right_goal T.
rewrite (rngl_add_opp_l Hop).
apply (rngl_le_sub_0 Hop Hor).
destruct (rngl_le_dec Hor 0 (rngl_sin θ1)) as [Hzs1| Hs1z]. 2: {
  exfalso.
  apply (rngl_nle_gt_iff Hor) in Hs1z.
  apply (rngl_lt_le_incl Hor) in Hs1z.
  destruct (rngl_le_dec Hor 0 (rngl_cos θ1)) as [Hzc1| Hc1z]. {
    change_angle_add_r θ1 angle_right.
    progress sin_cos_add_sub_right_hyp T Hzs12.
    progress sin_cos_add_sub_right_hyp T Hzs13.
    progress sin_cos_add_sub_right_hyp T Hzc1.
    progress sin_cos_add_sub_right_hyp T Hs1z.
    apply rngl_nle_gt in Hzs12.
    apply Hzs12; clear Hzs12.
    now apply rngl_sin_add_nonneg.
  } {
    apply (rngl_nle_gt_iff Hor) in Hc1z.
    apply (rngl_lt_le_incl Hor) in Hc1z.
    change_angle_add_r θ1 angle_straight.
    progress sin_cos_add_sub_straight_hyp T Hzs12.
    progress sin_cos_add_sub_straight_hyp T Hzs13.
    progress sin_cos_add_sub_straight_hyp T Hc1z.
    progress sin_cos_add_sub_straight_hyp T Hs1z.
    apply rngl_nle_gt in Hzs13.
    apply Hzs13; clear Hzs13.
    now apply rngl_sin_add_nonneg.
  }
}
apply (rngl_lt_le_incl Hor) in Hzs13, Hzs12.
destruct (rngl_le_dec Hor 0 (rngl_cos θ1)) as [Hzc1| Hc1z]. {
  rename Hzs12 into Hc12z.
  change_angle_sub_l θ1 angle_right.
  progress sin_cos_add_sub_right_hyp T Hc12z.
  progress sin_cos_add_sub_right_hyp T Hzs13.
  progress sin_cos_add_sub_right_hyp T Hzc1.
  progress sin_cos_add_sub_right_hyp T Hzs1.
  progress sin_cos_add_sub_right_goal T.
  rewrite rngl_sin_sub_anticomm in Hc12z.
  apply (rngl_opp_nonpos_nonneg Hop Hor) in Hc12z.
  apply (rngl_nlt_ge_iff Hor).
  intros Hc12s13.
  rename Hzs13 into Hzc13.
  assert (Hzs13 : (0 ≤ rngl_sin (θ1 - θ3))%L). {
    apply (rngl_lt_le_incl Hor) in Hc12s13.
    eapply (rngl_le_trans Hor); [ | apply Hc12s13 ].
    now apply rngl_cos_sub_nonneg.
  }
  change_angle_sub_l θ2 angle_right.
  progress sin_cos_add_sub_right_hyp T Hzs2.
  progress sin_cos_add_sub_right_hyp T Hc12z.
  progress sin_cos_add_sub_right_hyp T Hc2z.
  progress sin_cos_add_sub_right_hyp T Hc12s13.
  rewrite angle_add_comm in Hc12s13.
  apply rngl_nle_gt in Hc12s13.
  apply Hc12s13; clear Hc12s13.
  destruct (rngl_le_dec Hor (rngl_cos θ3) (rngl_cos θ2)) as [Hc32| Hc23]. {
    cbn.
    rewrite (rngl_mul_opp_r Hop).
    rewrite (rngl_add_opp_r Hop).
    apply (rngl_le_sub_le_add_l Hop Hor).
    rewrite rngl_add_assoc.
    apply (rngl_le_0_sub Hop Hor).
    rewrite rngl_add_add_swap.
    rewrite <- (rngl_add_sub_assoc Hop).
    rewrite <- (rngl_mul_sub_distr_l Hop).
    rewrite <- rngl_mul_add_distr_l.
    apply (rngl_le_0_add Hos Hor).
    apply (rngl_mul_nonneg_nonneg Hon Hos Hiq Hor); [ easy | ].
    now apply (rngl_le_0_add Hos Hor).
    apply (rngl_mul_nonneg_nonneg Hon Hos Hiq Hor); [ easy | ].
    now apply (rngl_le_0_sub Hop Hor).
  }
  apply (rngl_nle_gt_iff Hor) in Hc23.
  rewrite angle_add_comm in Hc12z.
  apply rngl_cos_cos_sin_sin_nonneg_sin_le_cos_le_iff; try easy.
  apply rngl_sin_add_nonneg; try easy.
  apply quadrant_1_sin_sub_nonneg_cos_le; try easy.
  apply rngl_sin_add_nonneg; try easy.
  rewrite angle_sub_sub_distr.
  rewrite (angle_add_comm θ1).
  rewrite angle_add_sub.
  now apply rngl_sin_add_nonneg.
}
apply (rngl_nle_gt_iff Hor) in Hc1z.
apply (rngl_lt_le_incl Hor) in Hc1z.
change_angle_sub_r θ1 angle_right.
progress sin_cos_add_sub_right_hyp T Hzs13.
progress sin_cos_add_sub_right_hyp T Hc1z.
progress sin_cos_add_sub_right_hyp T Hzs1.
progress sin_cos_add_sub_right_goal T.
change_angle_sub_l θ2 angle_right.
progress sin_cos_add_sub_right_hyp T Hzs2.
progress sin_cos_add_sub_right_hyp T Hc2z.
progress sin_cos_add_sub_right_goal T.
apply (rngl_le_0_sub Hop Hor).
destruct (rngl_le_dec Hor (rngl_cos θ2) (rngl_cos θ3)) as [Hc23| Hc32]. {
  cbn.
  rewrite (rngl_mul_opp_r Hop).
  rewrite (rngl_sub_add_distr Hos).
  rewrite (rngl_sub_opp_r Hop).
  rewrite (rngl_add_sub_swap Hop).
  rewrite <- (rngl_mul_sub_distr_l Hop).
  apply (rngl_le_0_add Hos Hor). {
    apply (rngl_le_0_add Hos Hor). {
      apply (rngl_mul_nonneg_nonneg Hon Hos Hiq Hor); [ easy | ].
      now apply (rngl_le_0_sub Hop Hor).
    }
    now apply (rngl_mul_nonneg_nonneg Hon Hos Hiq Hor).
  }
  now apply (rngl_mul_nonneg_nonneg Hon Hos Hiq Hor).
}
apply (rngl_nle_gt_iff Hor) in Hc32.
apply (rngl_le_0_sub Hop Hor).
apply rngl_sin_sub_nonneg_sin_le_sin; try easy.
apply rngl_sin_add_nonneg; try easy.
rewrite angle_sub_sub_distr.
rewrite (angle_add_comm θ1).
rewrite angle_add_sub.
now apply rngl_sin_add_nonneg.
Qed.

End a.
