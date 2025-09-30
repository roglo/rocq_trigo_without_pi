Set Nested Proofs Allowed.
From Stdlib Require Import Utf8 Arith.

Require Import RingLike.Core.
Require Import AngleDef Angle TrigoWithoutPiExt.
Require Import AngleAddOverflowLe.
Require Import AngleAddOverflowEquiv.
Require Import Order.
Require Import TacChangeAngle.

Section a.

Context {T : Type}.
Context {ro : ring_like_op T}.
Context {rp : ring_like_prop T}.
Context {ac : angle_ctx T}.

Theorem angle_add_le_mono_l_lemma_11 :
  ∀ θ1 θ2,
  (rngl_sin θ2 < 0)%L
  → (rngl_cos θ2 < 0)%L
  → (0 ≤ rngl_sin (θ1 + θ2))%L
  → angle_add_overflow θ1 θ2 = true.
Proof.
destruct_ac.
destruct (Nat.eq_dec (rngl_characteristic T) 1) as [Hc1| Hc1]. {
  specialize (rngl_characteristic_1 Hon Hos Hc1) as H1.
  intros * Hzs2 Hc2z Hzs12.
  rewrite (H1 (rngl_sin _)) in Hzs2.
  now apply (rngl_lt_irrefl Hor) in Hzs2.
}
intros * Hzs2 Hc2z Hzs12.
change_angle_add_r θ2 π.
progress sin_cos_add_sub_straight_hyp T Hzs12.
progress sin_cos_add_sub_straight_hyp T Hc2z.
progress sin_cos_add_sub_straight_hyp T Hzs2.
destruct (rngl_leb_dec 0 (rngl_cos θ1))%L as [Hzc1| Hc1z]. {
  apply rngl_leb_le in Hzc1.
  apply rngl_nlt_ge in Hzs12.
  apply Bool.not_false_iff_true.
  intros Haov12.
  apply Hzs12; clear Hzs12.
  destruct (rngl_ltb_dec 0 (rngl_sin θ1))%L as [Hzs1| Hs1z]. {
    apply rngl_ltb_lt in Hzs1.
    apply (rngl_lt_le_incl Hor) in Hzs2.
    now apply rngl_sin_add_pos_2.
  }
  apply (rngl_ltb_ge_iff Hor) in Hs1z.
  apply (rngl_nle_gt_iff Hor).
  intros Hzs12.
  change_angle_add_r θ1 π/₂.
  progress sin_cos_add_sub_right_hyp T Hzc1.
  progress sin_cos_add_sub_right_hyp T Hzs12.
  progress sin_cos_add_sub_right_hyp T Hs1z.
  clear - Haov12 ac Hos Hop Hiq Hs1z Hor Hzc1 Hzs2 Hc2z Hzs12 Hon Hc1.
  rewrite <- angle_add_overflow_equiv2 in Haov12.
  progress unfold angle_add_overflow2 in Haov12.
  apply Bool.not_true_iff_false in Haov12.
  apply Haov12; clear Haov12.
  rewrite angle_add_sub_assoc.
  rewrite <- angle_add_sub_swap.
  progress unfold angle_ltb.
  rewrite rngl_sin_sub_straight_r.
  rewrite rngl_sin_sub_right_r.
  rewrite (rngl_opp_involutive Hop).
  rewrite rngl_sin_sub_right_r.
  generalize Hs1z; intros H.
  apply (rngl_lt_eq_cases Hor) in H.
  destruct H as [H| H]. {
    apply (rngl_opp_lt_compat Hop Hor) in H.
    rewrite (rngl_opp_0 Hop) in H.
    apply (rngl_leb_gt_iff Hor) in H.
    rewrite H; clear H.
    rewrite rngl_cos_sub_straight_r.
    do 2 rewrite rngl_cos_sub_right_r.
    destruct (0 ≤? rngl_cos _)%L; [ easy | ].
    apply rngl_ltb_lt.
    apply (rngl_lt_opp_l Hop Hor).
    apply (rngl_lt_0_add Hor); [ | easy ].
    apply (rngl_le_neq Hor).
    split. {
      apply (rngl_lt_le_incl Hor) in Hzs2, Hc2z.
      now apply rngl_sin_add_nonneg.
    }
    intros H; symmetry in H.
    apply (eq_rngl_sin_0) in H.
    destruct H as [H| H]. {
      apply angle_add_move_l in H.
      rewrite angle_sub_0_l in H.
      subst θ2.
      cbn in Hzs2.
      apply (rngl_opp_pos_neg Hop Hor) in Hzs2.
      now apply rngl_nle_gt in Hzs2.
    }
    apply angle_add_move_l in H.
    subst θ2.
    rewrite rngl_cos_sub_straight_l in Hc2z.
    apply (rngl_opp_pos_neg Hop Hor) in Hc2z.
    now apply rngl_nle_gt in Hc2z.
  }
  exfalso.
  symmetry in H.
  apply (eq_rngl_cos_0) in H.
  destruct H; subst θ1. {
    rewrite rngl_cos_add_right_l in Hzs12.
    apply (rngl_opp_nonneg_nonpos Hop Hor) in Hzs12.
    now apply rngl_nlt_ge in Hzs12.
  }
  apply rngl_nlt_ge in Hzc1.
  apply Hzc1.
  apply (rngl_opp_1_lt_0 Hon Hop Hor Hc1).
}
apply (rngl_leb_gt_iff Hor) in Hc1z.
destruct (rngl_ltb_dec (rngl_sin θ1) 0)%L as [Hs1z| Hzs1]. 2: {
  apply (rngl_ltb_ge_iff Hor) in Hzs1.
  change_angle_sub_r θ1 π/₂.
  progress sin_cos_add_sub_right_hyp T Hzs12.
  progress sin_cos_add_sub_right_hyp T Hzs1.
  progress sin_cos_add_sub_right_hyp T Hc1z.
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
  rewrite rngl_cos_add_right_r.
  rewrite rngl_cos_sub_right_r.
  apply rngl_ltb_lt.
  apply (rngl_lt_le_trans Hor _ 0); [ now apply (rngl_opp_neg_pos Hop Hor) | ].
  apply (rngl_lt_le_incl Hor) in Hc1z, Hzs2, Hc2z.
  now apply rngl_sin_add_nonneg.
}
apply rngl_ltb_lt in Hs1z.
apply rngl_nlt_ge in Hzs12.
apply Bool.not_false_iff_true.
intros Haov12.
apply Hzs12; clear Hzs12.
apply (rngl_nle_gt_iff Hor).
intros Hzs12.
change_angle_add_r θ1 π.
progress sin_cos_add_sub_straight_hyp T Hzs12.
progress sin_cos_add_sub_straight_hyp T Hs1z.
progress sin_cos_add_sub_straight_hyp T Hc1z.
apply Bool.not_true_iff_false in Haov12.
apply Haov12; clear Haov12.
rewrite <- angle_add_overflow_equiv2.
progress unfold angle_add_overflow2.
rewrite angle_add_sub_assoc.
rewrite <- angle_add_sub_swap.
rewrite <- angle_sub_add_distr.
rewrite angle_straight_add_straight.
rewrite angle_sub_0_r.
progress unfold angle_ltb.
rewrite rngl_sin_sub_straight_r.
generalize Hs1z; intros H.
apply (rngl_opp_lt_compat Hop Hor) in H.
rewrite (rngl_opp_0 Hop) in H.
apply rngl_nle_gt in H.
apply rngl_leb_nle in H.
rewrite H; clear H.
rewrite rngl_cos_sub_straight_r.
apply rngl_leb_le in Hzs12.
now rewrite Hzs12.
Qed.

Theorem angle_lt_rngl_cos_add_pos :
  ∀ θ1 θ2,
  (θ2 < π/₂ - θ1)%A ∨ (- π/₂ - θ1 < θ2)%A
  → (0 < rngl_cos θ1)%L
  → (0 < rngl_cos (θ1 + θ2))%L.
Proof.
destruct_ac.
intros * H21 Hs1z.
apply (rngl_nle_gt_iff Hor).
intros Hzs12.
destruct H21 as [H21| H21]. {
  apply angle_nle_gt in H21.
  apply H21; clear H21.
  progress unfold angle_leb.
  rewrite rngl_sin_sub_right_l.
  generalize Hs1z; intros H.
  apply (rngl_lt_le_incl Hor) in H.
  apply rngl_leb_le in H; rewrite H; clear H.
  remember (0 ≤? rngl_sin θ2)%L as zs2 eqn:Hzs2.
  symmetry in Hzs2.
  destruct zs2; [ | easy ].
  apply rngl_leb_le in Hzs2.
  apply rngl_leb_le.
  rewrite rngl_cos_sub_right_l.
  rewrite rngl_cos_add in Hzs12.
  apply -> (rngl_le_sub_0 Hop Hor) in Hzs12.
  destruct (rngl_leb_dec 0 (rngl_sin θ1)) as [Hzs1| Hzs1]. {
    apply rngl_leb_le in Hzs1.
    apply (rngl_mul_le_mono_nonneg_l Hop Hor (rngl_cos θ1)) in Hzs12. 2: {
      now apply (rngl_lt_le_incl Hor) in Hs1z.
    }
    rewrite rngl_mul_assoc in Hzs12.
    rewrite fold_rngl_squ in Hzs12.
    specialize (cos2_sin2_1 θ1) as H.
    apply (rngl_add_move_r Hop) in H.
    rewrite H in Hzs12; clear H.
    rewrite (rngl_mul_sub_distr_r Hop) in Hzs12.
    rewrite (rngl_mul_1_l Hon) in Hzs12.
    apply (rngl_le_sub_le_add_r Hop Hor) in Hzs12.
    rewrite (rngl_mul_comm Hic) in Hzs12.
    progress unfold rngl_squ in Hzs12.
    do 2 rewrite <- rngl_mul_assoc in Hzs12.
    rewrite <- rngl_mul_add_distr_l in Hzs12.
    rewrite rngl_add_comm in Hzs12.
    rewrite (rngl_mul_comm Hic (rngl_sin θ2)) in Hzs12.
    rewrite <- rngl_sin_add in Hzs12.
    eapply (rngl_le_trans Hor); [ apply Hzs12 | ].
    rewrite <- (rngl_mul_1_r Hon (rngl_sin θ1)) at 2.
    apply (rngl_mul_le_mono_nonneg_l Hop Hor); [ easy | ].
    apply rngl_sin_bound.
  } {
    apply (rngl_leb_gt_iff Hor) in Hzs1.
    assert (Hc2z : (rngl_cos θ2 ≤ 0)%L). {
      apply (rngl_nlt_ge_iff Hor).
      intros Hzc2.
      apply rngl_nlt_ge in Hzs12.
      apply Hzs12; clear Hzs12.
      apply (rngl_le_lt_trans Hor _ 0). {
        apply (rngl_lt_le_incl Hor) in Hzs1.
        now apply (rngl_mul_nonpos_nonneg Hop Hor).
      }
      now apply (rngl_mul_pos_pos Hon Hop Hiq Hor).
    }
    apply (rngl_mul_le_mono_nonneg_r Hop Hor _ _ (rngl_sin θ2))
      in Hzs12; [ | easy ].
    do 2 rewrite <- rngl_mul_assoc in Hzs12.
    rewrite fold_rngl_squ in Hzs12.
    specialize (cos2_sin2_1 θ2) as H.
    apply (rngl_add_move_l Hop) in H.
    rewrite H in Hzs12; clear H.
    rewrite (rngl_mul_sub_distr_l Hop) in Hzs12.
    rewrite (rngl_mul_1_r Hon) in Hzs12.
    apply (rngl_le_add_le_sub_r Hop Hor) in Hzs12.
    progress unfold rngl_squ in Hzs12.
    do 2 rewrite (rngl_mul_comm Hic _ (_ * _)) in Hzs12.
    do 2 rewrite <- rngl_mul_assoc in Hzs12.
    rewrite <- rngl_mul_add_distr_l in Hzs12.
    rewrite <- rngl_sin_add in Hzs12.
    eapply (rngl_le_trans Hor); [ | apply Hzs12 ].
    rewrite <- (rngl_mul_1_r Hon (rngl_cos θ2)) at 1.
    apply (rngl_mul_le_mono_nonpos_l Hop Hor); [ easy | ].
    apply rngl_sin_bound.
  }
} {
  apply angle_nle_gt in H21.
  apply H21; clear H21.
  progress unfold angle_leb.
  rewrite <- angle_opp_add_distr.
  rewrite angle_add_comm.
  rewrite angle_opp_add_distr.
  rewrite rngl_sin_sub_right_r.
  cbn.
  rewrite (rngl_leb_0_opp Hop Hor).
  apply (rngl_leb_gt_iff Hor) in Hs1z.
  rewrite Hs1z.
  remember (0 ≤? rngl_sin θ2)%L as zs2 eqn:Hzs2.
  symmetry in Hzs2.
  destruct zs2; [ easy | ].
  apply rngl_leb_le.
  rewrite (rngl_mul_0_r Hos).
  rewrite (rngl_sub_0_l Hop).
  rewrite <- (rngl_mul_opp_r Hop).
  rewrite (rngl_opp_involutive Hop).
  rewrite (rngl_mul_1_r Hon).
  apply (rngl_leb_gt_iff Hor) in Hs1z, Hzs2.
  apply (rngl_le_opp_r Hop Hor).
  destruct (rngl_leb_dec 0 (rngl_cos θ2)) as [Hzc2| Hc2z]. {
    apply rngl_leb_le in Hzc2.
    change_angle_add_r θ2 π/₂.
    progress sin_cos_add_sub_right_hyp T Hzc2.
    progress sin_cos_add_sub_right_hyp T Hzs2.
    progress sin_cos_add_sub_right_hyp T Hzs12.
    progress sin_cos_add_sub_right_goal T.
    destruct (rngl_ltb_dec 0 (rngl_sin θ1)) as [Hzs1| Hc1z]. {
      apply rngl_ltb_lt in Hzs1.
      exfalso.
      apply rngl_nlt_ge in Hzs12.
      apply Hzs12; clear Hzs12.
      apply (rngl_lt_le_incl Hor) in Hs1z.
      now apply rngl_sin_add_pos_2.
    }
    apply (rngl_ltb_ge_iff Hor) in Hc1z.
    change_angle_opp θ1.
    progress sin_cos_opp_hyp T Hs1z.
    progress sin_cos_opp_hyp T Hc1z.
    rewrite angle_add_opp_l in Hzs12.
    rewrite rngl_sin_sub_anticomm in Hzs12.
    apply (rngl_opp_nonpos_nonneg Hop Hor) in Hc1z, Hzs12.
    cbn.
    rewrite (rngl_add_opp_r Hop).
    apply (rngl_le_sub_0 Hop Hor).
    apply (rngl_lt_le_incl Hor) in Hs1z.
    now apply rngl_sin_sub_nonneg_sin_le_sin.
  }
  apply (rngl_leb_gt_iff Hor) in Hc2z.
  change_angle_add_r θ2 π.
  progress sin_cos_add_sub_straight_hyp T Hc2z.
  progress sin_cos_add_sub_straight_hyp T Hzs2.
  progress sin_cos_add_sub_straight_hyp T Hzs12.
  progress sin_cos_add_sub_straight_goal T.
  rewrite (rngl_add_opp_l Hop).
  apply (rngl_le_sub_0 Hop Hor).
  destruct (rngl_leb_dec (rngl_sin θ1) 0) as [Hzs1| Hzs1]. {
    apply rngl_leb_le in Hzs1.
    apply (rngl_lt_le_incl Hor) in Hc2z.
    now apply (rngl_le_trans Hor _ 0).
  }
  apply (rngl_leb_gt_iff Hor) in Hzs1.
  change_angle_sub_l θ1 π/₂.
  progress sin_cos_add_sub_right_hyp T Hs1z.
  progress sin_cos_add_sub_right_hyp T Hzs1.
  progress sin_cos_add_sub_right_hyp T Hzs12.
  progress sin_cos_add_sub_right_goal T.
  apply (rngl_lt_le_incl Hor) in Hs1z, Hc2z, Hzs2, Hzs1.
  now apply quadrant_1_sin_sub_nonneg_cos_le.
}
Qed.

Theorem angle_lt_rngl_sin_add_nonneg_sin_nonneg :
  ∀ θ1 θ2,
  (θ2 < - θ1)%A ∨ (π - θ1 < θ2)%A
  → (0 ≤ rngl_sin (θ1 + θ2))%L
  → (0 ≤ rngl_sin θ1)%L.
Proof.
destruct_ac.
intros * H21 Hzs12.
apply (rngl_nlt_ge_iff Hor).
intros Hs1z.
change_angle_add_r θ1 π/₂.
progress sin_cos_add_sub_right_hyp T Hs1z.
progress sin_cos_add_sub_right_hyp T Hzs12.
apply rngl_nlt_ge in Hzs12.
apply Hzs12; clear Hzs12.
rewrite angle_opp_sub_distr in H21.
rewrite <- angle_opp_straight in H21.
rewrite <- angle_opp_add_distr in H21.
rewrite <- angle_add_sub_swap in H21.
rewrite <- angle_add_sub_assoc in H21.
rewrite angle_straight_sub_right in H21.
rewrite angle_opp_add_distr in H21.
now apply angle_lt_rngl_cos_add_pos.
Qed.

Theorem angle_add_overflow_if :
  ∀ θ1 θ2,
  angle_add_overflow θ1 θ2 = false
  → (θ1 = 0 ∨ θ2 < - θ1)%A.
Proof.
intros * Haov.
progress unfold angle_add_overflow in Haov.
remember (θ1 =? 0)%A as z1 eqn:Hz1.
symmetry in Hz1.
destruct z1; [ now left; apply angle_eqb_eq | right ].
now apply angle_leb_gt.
Qed.

Theorem rngl_sin_add_nonneg_sin_nonneg :
  ∀ θ1 θ2,
  angle_add_overflow θ1 θ2 = false
  → (0 ≤ rngl_sin (θ1 + θ2))%L
  → (0 ≤ rngl_sin θ1)%L.
Proof.
destruct_ac.
intros * Haov12 Hzs12.
apply angle_add_overflow_if in Haov12.
destruct Haov12 as [H| H]. {
  subst θ1.
  apply (rngl_le_refl Hor).
}
apply (angle_lt_rngl_sin_add_nonneg_sin_nonneg _ θ2); [ | easy ].
now left.
Qed.

Theorem angle_add_le_mono_l_lemma_1 :
  ∀ θ1 θ2 θ3,
  angle_add_overflow θ1 θ3 = false
  → (0 ≤ rngl_sin θ2)%L
  → (0 ≤ rngl_sin θ3)%L
  → (0 ≤ rngl_cos θ1)%L
  → (0 ≤ rngl_sin (θ1 + θ2))%L
  → (0 ≤ rngl_sin (θ1 + θ3))%L
  → (rngl_cos θ3 ≤ rngl_cos θ2)%L
  → (rngl_cos (θ1 + θ3) ≤ rngl_cos (θ1 + θ2))%L.
Proof.
destruct_ac.
intros * Haov13 Hzs2 Hzs3 Hzc1 Hzs12 Hzs13 H23.
generalize Hzs13; intros Hzs1.
apply rngl_sin_add_nonneg_sin_nonneg in Hzs1; [ | easy ].
apply angle_le_sub_le_add_l_lemma_1; try easy. {
  rewrite angle_add_comm.
  now rewrite angle_add_sub.
} {
  rewrite angle_add_comm.
  now rewrite angle_add_sub.
}
Qed.

Theorem angle_add_overflow_opp_r :
  ∀ θ, θ ≠ 0%A → angle_add_overflow θ (- θ) = true.
Proof.
intros * Htz.
progress unfold angle_add_overflow.
apply Bool.andb_true_iff.
split; [ | apply angle_le_refl ].
apply Bool.not_false_iff_true.
intros H1.
apply Htz; clear Htz.
apply Bool.negb_false_iff in H1.
now apply angle_eqb_eq in H1.
Qed.

Theorem angle_add_le_mono_l_lemma_3 :
  ∀ θ1 θ2 θ3,
  angle_add_overflow θ1 θ3 = false
  → (0 ≤ rngl_sin θ2)%L
  → (0 ≤ rngl_sin θ3)%L
  → (0 ≤ rngl_sin (θ1 + θ2))%L
  → (0 ≤ rngl_sin (θ1 + θ3))%L
  → (rngl_cos θ3 ≤ rngl_cos θ2)%L
  → (rngl_cos (θ1 + θ3) ≤ rngl_cos (θ1 + θ2))%L.
Proof.
destruct_ac.
intros * Haov13 Hzs2 Hzs3 Hzs12 Hzs13 H23.
destruct (rngl_leb_dec 0 (rngl_cos θ1))%L as [Hzc1| Hc1z]. {
  apply rngl_leb_le in Hzc1.
  move Hzc1 before Hzs3.
  now apply angle_add_le_mono_l_lemma_1.
}
apply (rngl_leb_gt_iff Hor) in Hc1z.
move Hc1z before Hzs3.
destruct (rngl_leb_dec 0 (rngl_sin θ1))%L as [Hzs1| Hs1z]. 2: {
  apply (rngl_leb_gt_iff Hor) in Hs1z.
  move Hs1z after Hzs2.
  change_angle_sub_r θ1 π.
  progress sin_cos_add_sub_straight_hyp T Hs1z.
  progress sin_cos_add_sub_straight_hyp T Hzs13.
  progress sin_cos_add_sub_straight_hyp T Hzs12.
  progress sin_cos_add_sub_straight_hyp T Hc1z.
  progress sin_cos_add_sub_straight_goal T.
  destruct (rngl_ltb_dec 0 (rngl_cos θ2))%L as [Hzc2| Hc2z]. {
    apply rngl_ltb_lt in Hzc2.
    move Hzc2 before Hc1z.
    exfalso.
    apply rngl_nlt_ge in Hzs12.
    apply Hzs12; clear Hzs12.
    apply (rngl_lt_le_incl Hor) in Hc1z.
    now apply rngl_sin_add_pos_2.
  }
  apply (rngl_ltb_ge_iff Hor) in Hc2z.
  change_angle_sub_r θ2 π/₂.
  progress sin_cos_add_sub_right_hyp T Hzs2.
  progress sin_cos_add_sub_right_hyp T Hzs12.
  progress sin_cos_add_sub_right_hyp T Hc2z.
  progress sin_cos_add_sub_right_hyp T H23.
  progress sin_cos_add_sub_right_goal T.
  destruct (rngl_ltb_dec 0 (rngl_cos θ3))%L as [Hzc3| Hc3z]. {
    apply rngl_ltb_lt in Hzc3.
    move Hzc3 before Hzs2.
    exfalso.
    apply rngl_nlt_ge in Hzs13.
    apply Hzs13; clear Hzs13.
    apply (rngl_lt_le_incl Hor) in Hc1z.
    now apply rngl_sin_add_pos_2.
  }
  apply (rngl_ltb_ge_iff Hor) in Hc3z.
  change_angle_sub_r θ3 π/₂.
  progress sin_cos_add_sub_right_hyp T Hzs13.
  progress sin_cos_add_sub_right_hyp T Hzs3.
  progress sin_cos_add_sub_right_hyp T Hc3z.
  progress sin_cos_add_sub_right_hyp T H23.
  progress sin_cos_add_sub_right_goal T.
  generalize H23; intros H32.
  apply rngl_cos_cos_sin_sin_nonneg_sin_le_cos_le_iff in H32; try easy.
  move H32 before H23.
  assert (Hs12z : (0 ≤ rngl_sin (θ1 + θ2))%L). {
    apply (rngl_lt_le_incl Hor) in Hs1z, Hc1z.
    now apply rngl_sin_add_nonneg.
  }
  assert (Hs13z : (0 ≤ rngl_sin (θ1 + θ3))%L). {
    apply (rngl_lt_le_incl Hor) in Hs1z, Hc1z.
    now apply rngl_sin_add_nonneg.
  }
  apply rngl_cos_cos_sin_sin_neg_sin_le_cos_le_iff; try easy.
  apply angle_add_le_mono_l_lemma_1; try easy; cycle 1.
  now apply (rngl_lt_le_incl Hor).
  clear - ac Hs13z Hc3z Hs1z.
  rewrite angle_add_overflow_comm.
  rewrite angle_add_comm in Hs13z.
  now apply rngl_sin_add_nonneg_angle_add_not_overflow; try easy.
}
apply rngl_leb_le in Hzs1.
change_angle_sub_r θ1 π/₂.
progress sin_cos_add_sub_right_hyp T Hzs1.
progress sin_cos_add_sub_right_hyp T Hzs13.
progress sin_cos_add_sub_right_hyp T Hzs12.
progress sin_cos_add_sub_right_hyp T Hc1z.
progress sin_cos_add_sub_right_goal T.
specialize rngl_sin_nonneg_cos_le_sin_le as H1.
specialize (H1 θ3 θ2 Hzs3 Hzs2 H23).
destruct (rngl_leb_dec 0 (rngl_cos θ3))%L as [Hzc3| Hc3z]. {
  rewrite Hzc3 in H1.
  apply rngl_leb_le in Hzc3.
  rename H1 into Hs23.
  destruct (rngl_ltb_dec (rngl_cos θ2) 0)%L as [Hc2z| Hzc2]. {
    apply rngl_ltb_lt in Hc2z.
    apply rngl_nle_gt in Hc2z.
    exfalso; apply Hc2z; clear Hc2z.
    eapply (rngl_le_trans Hor); [ apply Hzc3 | easy ].
  }
  apply (rngl_ltb_ge_iff Hor) in Hzc2.
  move Hzc2 before Hzs1.
  rename Hzs12 into Hzc12; rename Hzs13 into Hzc13.
  assert (Hzs12 : (0 ≤ rngl_sin (θ1 + θ2))%L). {
    apply (rngl_lt_le_incl Hor) in Hc1z.
    now apply rngl_sin_add_nonneg.
  }
  assert (Hzs13 : (0 ≤ rngl_sin (θ1 + θ3))%L). {
    apply (rngl_lt_le_incl Hor) in Hc1z.
    now apply rngl_sin_add_nonneg.
  }
  specialize rngl_cos_cos_sin_sin_nonneg_sin_le_cos_le_iff as H1.
  apply H1; try easy.
  clear H1.
  apply angle_add_le_mono_l_lemma_1; try easy.
  rewrite angle_add_overflow_comm.
  rewrite angle_add_comm in Hzs13.
  now apply rngl_sin_add_nonneg_angle_add_not_overflow.
}
rewrite Hc3z in H1.
apply (rngl_leb_gt_iff Hor) in Hc3z.
apply rngl_nlt_ge in Hzs13.
exfalso; apply Hzs13; clear Hzs13.
apply (rngl_le_neq Hor).
split. {
  cbn.
  apply (rngl_le_sub_0 Hop Hor).
  apply (rngl_le_trans Hor _ 0).
  apply (rngl_mul_nonneg_nonpos Hop Hor); [ easy | ].
  now apply (rngl_lt_le_incl Hor).
  apply (rngl_mul_nonneg_nonneg Hos Hor); [ | easy ].
  now apply (rngl_lt_le_incl Hor).
}
intros Hc13.
apply (eq_rngl_cos_0) in Hc13.
destruct Hc13 as [Hc13| Hc13]. {
  apply angle_add_move_l in Hc13.
  subst θ3.
  apply rngl_nle_gt in Hc3z.
  apply Hc3z.
  rewrite rngl_cos_sub_right_l.
  now apply (rngl_lt_le_incl Hor).
}
apply angle_add_move_l in Hc13.
subst θ3.
rewrite <- angle_opp_add_distr in Haov13.
apply Bool.not_true_iff_false in Haov13.
apply Haov13; clear Haov13.
apply angle_add_overflow_opp_r.
intros H.
apply angle_add_move_0_r in H; subst θ1.
apply rngl_nle_gt in Hc1z.
apply Hc1z; cbn.
apply (rngl_opp_1_le_0 Hon Hop Hor).
Qed.

End a.
