Set Nested Proofs Allowed.
From Stdlib Require Import Utf8 Arith.

Require Import RingLike.Core.
Require Import RingLike.RealLike.
Require Import RingLike.Misc.
Require Import Angle AngleDef.
Require Import Order.
Require Import AngleAddOverflowEquiv.
Require Import Distance.
Require Import TacChangeAngle.

Section a.

Context {T : Type}.
Context {ro : ring_like_op T}.
Context {rp : ring_like_prop T}.
Context {ac : angle_ctx T}.

(* *)

Theorem rngl_cos_add_nonneg :
  ∀ θ1 θ2,
  (rngl_sin θ1 < 0)%L
  → (0 ≤ rngl_sin θ2)%L
  → (0 ≤ rngl_cos θ1)%L
  → (0 ≤ rngl_cos θ2)%L
  → (0 ≤ rngl_cos (θ1 + θ2))%L.
Proof.
destruct_ac.
intros * Hs1z Hzs2 Hzc1 Hzc2.
change_angle_add_r θ1 π/₂.
progress sin_cos_add_sub_right_hyp T Hs1z.
progress sin_cos_add_sub_right_hyp T Hzc1.
progress sin_cos_add_sub_right_goal T.
apply (rngl_lt_le_incl Hor) in Hs1z.
now apply rngl_sin_add_nonneg.
Qed.

Theorem rngl_sin_add_nonneg_angle_add_not_overflow :
  ∀ θ1 θ2,
  (0 ≤ rngl_sin θ1)%L
  → (0 < rngl_sin θ2)%L
  → (0 ≤ rngl_sin (θ1 + θ2))%L
  → angle_add_overflow θ1 θ2 = false.
Proof.
destruct_ac.
intros * Hzs1 Hzs2 Hzs3.
apply Bool.not_true_iff_false.
intros Haov.
apply rngl_nle_gt in Hzs2.
apply Hzs2; clear Hzs2.
rewrite <- angle_add_overflow_equiv2 in Haov.
progress unfold angle_add_overflow2 in Haov.
apply angle_leb_gt in Haov.
remember (θ1 + θ2)%A as θ3 eqn:Hθ3.
apply (rngl_nlt_ge_iff Hor).
intros Hzs2.
progress unfold angle_leb in Haov.
apply rngl_leb_le in Hzs1.
rewrite Hzs1 in Haov.
apply rngl_leb_le in Hzs1.
apply rngl_leb_le in Hzs3.
rewrite Hzs3 in Haov.
apply rngl_leb_le in Hzs3.
apply (rngl_leb_gt_iff Hor) in Haov.
apply rngl_nle_gt in Hzs2.
apply Hzs2; clear Hzs2.
symmetry in Hθ3.
apply angle_add_move_l in Hθ3.
subst θ2.
rewrite rngl_sin_sub_anticomm.
apply (rngl_opp_nonpos_nonneg Hop Hor).
apply rngl_sin_sub_nonneg; [ easy | easy | ].
now apply (rngl_lt_le_incl Hor).
Qed.

Theorem rngl_sin_add_nonneg_angle_add_not_overflow_sin_nonneg :
  ∀ θ1 θ2,
  (0 ≤ rngl_sin θ1)%L
  → (0 ≤ rngl_sin (θ1 + θ2))%L
  → angle_add_overflow θ1 θ2 = false
  → (0 ≤ rngl_sin θ2)%L.
Proof.
destruct_ac.
intros * Hzs1 Hzs3 Haov.
rewrite <- angle_add_overflow_equiv2 in Haov.
progress unfold angle_add_overflow2 in Haov.
remember (θ1 + θ2)%A as θ3 eqn:Hθ3.
apply (rngl_nlt_ge_iff Hor).
intros Hzs2.
progress unfold angle_ltb in Haov.
cbn in Haov.
apply rngl_leb_le in Hzs1.
rewrite Hzs1 in Haov.
apply rngl_leb_le in Hzs1.
apply rngl_leb_le in Hzs3.
rewrite Hzs3 in Haov.
apply rngl_leb_le in Hzs3.
apply (rngl_ltb_ge_iff Hor) in Haov.
apply rngl_nle_gt in Hzs2.
apply Hzs2; clear Hzs2.
symmetry in Hθ3.
apply angle_add_move_l in Hθ3.
subst θ2.
now apply rngl_sin_sub_nonneg.
Qed.

Theorem rngl_sin_nonneg_add_nonneg :
  ∀ θ1 θ2,
  (0 ≤ rngl_sin θ1)%L
  → (0 ≤ rngl_sin (θ1 + θ2))%L
  → if angle_add_overflow θ1 θ2 then (rngl_sin θ2 ≤ 0)%L
     else (0 ≤ rngl_sin θ2)%L.
Proof.
destruct_ac.
destruct (Nat.eq_dec (rngl_characteristic T) 1) as [Hc1| Hc1]. {
  specialize (rngl_characteristic_1_angle_0 Hc1) as H1.
  intros * Hzs1 Hzs3.
  rewrite (H1 θ1), (H1 θ2).
  rewrite angle_add_overflow_0_l.
  apply (rngl_le_refl Hor).
}
intros * Hzs1 Hzs3.
remember (angle_add_overflow θ1 θ2) as aov eqn:Haov.
symmetry in Haov.
destruct aov. {
  apply (rngl_nlt_ge_iff Hor).
  intros Hzs2.
  apply Bool.not_false_iff_true in Haov.
  apply Haov; clear Haov.
  now apply rngl_sin_add_nonneg_angle_add_not_overflow.
} {
  now apply (rngl_sin_add_nonneg_angle_add_not_overflow_sin_nonneg θ1).
}
Qed.

(* *)

Theorem angle_le_sub_le_add_l_lemma_1 :
  ∀ θ1 θ2 θ3,
  (0 ≤ rngl_sin θ1)%L
  → (0 ≤ rngl_sin θ2)%L
  → (0 ≤ rngl_sin θ3)%L
  → (0 ≤ rngl_cos θ2)%L
  → (rngl_cos θ3 ≤ rngl_cos (θ1 - θ2))%L
  → (0 ≤ rngl_sin (θ1 - θ2))%L
  → (0 ≤ rngl_sin (θ2 + θ3))%L
  → (rngl_cos (θ2 + θ3) ≤ rngl_cos θ1)%L.
Proof.
(* thanks Geoffroy *)
destruct_ac.
destruct (Nat.eq_dec (rngl_characteristic T) 1) as [Hc1| Hc1]. {
  specialize (rngl_characteristic_1 Hon Hos Hc1) as H1.
  intros.
  rewrite H1, (H1 (rngl_cos _)).
  apply (rngl_le_refl Hor).
}
intros * Hzs1 Hzs2 Hzs3 Hzc2 Hc123 Hzs12 Hzs23.
destruct (rngl_leb_dec 0 (rngl_cos θ3))%L as [Hzc3| Hc3z]. {
  apply rngl_leb_le in Hzc3.
  move Hzc3 before Hzs3.
  generalize Hc123; intros Hc123v.
  cbn in Hc123 |-*.
  rewrite (rngl_mul_opp_r Hop) in Hc123.
  rewrite (rngl_sub_opp_r Hop) in Hc123.
  apply (rngl_le_sub_le_add_r Hop Hor).
  apply (rngl_mul_le_mono_nonneg_l Hon Hop Hiq Hor (rngl_cos θ2)) in Hc123;
    [ | easy ].
  rewrite rngl_mul_add_distr_l in Hc123.
  rewrite (rngl_mul_comm Hic _ (_ * _))%L in Hc123.
  rewrite <- rngl_mul_assoc in Hc123.
  rewrite fold_rngl_squ in Hc123.
  specialize (cos2_sin2_1 θ2) as H1.
  apply (rngl_add_move_r Hop) in H1.
  rewrite H1 in Hc123; clear H1.
  rewrite (rngl_mul_sub_distr_l Hop) in Hc123.
  rewrite (rngl_mul_1_r Hon) in Hc123.
  eapply (rngl_le_trans Hor); [ apply Hc123 | ].
  rewrite <- (rngl_add_sub_swap Hop).
  rewrite <- (rngl_add_sub_assoc Hop).
  apply (rngl_add_le_mono_l Hos Hor).
  progress unfold rngl_squ.
  do 2 rewrite rngl_mul_assoc.
  rewrite <- (rngl_mul_sub_distr_r Hop).
  rewrite (rngl_mul_comm Hic _ (rngl_sin θ2)).
  apply (rngl_mul_le_mono_nonneg_l Hon Hop Hiq Hor); [ easy | ].
  rewrite (rngl_mul_comm Hic (rngl_cos θ2)).
  rewrite <- rngl_sin_sub.
  specialize rngl_cos_cos_sin_sin_nonneg_sin_le_cos_le_iff as H1.
  assert (H : (0 ≤ rngl_cos (θ1 - θ2))%L). {
    now apply (rngl_le_trans Hor _ (rngl_cos θ3)).
  }
  now apply (H1 _ _ Hzs12 Hzs3 H Hzc3).
}
apply (rngl_leb_gt_iff Hor) in Hc3z.
change_angle_sub_r θ3 π/₂.
progress sin_cos_add_sub_right_hyp T Hzs3.
progress sin_cos_add_sub_right_hyp T Hc123.
progress sin_cos_add_sub_right_hyp T Hc3z.
progress sin_cos_add_sub_right_hyp T Hzs23.
progress sin_cos_add_sub_right_goal T.
destruct (rngl_leb_dec 0 (rngl_cos θ1))%L as [Hzc1| Hc1z]. {
  apply rngl_leb_le in Hzc1.
  move Hzc1 before Hc3z.
  apply (rngl_le_0_add Hos Hor); [ | easy ].
  apply (rngl_lt_le_incl Hor) in Hc3z.
  now apply (rngl_sin_add_nonneg).
}
apply (rngl_leb_gt_iff Hor) in Hc1z.
change_angle_sub_r θ1 π/₂.
progress sin_cos_add_sub_right_hyp T Hzs1.
progress sin_cos_add_sub_right_hyp T Hzs12.
progress sin_cos_add_sub_right_hyp T Hc123.
progress sin_cos_add_sub_right_hyp T Hc1z.
progress sin_cos_add_sub_right_goal T.
destruct (rngl_eqb_dec (rngl_cos θ2) 0) as [Hc2z| Hc2z]. {
  apply (rngl_eqb_eq Heo) in Hc2z.
  exfalso.
  cbn in Hc123.
  rewrite (rngl_mul_opp_r Hop) in Hc123.
  rewrite (rngl_add_opp_r Hop) in Hc123.
  apply (rngl_le_sub_le_add_r Hop Hor) in Hc123.
  apply rngl_nlt_ge in Hzs23.
  apply Hzs23; clear Hzs23; cbn.
  rewrite Hc2z.
  rewrite (rngl_mul_0_l Hos).
  rewrite (rngl_sub_0_l Hop).
  apply (rngl_opp_neg_pos Hop Hor).
  apply (rngl_mul_pos_pos Hon Hop Hiq Hor); [ | easy ].
  apply eq_rngl_cos_0 in Hc2z.
  destruct Hc2z; subst θ2. {
    apply (rngl_0_lt_1 Hon Hos Hiq Hc1 Hor).
  }
  rewrite angle_sub_opp_r in Hzs12.
  rewrite rngl_cos_add_right_r in Hzs12.
  apply (rngl_opp_nonneg_nonpos Hop Hor) in Hzs12.
  now apply rngl_nlt_ge in Hzs12.
}
apply (rngl_eqb_neq Heo) in Hc2z.
rename Hc123 into Hs123.
destruct (rngl_leb_dec (rngl_cos θ1) (rngl_cos (θ2 + θ3)))
    as [Hc123| Hc231]. {
  apply rngl_leb_le in Hc123.
  apply (rngl_mul_le_mono_pos_r Hon Hop Hiq Hor _ _ (rngl_cos θ2)). {
    apply not_eq_sym in Hc2z.
    now apply (rngl_le_neq Hor).
  }
  cbn in Hs123 |-*.
  rewrite (rngl_mul_opp_r Hop) in Hs123.
  rewrite (rngl_add_opp_r Hop) in Hs123.
  apply (rngl_le_sub_le_add_l Hop Hor) in Hs123.
  rewrite rngl_mul_add_distr_r.
  rewrite rngl_add_comm.
  rewrite (rngl_mul_mul_swap Hic).
  rewrite fold_rngl_squ.
  specialize (cos2_sin2_1 θ2) as H1.
  apply (rngl_add_move_r Hop) in H1.
  rewrite H1; clear H1.
  rewrite (rngl_mul_sub_distr_r Hop).
  rewrite (rngl_mul_1_l Hon).
  rewrite <- (rngl_add_sub_swap Hop).
  rewrite <- (rngl_add_sub_assoc Hop).
  apply (rngl_le_sub_le_add_l Hop Hor).
  apply (rngl_le_sub_le_add_r Hop Hor) in Hs123.
  eapply (rngl_le_trans Hor); [ apply Hs123 | ].
  progress unfold rngl_squ.
  do 2 rewrite <- rngl_mul_assoc.
  rewrite <- (rngl_mul_sub_distr_l Hop).
  rewrite (rngl_mul_comm Hic (rngl_cos θ3)).
  rewrite <- rngl_cos_add.
  rewrite (rngl_mul_comm Hic).
  now apply (rngl_mul_le_mono_nonneg_l Hon Hop Hiq Hor).
}
apply (rngl_leb_gt_iff Hor) in Hc231.
move Hc231 before Hs123.
specialize rngl_cos_cos_sin_sin_nonneg_sin_le_cos_le_iff as H1.
apply (rngl_lt_le_incl Hor) in Hc1z, Hc231.
apply H1; try easy.
cbn.
apply (rngl_le_0_add Hos Hor). {
  now apply (rngl_mul_nonneg_nonneg Hon Hos Hiq Hor).
} {
  apply (rngl_lt_le_incl Hor) in Hc3z.
  now apply (rngl_mul_nonneg_nonneg Hon Hos Hiq Hor).
}
Qed.

Theorem rngl_cos_le_cos_add :
  ∀ θ1 θ2,
  (rngl_sin θ1 ≤ 0)%L
  → (0 ≤ rngl_sin θ2)%L
  → (rngl_sin (θ1 + θ2) < 0)%L
  → (rngl_cos θ1 ≤ rngl_cos (θ1 + θ2))%L.
Proof.
destruct_ac.
intros * Hzs1 Hzs2 Hzs12.
destruct (rngl_leb_dec 0 (rngl_cos θ1)) as [Hzc1| Hc1z]. {
  apply rngl_leb_le in Hzc1.
  change_angle_add_r θ1 π/₂.
  progress sin_cos_add_sub_right_hyp T Hzs1.
  progress sin_cos_add_sub_right_hyp T Hzc1.
  progress sin_cos_add_sub_right_hyp T Hzs12.
  progress sin_cos_add_sub_right_goal T.
  destruct (rngl_leb_dec 0 (rngl_cos θ2)) as [Hzc2| Hc2z]. {
    apply rngl_leb_le in Hzc2.
    move Hzc2 before Hzc1.
    assert (Hzc12 : (0 ≤ rngl_sin (θ1 + θ2))%L). {
      cbn.
      apply (rngl_le_0_add Hos Hor).
      now apply (rngl_mul_nonneg_nonneg Hon Hos Hiq Hor).
      now apply (rngl_mul_nonneg_nonneg Hon Hos Hiq Hor).
    }
    apply rngl_cos_cos_sin_sin_nonneg_sin_le_cos_le_iff; try easy.
    now apply (rngl_lt_le_incl Hor).
    apply angle_le_sub_le_add_l_lemma_1; try easy.
    rewrite angle_sub_diag.
    apply rngl_cos_bound.
    rewrite angle_sub_diag.
    apply (rngl_le_refl Hor).
  }
  apply (rngl_leb_gt_iff Hor) in Hc2z.
  exfalso.
  change_angle_sub_r θ2 π/₂.
  progress sin_cos_add_sub_right_hyp T Hzs2.
  progress sin_cos_add_sub_right_hyp T Hc2z.
  progress sin_cos_add_sub_right_hyp T Hzs12.
  apply rngl_nle_gt in Hzs12.
  apply Hzs12; clear Hzs12; cbn.
  apply (rngl_le_0_add Hos Hor).
  now apply (rngl_mul_nonneg_nonneg Hon Hos Hiq Hor).
  apply (rngl_mul_nonneg_nonneg Hon Hos Hiq Hor); [ easy | ].
  now apply (rngl_lt_le_incl Hor).
}
apply (rngl_leb_gt_iff Hor) in Hc1z.
change_angle_sub_r θ1 π.
progress sin_cos_add_sub_straight_hyp T Hzs1.
progress sin_cos_add_sub_straight_hyp T Hc1z.
progress sin_cos_add_sub_straight_hyp T Hzs12.
progress sin_cos_add_sub_straight_goal T.
apply (rngl_lt_le_incl Hor) in Hc1z, Hzs12.
apply rngl_cos_add_le_cos; try easy.
now right; right; left.
Qed.

Theorem angle_add_overflow_le_lemma_2 :
  ∀ θ1 θ2,
  rngl_cos θ1 ≠ (-1)%L
  → (0 ≤ rngl_sin θ1)%L
  → (0 ≤ rngl_sin θ2)%L
  → (rngl_cos θ1 ≤ 0)%L
  → (0 ≤ rngl_sin (θ1 + θ2))%L
  → (rngl_cos (θ1 + θ2) ≤ rngl_cos θ1)%L.
Proof.
destruct_ac.
destruct (Nat.eq_dec (rngl_characteristic T) 1) as [Hc1| Hc1]. {
  specialize (rngl_characteristic_1 Hon Hos Hc1) as H1.
  intros * Hco1 Hzs1 Hzs2 Hc1z Hzs12.
  do 2 rewrite (H1 (rngl_cos _)).
  apply (rngl_le_refl Hor).
}
intros * Hco1 Hzs1 Hzs2 Hc1z Hzs12.
change_angle_sub_r θ1 π/₂.
progress sin_cos_add_sub_right_hyp T Hzs1.
progress sin_cos_add_sub_right_hyp T Hco1.
progress sin_cos_add_sub_right_hyp T Hzs12.
progress sin_cos_add_sub_right_hyp T Hc1z.
progress sin_cos_add_sub_right_goal T.
destruct (rngl_leb_dec (rngl_cos θ2) 0) as [Hc2z| Hzc2]. {
  apply rngl_leb_le in Hc2z.
  change_angle_sub_r θ2 π/₂.
  progress sin_cos_add_sub_right_hyp T Hzs12.
  progress sin_cos_add_sub_right_hyp T Hzs2.
  progress sin_cos_add_sub_right_hyp T Hc2z.
  progress sin_cos_add_sub_right_goal T.
  apply (rngl_nlt_ge_iff Hor).
  intros Hc12.
  apply rngl_nlt_ge in Hzs12.
  apply Hzs12; clear Hzs12.
  apply (rngl_le_neq Hor).
  split. {
    cbn.
    apply (rngl_le_0_add Hos Hor).
    now apply (rngl_mul_nonneg_nonneg Hon Hos Hiq Hor).
    now apply (rngl_mul_nonneg_nonneg Hon Hos Hiq Hor).
  }
  intros H; symmetry in H.
  apply eq_rngl_sin_0 in H.
  destruct H as [H| H]. {
    rewrite H in Hc12.
    apply rngl_nle_gt in Hc12.
    apply Hc12; clear Hc12; cbn.
    apply rngl_sin_bound.
  }
  apply angle_add_move_l in H.
  subst θ2.
  clear Hc12 Hc2z.
  rewrite rngl_cos_sub_straight_l in Hzs2.
  apply (rngl_opp_nonneg_nonpos Hop Hor) in Hzs2.
  apply (rngl_le_antisymm Hor) in Hzs2; [ | easy ].
  symmetry in Hzs2.
  apply eq_rngl_cos_0 in Hzs2.
  destruct Hzs2; subst θ1; [ easy | ].
  apply rngl_nlt_ge in Hc1z.
  apply Hc1z; clear Hc1z.
  apply (rngl_opp_1_lt_0 Hon Hop Hiq Hor Hc1).
}
apply (rngl_leb_gt_iff Hor) in Hzc2.
move Hzc2 before Hzs1.
apply rngl_cos_cos_sin_sin_nonneg_sin_le_cos_le_iff; try easy. {
  cbn.
  apply (rngl_le_0_add Hos Hor).
  apply (rngl_mul_nonneg_nonneg Hon Hos Hiq Hor); [ easy | ].
  now apply (rngl_lt_le_incl Hor).
  now apply (rngl_mul_nonneg_nonneg Hon Hos Hiq Hor).
}
apply angle_le_sub_le_add_l_lemma_1; try easy. {
  rewrite angle_sub_diag.
  apply rngl_cos_bound.
} {
  rewrite angle_sub_diag.
  apply (rngl_le_refl Hor).
}
cbn.
apply (rngl_le_0_add Hos Hor).
apply (rngl_mul_nonneg_nonneg Hon Hos Hiq Hor); [ easy | ].
now apply (rngl_lt_le_incl Hor).
now apply (rngl_mul_nonneg_nonneg Hon Hos Hiq Hor).
Qed.

Theorem angle_add_overflow_le_lemma_5 :
  ∀ θ1 θ2,
  rngl_cos θ1 ≠ 1%L
  → (0 ≤ rngl_sin θ1)%L
  → (rngl_sin θ2 < 0)%L
  → (0 < rngl_cos θ1)%L
  → (0 ≤ rngl_sin (θ1 + θ2))%L
  → (rngl_cos (θ1 + θ2) ≤ rngl_cos θ1)%L
  → False.
Proof.
destruct_ac.
intros * Hc11 Hzs1 Hzs2 Hzc1 Hzs12 H12.
destruct (rngl_ltb_dec 0 (rngl_cos θ2)) as [Hzc2| Hzc2]. {
  apply rngl_ltb_lt in Hzc2.
  change_angle_opp θ2.
  progress sin_cos_opp_hyp T Hzs2.
  progress sin_cos_opp_hyp T H12.
  progress sin_cos_opp_hyp T Hzs12.
  progress sin_cos_opp_hyp T Hzc2.
  apply rngl_nlt_ge in H12.
  apply H12; clear H12.
  rewrite rngl_cos_sub_comm.
  destruct (rngl_eqb_dec (rngl_cos θ1) (rngl_cos θ2)) as [Hc1c2| Hc1c2]. {
    apply (rngl_eqb_eq Heo) in Hc1c2.
    apply rngl_cos_eq in Hc1c2.
    destruct Hc1c2; subst θ1. {
      rewrite angle_sub_diag; cbn.
      apply (rngl_le_neq Hor).
      split; [ apply rngl_cos_bound | easy ].
    }
    cbn in Hzs1, Hzc1.
    rewrite angle_sub_opp_r.
    exfalso.
    apply rngl_nlt_ge in Hzs12.
    apply Hzs12; clear Hzs12; cbn.
    rewrite (rngl_mul_opp_r Hop).
    rewrite (rngl_mul_opp_l Hop).
    rewrite (rngl_add_opp_r Hop).
    rewrite <- (rngl_opp_add_distr Hop).
    apply (rngl_opp_neg_pos Hop Hor).
    rewrite (rngl_mul_comm Hic).
    apply (rngl_lt_0_add Hos Hor).
    now apply (rngl_mul_pos_pos Hon Hop Hiq Hor).
    apply (rngl_mul_nonneg_nonneg Hon Hos Hiq Hor).
    now apply (rngl_lt_le_incl Hor).
    now apply (rngl_lt_le_incl Hor).
  }
  apply rngl_cos_lt_cos_sub; try easy.
  apply quadrant_1_sin_sub_nonneg_cos_le; try easy.
  now apply (rngl_lt_le_incl Hor).
  now apply (rngl_lt_le_incl Hor).
}
apply (rngl_ltb_ge_iff Hor) in Hzc2.
change_angle_add_r θ2 π.
progress sin_cos_add_sub_straight_hyp T Hzs2.
progress sin_cos_add_sub_straight_hyp T H12.
progress sin_cos_add_sub_straight_hyp T Hzs12.
progress sin_cos_add_sub_straight_hyp T Hzc2.
exfalso.
apply rngl_nlt_ge in Hzs12.
apply Hzs12; clear Hzs12; cbn.
apply (rngl_add_nonneg_pos Hos Hor).
now apply (rngl_mul_nonneg_nonneg Hon Hos Hiq Hor).
now apply (rngl_mul_pos_pos Hon Hop Hiq Hor).
Qed.

Theorem angle_add_overflow_le_lemma_6 :
  ∀ θ1 θ2,
  (0 ≤ rngl_sin θ1)%L
  → (rngl_sin θ2 < 0)%L
  → (0 ≤ rngl_sin (θ1 + θ2))%L
  → (rngl_cos (θ1 + θ2) ≤ rngl_cos θ1)%L
  → False.
Proof.
destruct_ac.
destruct (Nat.eq_dec (rngl_characteristic T) 1) as [Hc1| Hc1]. {
  specialize (rngl_characteristic_1 Hon Hos Hc1) as H1.
  intros * Hzs1 Hzs2 Hzs12 H12.
  rewrite (H1 (rngl_sin _)) in Hzs2.
  now apply (rngl_lt_irrefl Hor) in Hzs2.
}
intros * Hzs1 Hzs2 Hzs12 H12.
destruct (rngl_ltb_dec 0 (rngl_cos θ1)) as [Hzc1| Hzc1]. {
  apply rngl_ltb_lt in Hzc1.
  destruct (rngl_eqb_dec (rngl_cos θ1) 1) as [H| H]. {
    apply (rngl_eqb_eq Heo) in H.
    apply eq_rngl_cos_1 in H.
    subst θ1.
    rewrite angle_add_0_l in Hzs12.
    now apply rngl_nlt_ge in Hzs12.
  }
  apply (rngl_eqb_neq Heo) in H.
  now apply angle_add_overflow_le_lemma_5 in H12.
}
apply (rngl_ltb_ge_iff Hor) in Hzc1.
change_angle_sub_r θ1 π/₂.
progress sin_cos_add_sub_right_hyp T Hzs1.
progress sin_cos_add_sub_right_hyp T Hzc1.
progress sin_cos_add_sub_right_hyp T H12.
progress sin_cos_add_sub_right_hyp T Hzs12.
destruct (rngl_ltb_dec 0 (rngl_cos θ2)) as [Hzc2| Hzc2]. {
  apply rngl_ltb_lt in Hzc2.
  change_angle_opp θ2.
  progress sin_cos_opp_hyp T Hzs2.
  progress sin_cos_opp_hyp T Hzc2.
  progress sin_cos_opp_hyp T Hzs12.
  progress sin_cos_opp_hyp T H12.
  apply rngl_nlt_ge in H12.
  apply H12; clear H12.
  rename Hzs12 into Hzc12.
  destruct (rngl_ltb_dec (rngl_sin (θ1 - θ2)) 0) as [Hs12z| Hzs12]. {
    apply rngl_ltb_lt in Hs12z.
    eapply (rngl_lt_le_trans Hor); [ apply Hs12z | easy ].
  }
  apply (rngl_ltb_ge_iff Hor) in Hzs12.
  destruct (rngl_eqb_dec (rngl_cos θ2) 1) as [Hc21| Hc21]. {
    apply (rngl_eqb_eq Heo) in Hc21.
    apply eq_rngl_cos_1 in Hc21.
    subst θ2.
    now apply (rngl_lt_irrefl Hor) in Hzs2.
  }
  apply (rngl_eqb_neq Heo) in Hc21.
  destruct (rngl_eqb_dec (rngl_cos θ1) 0) as [Hc1z| Hc1z]. {
    apply (rngl_eqb_eq Heo) in Hc1z.
    apply eq_rngl_cos_0 in Hc1z.
    destruct Hc1z; subst θ1. {
      rewrite rngl_sin_sub_right_l.
      apply (rngl_le_neq Hor).
      split; [ | easy ].
      apply rngl_cos_bound.
    }
    exfalso.
    apply rngl_nlt_ge in Hzc1.
    apply Hzc1; cbn.
    apply (rngl_opp_1_lt_0 Hon Hop Hiq Hor Hc1).
  }
  apply (rngl_eqb_neq Heo) in Hc1z.
  apply rngl_sin_sub_lt_sin_l; [ easy | easy | ].
  apply (rngl_le_neq Hor).
  now apply not_eq_sym in Hc1z.
}
apply (rngl_ltb_ge_iff Hor) in Hzc2.
change_angle_add_r θ2 π.
progress sin_cos_add_sub_straight_hyp T Hzs2.
progress sin_cos_add_sub_straight_hyp T Hzc2.
progress sin_cos_add_sub_straight_hyp T Hzs12.
progress sin_cos_add_sub_straight_hyp T H12.
apply rngl_nlt_ge in H12.
apply H12; clear H12.
destruct (rngl_eqb_dec (rngl_sin θ1) 0) as [Hs1z| Hs1z]. {
  apply (rngl_eqb_eq Heo) in Hs1z.
  apply eq_rngl_sin_0 in Hs1z.
  destruct Hs1z; subst θ1. {
    rewrite angle_add_0_l; cbn.
    now rewrite rngl_add_0_l.
  }
  exfalso.
  apply rngl_nlt_ge in Hzs1.
  apply Hzs1; cbn.
  apply (rngl_opp_1_lt_0 Hon Hop Hiq Hor Hc1).
}
apply (rngl_eqb_neq Heo) in Hs1z.
apply (rngl_lt_0_add Hos Hor). {
  apply not_eq_sym in Hs1z.
  now apply (rngl_le_neq Hor).
}
cbn.
apply (rngl_le_0_add Hos Hor).
now apply (rngl_mul_nonneg_nonneg Hon Hos Hiq Hor).
apply (rngl_mul_nonneg_nonneg Hon Hos Hiq Hor); [ easy | ].
now apply (rngl_lt_le_incl Hor).
Qed.

Context {rl : real_like_prop T}.

End a.

Section a.

Context {T : Type}.
Context {ro : ring_like_op T}.
Context {rp : ring_like_prop T}.
Context {rl : real_like_prop T}.
Context {ac : angle_ctx T}.

Fixpoint angle_mul_nat_overflow n θ :=
  match n with
  | 0 | 1 => false
  | S n' =>
      (angle_add_overflow θ (n' * θ) ||
       angle_mul_nat_overflow n' θ)%bool
  end.

Theorem angle_mul_nat_overflow_succ_l_false :
  ∀ θ n,
  angle_mul_nat_overflow (S n) θ = false
  ↔ angle_mul_nat_overflow n θ = false ∧
    angle_add_overflow θ (n * θ) = false.
Proof.
intros.
split; intros Hn. {
  destruct n. {
    split; [ easy | cbn ].
    apply angle_add_overflow_0_r.
  }
  remember (S n) as sn; cbn in Hn; subst sn.
  now apply Bool.orb_false_iff in Hn.
} {
  destruct n; [ easy | ].
  remember (S n) as sn; cbn; subst sn.
  now apply Bool.orb_false_iff.
}
Qed.

Theorem angle_mul_1_l : ∀ θ, (1 * θ)%A = θ.
Proof.
intros; cbn.
apply angle_add_0_r.
Qed.

Theorem angle_mul_nat_assoc :
  ∀ a b θ, (a * (b * θ) = (a * b) * θ)%A.
Proof.
intros.
induction a; [ easy | cbn ].
rewrite IHa.
symmetry.
apply angle_mul_add_distr_r.
Qed.

Theorem angle_lim_add_add :
  ∀ u v θ1 θ2,
  angle_lim u θ1
  → angle_lim v θ2
  → angle_lim (λ i, (u i + v i))%A (θ1 + θ2).
Proof.
destruct_ac.
specialize (rngl_has_inv_and_1_has_inv_and_1_or_pdiv Hon Hiv) as Hi1.
destruct (Nat.eq_dec (rngl_characteristic T) 1) as [Hc1| Hc1]. {
  intros * Hu Hv ε Hε.
  rewrite (rngl_characteristic_1 Hon Hos Hc1 ε) in Hε.
  now apply (rngl_lt_irrefl Hor) in Hε.
}
intros * Hu Hv.
intros ε Hε.
assert (Hε2 : (0 < ε / 2)%L). {
  apply (rngl_lt_div_r Hon Hop Hiv Hor).
  apply (rngl_0_lt_2 Hon Hos Hiq Hc1 Hor).
  now rewrite (rngl_mul_0_l Hos).
}
specialize (Hu _ Hε2).
specialize (Hv _ Hε2).
destruct Hu as (M, HM).
destruct Hv as (N, HN).
exists (max M N).
intros n Hn.
specialize (HM n (Nat.max_lub_l _ _ _ Hn)).
specialize (HN n (Nat.max_lub_r _ _ _ Hn)).
cbn in HM, HN |-*.
rewrite angle_eucl_dist_move_0_l in HM, HN.
rewrite angle_eucl_dist_move_0_l.
specialize (rngl_div_add_distr_r Hiv ε ε 2)%L as Hεε2.
rewrite <- (rngl_mul_2_r Hon) in Hεε2.
rewrite (rngl_mul_div Hi1) in Hεε2. 2: {
  apply (rngl_2_neq_0 Hon Hos Hiq Hc1 Hor).
}
rewrite Hεε2.
eapply (rngl_le_lt_trans Hor). {
  apply (angle_eucl_dist_triangular _ (θ1 - u n)).
}
apply (rngl_add_lt_compat Hos Hor); [ | easy ].
rewrite angle_add_comm.
rewrite angle_eucl_dist_move_0_r.
rewrite angle_sub_sub_swap.
rewrite angle_sub_sub_distr.
rewrite angle_add_sub.
rewrite angle_sub_add_distr.
now rewrite angle_add_sub.
Qed.

Theorem angle_lim_mul :
  ∀ k u θ,
  angle_lim u θ
  → angle_lim (λ i, (k * u i)%A) (k * θ).
Proof.
destruct_ac.
specialize (rngl_has_inv_and_1_has_inv_and_1_or_pdiv Hon Hiv) as Hi1.
intros * Hu.
induction k. {
  intros ε Hε.
  exists 0.
  intros n _.
  cbn.
  progress unfold angle_eucl_dist.
  progress unfold rl_modl.
  cbn.
  do 2 rewrite (rngl_sub_diag Hos).
  rewrite (rngl_squ_0 Hos).
  rewrite rngl_add_0_l.
  now rewrite (rl_sqrt_0 Hon Hop Hor Hii).
}
cbn.
now apply angle_lim_add_add.
Qed.

Theorem angle_mul_0_r : ∀ n, (n * 0 = 0)%A.
Proof.
destruct_ac.
intros.
apply eq_angle_eq; cbn.
induction n; [ easy | cbn ].
do 2 rewrite (rngl_mul_1_l Hon).
do 2 rewrite (rngl_mul_0_l Hos).
rewrite (rngl_sub_0_r Hos).
now rewrite rngl_add_0_l.
Qed.

Theorem angle_mul_nat_overflow_0_l :
  ∀ θ, angle_mul_nat_overflow 0 θ = false.
Proof. easy. Qed.

Theorem angle_mul_nat_overflow_0_r :
  ∀ n, angle_mul_nat_overflow n 0 = false.
Proof.
intros.
induction n; [ easy | cbn ].
destruct n; [ easy | ].
rewrite angle_add_overflow_0_l.
now apply Bool.orb_false_iff.
Qed.

Theorem angle_add_not_overflow_move_add :
  ∀ θ1 θ2 θ3,
  angle_add_overflow θ1 θ3 = false
  → angle_add_overflow (θ1 + θ3) θ2 = false
  → angle_add_overflow θ1 (θ2 + θ3) = false.
Proof.
destruct_ac.
intros * H13 H132.
rewrite <- angle_add_overflow_equiv2 in H132 |-*.
progress unfold angle_add_overflow2 in H132.
progress unfold angle_add_overflow2.
apply Bool.not_true_iff_false in H132.
apply angle_nlt_ge in H132.
apply Bool.not_true_iff_false.
apply angle_nlt_ge.
rewrite angle_add_add_swap in H132.
rewrite <- angle_add_assoc in H132.
apply (angle_le_trans _ (θ1 + θ3))%A; [ | apply H132 ].
rewrite <- angle_add_overflow_equiv2 in H13.
progress unfold angle_add_overflow2 in H13.
apply Bool.not_true_iff_false in H13.
now apply angle_nlt_ge in H13.
Qed.

Theorem angle_add_overflow_move_add :
  ∀ θ1 θ2 θ3,
  angle_add_overflow θ2 θ3 = false
  → angle_add_overflow (θ1 + θ2) θ3 = true
  → angle_add_overflow θ1 (θ2 + θ3) = true.
Proof.
destruct_ac.
intros * H23 H123.
apply Bool.not_false_iff_true in H123.
apply Bool.not_false_iff_true.
intros H; apply H123.
rewrite angle_add_overflow_comm.
apply angle_add_not_overflow_move_add.
now rewrite angle_add_overflow_comm.
rewrite angle_add_comm.
now rewrite angle_add_overflow_comm.
Qed.

Theorem angle_add_overflow_assoc :
  ∀ θ1 θ2 θ3,
  angle_add_overflow θ1 θ2 = false
  → angle_add_overflow θ2 θ3 = false
  → angle_add_overflow (θ1 + θ2) θ3 = angle_add_overflow θ1 (θ2 + θ3).
Proof.
intros * H12 H23.
remember (angle_add_overflow (θ1 + θ2) θ3) as ov eqn:Hov.
symmetry in Hov |-*.
destruct ov; [ now apply angle_add_overflow_move_add | ].
rewrite angle_add_comm.
now apply angle_add_not_overflow_move_add.
Qed.

Theorem angle_mul_2_l : ∀ θ, (2 * θ = θ + θ)%A.
Proof.
intros; cbn.
now rewrite angle_add_0_r.
Qed.

Theorem angle_mul_nat_overflow_succ_l_true :
  ∀ θ n,
  angle_mul_nat_overflow (S n) θ = true
  ↔ angle_mul_nat_overflow n θ = true ∨
    angle_add_overflow θ (n * θ) = true.
Proof.
intros.
split; intros Hn. {
  apply Bool.not_false_iff_true in Hn.
  remember (angle_mul_nat_overflow n θ) as x eqn:Hx.
  symmetry in Hx.
  destruct x; [ now left | right ].
  apply Bool.not_false_iff_true.
  intros Hy.
  apply Hn.
  now apply angle_mul_nat_overflow_succ_l_false.
} {
  apply Bool.not_false_iff_true.
  intros Hx.
  apply angle_mul_nat_overflow_succ_l_false in Hx.
  destruct Hx as (Hx, Hy).
  rewrite Hx in Hn.
  rewrite Hy in Hn.
  now destruct Hn.
}
Qed.

Theorem angle_mul_nat_overflow_succ_l :
  ∀ θ n,
  angle_mul_nat_overflow (S n) θ =
    (angle_mul_nat_overflow n θ || angle_add_overflow θ (n * θ))%bool.
Proof.
intros.
remember (_ || _)%bool as b eqn:Hb.
symmetry in Hb.
destruct b. {
  apply Bool.orb_true_iff in Hb.
  now apply angle_mul_nat_overflow_succ_l_true.
} {
  apply Bool.orb_false_iff in Hb.
  now apply angle_mul_nat_overflow_succ_l_false.
}
Qed.

Fixpoint rngl_cos_div_pow_2 θ n :=
  match n with
  | 0 => rngl_cos θ
  | S n' => (√((1 + rngl_cos_div_pow_2 θ n') / 2))%L
  end.

Fixpoint squ_rngl_cos_div_pow_2 θ n :=
  match n with
  | 0 => rngl_cos θ
  | S n' => ((1 + squ_rngl_cos_div_pow_2 θ n') / 2)%L
  end.

Theorem rngl_cos_div_pow_2_0 : ∀ n, rngl_cos_div_pow_2 0 n = 1%L.
Proof.
destruct_ac.
specialize (rngl_has_inv_and_1_has_inv_and_1_or_pdiv Hon Hiv) as Hi1.
specialize (rngl_int_dom_or_inv_1_quo_and_eq_dec Hi1 Hed) as Hid.
destruct (Nat.eq_dec (rngl_characteristic T) 1) as [Hc1| Hc1]. {
  intros.
  specialize (rngl_characteristic_1 Hon Hos Hc1) as H1.
  rewrite (H1 1%L).
  apply H1.
}
intros n.
induction n; [ easy | cbn ].
rewrite IHn.
rewrite (rngl_div_diag Hon Hiq). 2: {
  apply (rngl_2_neq_0 Hon Hos Hiq Hc1 Hor).
}
now apply (rl_sqrt_1 Hon Hop Hiq Hor).
Qed.

Theorem squ_rngl_cos_div_pow_2_0 : ∀ n, squ_rngl_cos_div_pow_2 0 n = 1%L.
Proof.
destruct_ac.
destruct (Nat.eq_dec (rngl_characteristic T) 1) as [Hc1| Hc1]. {
  intros.
  specialize (rngl_characteristic_1 Hon Hos Hc1) as H1.
  rewrite (H1 1%L).
  apply H1.
}
intros n.
induction n; [ easy | cbn ].
rewrite IHn.
apply (rngl_div_diag Hon Hiq).
apply (rngl_2_neq_0 Hon Hos Hiq Hc1 Hor).
Qed.

Theorem rngl_cos_decr :
  ∀ θ1 θ2, (θ1 ≤ θ2 ≤ π)%A → (rngl_cos θ2 ≤ rngl_cos θ1)%L.
Proof.
destruct_ac.
intros * (H12, H2s).
progress unfold angle_leb in H12, H2s.
cbn in H2s.
rewrite (rngl_leb_refl Hor) in H2s.
remember (0 ≤? rngl_sin θ2)%L as zs2 eqn:Hzs2.
symmetry in Hzs2.
destruct zs2; [ | easy ].
destruct (0 ≤? rngl_sin θ1)%L; [ | easy ].
now apply rngl_leb_le in H12.
Qed.

Theorem rngl_cos_decr_lt :
  ∀ θ1 θ2, (θ1 < θ2 ≤ π)%A → (rngl_cos θ2 < rngl_cos θ1)%L.
Proof.
destruct_ac.
intros * (H12, H2s).
progress unfold angle_ltb in H12.
progress unfold angle_leb in H2s.
cbn in H2s.
rewrite (rngl_leb_refl Hor) in H2s.
remember (0 ≤? rngl_sin θ2)%L as zs2 eqn:Hzs2.
symmetry in Hzs2.
destruct zs2; [ | easy ].
destruct (0 ≤? rngl_sin θ1)%L; [ | easy ].
now apply rngl_ltb_lt in H12.
Qed.

Theorem angle_le_dec :
  ∀ θ1 θ2 : angle T, {(θ1 ≤ θ2)%A} + {¬ (θ1 ≤ θ2)%A}.
Proof.
intros.
remember (θ1 ≤? θ2)%A as t12 eqn:Ht12.
symmetry in Ht12.
destruct t12; [ now left | now right ].
Qed.

Theorem angle_lt_dec :
  ∀ θ1 θ2 : angle T, {(θ1 < θ2)%A} + {¬ (θ1 < θ2)%A}.
Proof.
intros.
remember (θ1 <? θ2)%A as t12 eqn:Ht12.
symmetry in Ht12.
destruct t12; [ now left | now right ].
Qed.

Theorem angle_le_antisymm : ∀ θ1 θ2, (θ1 ≤ θ2)%A → (θ2 ≤ θ1)%A → θ1 = θ2.
Proof.
destruct_ac.
intros * H12 H21.
progress unfold angle_leb in H12.
progress unfold angle_leb in H21.
apply eq_angle_eq.
remember (0 ≤? rngl_sin θ1)%L as zs1 eqn:Hzs1.
remember (0 ≤? rngl_sin θ2)%L as zs2 eqn:Hzs2.
remember (0 ≤? rngl_cos θ1)%L as zc1 eqn:Hzc1.
remember (0 ≤? rngl_cos θ2)%L as zc2 eqn:Hzc2.
symmetry in Hzs1, Hzs2, Hzc1, Hzc2.
destruct zs1. 2: {
  destruct zs2; [ easy | ].
  apply rngl_leb_le in H12, H21.
  apply (rngl_le_antisymm Hor) in H12; [ clear H21 | easy ].
  rewrite H12; f_equal.
  apply (rngl_leb_gt_iff Hor) in Hzs1, Hzs2.
  (* lemma? *)
  change_angle_opp θ1.
  progress sin_cos_opp_hyp T Hzs1.
  change_angle_opp θ2.
  progress sin_cos_opp_hyp T Hzs2.
  cbn in H12 |-*.
  f_equal.
  apply (rngl_lt_le_incl Hor) in Hzs1, Hzs2.
  specialize (rngl_sin_nonneg_cos_le_sin_le θ1 θ2 Hzs1 Hzs2) as H1.
  specialize (rngl_sin_nonneg_cos_le_sin_le θ2 θ1 Hzs2 Hzs1) as H2.
  rewrite H12 in H1, H2.
  specialize (H1 (rngl_le_refl Hor _)).
  specialize (H2 (rngl_le_refl Hor _)).
  cbn in Hzc1.
  rewrite Hzc1 in H1, H2.
  now destruct zc1; apply (rngl_le_antisymm Hor).
}
destruct zs2; [ | easy ].
apply rngl_leb_le in H12, H21.
apply (rngl_le_antisymm Hor) in H12; [ clear H21 | easy ].
rewrite H12; f_equal.
apply rngl_leb_le in Hzs1, Hzs2.
specialize (rngl_sin_nonneg_cos_le_sin_le θ1 θ2 Hzs1 Hzs2) as H1.
specialize (rngl_sin_nonneg_cos_le_sin_le θ2 θ1 Hzs2 Hzs1) as H2.
rewrite H12 in H1, H2.
specialize (H1 (rngl_le_refl Hor _)).
specialize (H2 (rngl_le_refl Hor _)).
cbn in Hzc2.
rewrite Hzc2 in H1, H2.
now destruct zc2; apply (rngl_le_antisymm Hor).
Qed.

Theorem angle_opp_lt_compat_if :
  ∀ θ1 θ2,
  (θ1 ≠ 0)%A
  → (θ1 < θ2)%A
  → (- θ2 < - θ1)%A.
Proof.
destruct_ac.
intros * H1z H12.
progress unfold angle_ltb in H12.
progress unfold angle_ltb.
cbn.
do 2 rewrite (rngl_leb_0_opp Hop Hor).
remember (0 ≤? rngl_sin θ1)%L as zs1 eqn:Hzs1.
remember (rngl_sin θ1 ≤? 0)%L as s1z eqn:Hs1z.
remember (0 ≤? rngl_sin θ2)%L as zs2 eqn:Hzs2.
remember (rngl_sin θ2 ≤? 0)%L as s2z eqn:Hs2z.
symmetry in Hzs1, Hs1z.
symmetry in Hzs2, Hs2z.
destruct s2z. {
  destruct s1z; [ | easy ].
  apply rngl_leb_le in Hs1z.
  apply rngl_leb_le in Hs2z.
  apply rngl_ltb_lt.
  destruct zs2. {
    destruct zs1; [ | easy ].
    apply rngl_leb_le in Hzs1.
    apply rngl_leb_le in Hzs2.
    apply rngl_ltb_lt in H12.
    apply (rngl_le_antisymm Hor) in Hzs1; [ | easy ].
    apply eq_rngl_sin_0 in Hzs1.
    destruct Hzs1; subst θ1; [ easy | clear H1z ].
    apply (rngl_le_neq Hor).
    split; [ apply rngl_cos_bound | ].
    intros H2; symmetry in H2.
    apply eq_rngl_cos_opp_1 in H2; subst θ2.
    now apply (rngl_lt_irrefl Hor) in H12.
  }
  apply (rngl_leb_gt_iff Hor) in Hzs2.
  destruct zs1; [ | now apply rngl_ltb_lt in H12 ].
  apply rngl_leb_le in Hzs1.
  apply (rngl_le_antisymm Hor) in Hzs1; [ | easy ].
  apply eq_rngl_sin_0 in Hzs1.
  destruct Hzs1; subst θ1; [ easy | clear H1z ].
  apply (rngl_le_neq Hor).
  split; [ apply rngl_cos_bound | ].
  intros Hc; symmetry in Hc.
  apply eq_rngl_cos_opp_1 in Hc; subst θ2.
  now apply (rngl_lt_irrefl Hor) in Hzs2.
}
apply (rngl_leb_gt_iff Hor) in Hs2z.
destruct zs2. 2: {
  apply (rngl_leb_gt_iff Hor) in Hzs2.
  now apply (rngl_lt_asymm Hor) in Hzs2.
}
clear Hzs2.
destruct zs1; [ | easy ].
destruct s1z; [ | easy ].
exfalso.
apply rngl_leb_le in Hzs1, Hs1z.
apply (rngl_le_antisymm Hor) in Hzs1; [ | easy ].
apply eq_rngl_sin_0 in Hzs1.
destruct Hzs1; subst θ1; [ easy | ].
apply rngl_ltb_lt in H12.
apply rngl_nle_gt in H12.
apply H12, rngl_cos_bound.
Qed.

Theorem angle_opp_le_compat_if :
  ∀ θ1 θ2,
  (θ1 ≠ 0)%A
  → (θ1 ≤ θ2)%A
  → (- θ2 ≤ - θ1)%A.
Proof.
intros * H1z H12.
destruct (angle_lt_dec θ1 θ2) as [Hl12| Hl12]. {
  specialize (angle_opp_lt_compat_if θ1 θ2 H1z Hl12) as H1.
  now apply angle_lt_le_incl in H1.
}
apply angle_nlt_ge in Hl12.
apply angle_le_antisymm in H12; [ | easy ].
subst θ2.
apply angle_le_refl.
Qed.

Theorem rngl_sin_add_pos_1 :
  ∀ θ1 θ2,
  (0 ≤ rngl_sin θ1)%L
  → (0 < rngl_sin θ2)%L
  → (0 < rngl_cos θ1)%L
  → (0 ≤ rngl_cos θ2)%L
  → (0 < rngl_sin (θ1 + θ2))%L.
Proof.
destruct_ac.
intros  * Hs1z Hs2z Hc1z Hc2z.
cbn.
apply (rngl_add_nonneg_pos Hos Hor).
now apply (rngl_mul_nonneg_nonneg Hon Hos Hiq Hor).
now apply (rngl_mul_pos_pos Hon Hop Hiq Hor).
Qed.

Theorem rngl_sin_add_pos_2 :
  ∀ θ1 θ2,
  (0 < rngl_sin θ1)%L
  → (0 ≤ rngl_sin θ2)%L
  → (0 ≤ rngl_cos θ1)%L
  → (0 < rngl_cos θ2)%L
  → (0 < rngl_sin (θ1 + θ2))%L.
Proof.
destruct_ac.
intros  * Hs1z Hs2z Hc1z Hc2z.
cbn.
apply (rngl_lt_0_add Hos Hor).
now apply (rngl_mul_pos_pos Hon Hop Hiq Hor).
now apply (rngl_mul_nonneg_nonneg Hon Hos Hiq Hor).
Qed.

Theorem rngl_cos_sub_pos_2 :
  ∀ θ1 θ2,
  (0 < rngl_sin θ1)%L
  → (0 < rngl_sin θ2)%L
  → (0 ≤ rngl_cos θ1)%L
  → (0 ≤ rngl_cos θ2)%L
  → (0 < rngl_cos (θ1 - θ2))%L.
Proof.
destruct_ac.
intros  * Hs1z Hs2z Hc1z Hc2z.
rewrite rngl_cos_sub.
apply (rngl_add_nonneg_pos Hos Hor).
now apply (rngl_mul_nonneg_nonneg Hon Hos Hiq Hor).
now apply (rngl_mul_pos_pos Hon Hop Hiq Hor).
Qed.

Theorem rngl_sin_mul_2_l :
  ∀ θ, rngl_sin (2 * θ) = (2 * rngl_sin θ * rngl_cos θ)%L.
Proof.
destruct_ac.
intros; cbn.
do 2 rewrite (rngl_mul_1_r Hon).
do 2 rewrite (rngl_mul_0_r Hos).
rewrite (rngl_sub_0_r Hos).
rewrite rngl_add_0_r.
rewrite (rngl_mul_comm Hic (rngl_cos θ)).
rewrite <- rngl_mul_assoc; symmetry.
apply (rngl_mul_2_l Hon).
Qed.

Theorem rngl_cos_mul_2_l :
  ∀ θ, rngl_cos (2 * θ) = (rngl_cos² θ - rngl_sin² θ)%L.
Proof.
destruct_ac.
intros; cbn.
do 2 rewrite (rngl_mul_1_r Hon).
do 2 rewrite (rngl_mul_0_r Hos).
rewrite (rngl_sub_0_r Hos).
rewrite rngl_add_0_r.
now do 2 rewrite fold_rngl_squ.
Qed.

Theorem angle_straight_neq_0 :
  rngl_characteristic T ≠ 1
  → π ≠ 0%A.
Proof.
destruct_ac.
intros Hc1.
intros H.
apply eq_angle_eq in H.
injection H; clear H; intros H.
specialize (rngl_opp_1_lt_1 Hon Hop Hiq Hor Hc1) as H1.
rewrite H in H1.
now apply (rngl_lt_irrefl Hor) in H1.
Qed.

Theorem rngl_negb_ltb :
  rngl_is_ordered T = true →
  ∀ a b, (negb (a <? b) = (b ≤? a))%L.
Proof.
intros Hor *.
progress unfold rngl_is_ordered in Hor.
progress unfold rngl_ltb.
progress unfold rngl_leb.
destruct rngl_opt_leb; [ apply Bool.negb_involutive | easy ].
Qed.

Theorem rngl_lt_0_cos :
  ∀ θ, (θ < π/₂ ∨ - π/₂ < θ)%A ↔ (0 < rngl_cos θ)%L.
Proof.
destruct_ac.
destruct (Nat.eq_dec (rngl_characteristic T) 1) as [Hc1| Hc1]. {
  intros.
  specialize (rngl_characteristic_1 Hon Hos Hc1) as H1.
  specialize (rngl_characteristic_1_angle_0 Hc1) as H2.
  rewrite (H1 (rngl_cos _)).
  rewrite (H2 θ), (H2 π/₂).
  rewrite angle_opp_0.
  split; intros H; [ now destruct H; apply angle_lt_irrefl in H | ].
  now apply (rngl_lt_irrefl Hor) in H.
}
intros.
progress unfold angle_ltb.
cbn.
rewrite (rngl_leb_0_opp Hop Hor).
rewrite <- (rngl_negb_ltb Hor 0 1)%L.
specialize (rngl_0_le_1 Hon Hos Hiq Hor) as H1.
specialize (rngl_0_lt_1 Hon Hos Hiq Hc1 Hor) as H2.
apply rngl_leb_le in H1.
apply rngl_ltb_lt in H2.
rewrite H1, H2.
cbn.
remember (0 ≤? rngl_sin θ)%L as zst eqn:Hzst.
symmetry in Hzst.
split; intros Htr. {
  destruct zst. {
    destruct Htr as [Htr| ]; [ | easy ].
    now apply rngl_ltb_lt in Htr.
  } {
    destruct Htr as [| Htr]; [ easy | ].
    now apply rngl_ltb_lt in Htr.
  }
} {
  now destruct zst; [ left | right ]; apply rngl_ltb_lt.
}
Qed.

End a.

