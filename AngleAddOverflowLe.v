Set Nested Proofs Allowed.
Require Import Stdlib.Arith.Arith.
Require Import RingLike.Utf8.

Require Import Init.Nat.
Require Import RingLike.Core.
Require Import Angle AngleDef TrigoWithoutPiExt.
Require Import Order.
Require Import AngleAddOverflowEquiv.
Require Import TacChangeAngle.

Section a.

Context {T : Type}.
Context {ro : ring_like_op T}.
Context {rp : ring_like_prop T}.
Context {ac : angle_ctx T}.

Theorem angle_add_overflow_le_lemma_1 :
  ∀ θ1 θ2 θ3,
  (0 ≤ rngl_sin θ1)%L
  → (0 ≤ rngl_sin θ2)%L
  → (0 ≤ rngl_sin θ3)%L
  → (0 ≤ rngl_sin (θ1 + θ2))%L
  → (0 ≤ rngl_sin (θ1 + θ3))%L
  → (rngl_cos θ2 ≤ rngl_cos θ3)%L
  → (rngl_cos (θ1 + θ2) ≤ rngl_cos θ1)%L
  → (rngl_cos (θ1 + θ3) ≤ rngl_cos θ1)%L.
Proof.
destruct_ac.
destruct (Nat.eq_dec (rngl_characteristic T) 1) as [Hc1| Hc1]. {
  specialize (rngl_characteristic_1 Hos Hc1) as H1.
  intros * Hzs1 Hzs2 Hzs3 Hzs12 Hzs13 H32 H12.
  do 2 rewrite (H1 (rngl_cos _)).
  apply (rngl_le_refl Hor).
}
intros * Hzs1 Hzs2 Hzs3 Hzs12 Hzs13 H32 H12.
destruct (rngl_leb_dec 0 (rngl_cos θ1)) as [Hzc1| Hc1z]. {
  apply rngl_leb_le in Hzc1.
  cbn.
  apply (rngl_le_sub_le_add_r Hop Hto).
  eapply (rngl_le_trans Hor). 2: {
    apply (rngl_le_add_r Hos Hor).
    now apply (rngl_mul_nonneg_nonneg Hos Hor).
  }
  apply (rngl_le_0_sub Hop Hto).
  rewrite (rngl_sub_mul_r_diag_l Hop).
  apply (rngl_mul_nonneg_nonneg Hos Hor); [ easy | ].
  apply (rngl_le_0_sub Hop Hto).
  apply rngl_cos_bound.
}
apply (rngl_leb_gt_iff Hto) in Hc1z.
change_angle_sub_r θ1 π/₂.
progress sin_cos_add_sub_right_hyp T Hzs1.
progress sin_cos_add_sub_right_hyp T Hzs13.
progress sin_cos_add_sub_right_hyp T Hzs12.
progress sin_cos_add_sub_right_hyp T Hc1z.
progress sin_cos_add_sub_right_hyp T H12.
progress sin_cos_add_sub_right_goal T.
destruct (rngl_leb_dec (rngl_cos θ2) 0) as [Hc2z| Hzc2]. {
  apply rngl_leb_le in Hc2z.
  change_angle_sub_r θ2 π/₂.
  progress sin_cos_add_sub_right_hyp T Hzs2.
  progress sin_cos_add_sub_right_hyp T H32.
  progress sin_cos_add_sub_right_hyp T Hzs12.
  progress sin_cos_add_sub_right_hyp T Hc2z.
  progress sin_cos_add_sub_right_hyp T H12.
  apply (rngl_nlt_ge_iff Hto).
  intros Hs13.
  apply rngl_nlt_ge in Hzs12.
  apply Hzs12; clear Hzs12.
  apply (rngl_le_neq Hto).
  split. {
    cbn.
    apply (rngl_le_0_add Hos Hto).
    apply (rngl_mul_nonneg_nonneg Hos Hor); [ | easy ].
    now apply (rngl_lt_le_incl Hto).
    now apply (rngl_mul_nonneg_nonneg Hos Hor).
  }
  intros Hs12.
  symmetry in Hs12.
  apply eq_rngl_sin_0 in Hs12.
  destruct Hs12 as [Hs12| Hs12]. {
    apply angle_add_move_l in Hs12.
    rewrite angle_sub_0_l in Hs12.
    subst θ2.
    cbn in Hc2z.
    apply (rngl_opp_nonneg_nonpos Hop Hto) in Hc2z.
    now apply rngl_nlt_ge in Hc2z.
  }
  apply angle_add_move_l in Hs12.
  subst θ2.
  rewrite rngl_cos_sub_straight_l in Hzs2.
  apply (rngl_opp_nonneg_nonpos Hop Hto) in Hzs2.
  apply (rngl_le_antisymm Hor) in Hzs2; [ | easy ].
  symmetry in Hzs2.
  apply eq_rngl_cos_0 in Hzs2.
  destruct Hzs2; subst θ1. {
    rewrite angle_straight_sub_right in H12.
    rewrite angle_right_add_right in H12.
    apply rngl_nlt_ge in H12.
    apply H12; cbn.
    apply (rngl_opp_1_lt_1 Hop Hto Hc1).
  }
  apply rngl_nle_gt in Hc1z.
  apply Hc1z; cbn.
  apply (rngl_opp_1_le_0 Hop Hor).
}
apply (rngl_leb_gt_iff Hto) in Hzc2.
apply rngl_sin_sub_nonneg_sin_le_sin; try easy. {
  cbn.
  apply (rngl_le_0_add Hos Hto).
  apply (rngl_mul_nonneg_nonneg Hos Hor).
  now apply (rngl_lt_le_incl Hto).
  apply (rngl_lt_le_incl Hto).
  now apply (rngl_lt_le_trans Hto _ (rngl_cos θ2)).
  now apply (rngl_mul_nonneg_nonneg Hos Hor).
} {
  rewrite angle_add_sub_swap.
  rewrite angle_sub_diag.
  now rewrite angle_add_0_l.
}
Qed.

Theorem angle_add_overflow_le_lemma_3 :
  ∀ θ1 θ2 θ3,
  (0 ≤ rngl_sin θ1)%L
  → (0 ≤ rngl_sin θ3)%L
  → (rngl_sin (θ1 + θ2) < 0)%L
  → (0 ≤ rngl_sin (θ1 + θ3))%L
  → (rngl_cos θ2 ≤ rngl_cos θ3)%L
  → (rngl_cos (θ1 + θ3) ≤ rngl_cos θ1)%L.
Proof.
destruct_ac.
intros * Hzs1 Hzs3 Hzs12 Hzs13 H32.
destruct (rngl_leb_dec (rngl_cos θ1) 0) as [Hc1z| Hzc1]. {
  destruct (rngl_eqb_dec (rngl_cos θ1) (-1)) as [Hc1o| Hc1o]. {
    apply (rngl_eqb_eq Heo) in Hc1o.
    apply eq_rngl_cos_opp_1 in Hc1o.
    subst θ1.
    rewrite rngl_sin_add_straight_l in Hzs12, Hzs13.
    rewrite rngl_cos_add_straight_l.
    apply (rngl_opp_nonneg_nonpos Hop Hto) in Hzs13.
    apply (rngl_opp_neg_pos Hop Hto) in Hzs12.
    apply (rngl_le_antisymm Hor) in Hzs13; [ | easy ].
    symmetry in Hzs13.
    apply -> (rngl_opp_le_compat Hop Hto).
    apply eq_rngl_sin_0 in Hzs13.
    destruct Hzs13; subst θ3; [ apply (rngl_le_refl Hor) | ].
    cbn in H32.
    specialize (rngl_cos_bound θ2) as H1.
    apply (rngl_le_antisymm Hor) in H32; [ | easy ].
    clear H1.
    symmetry in H32.
    apply eq_rngl_cos_opp_1 in H32.
    subst θ2.
    now apply (rngl_lt_irrefl Hor) in Hzs12.
  }
  apply (rngl_eqb_neq Heo) in Hc1o.
  apply rngl_leb_le in Hc1z.
  now apply angle_add_overflow_le_lemma_2.
}
apply (rngl_leb_gt_iff Hto) in Hzc1.
move Hzc1 before Hzs3.
destruct (rngl_leb_dec (rngl_cos θ3) 0) as [Hc3z| Hzc3]. {
  apply rngl_leb_le in Hc3z.
  eapply (rngl_le_trans Hor); [ | apply (rngl_lt_le_incl Hto), Hzc1 ].
  cbn.
  progress unfold rngl_sub.
  rewrite Hop.
  apply (rngl_add_nonpos_nonpos Hos Hor).
  apply (rngl_mul_nonneg_nonpos Hop Hto); [ | easy ].
  now apply (rngl_lt_le_incl Hto).
  apply (rngl_opp_nonpos_nonneg Hop Hto).
  now apply (rngl_mul_nonneg_nonneg Hos Hor).
}
apply (rngl_leb_gt_iff Hto) in Hzc3.
move Hzc3 before Hzc1.
apply angle_le_sub_le_add_l_lemma_1; try easy. {
  now apply (rngl_lt_le_incl Hto).
} {
  rewrite angle_sub_diag.
  apply rngl_cos_bound.
}
rewrite angle_sub_diag.
apply (rngl_le_refl Hor).
Qed.

Theorem angle_add_overflow_le_lemma_4 :
  ∀ θ1 θ2 θ3,
  (0 ≤ rngl_sin θ1)%L
  → (rngl_sin θ2 < 0)%L
  → (0 ≤ rngl_sin θ3)%L
  → (rngl_sin (θ1 + θ2) < 0)%L
  → (0 ≤ rngl_sin (θ1 + θ3))%L
  → (rngl_cos (θ1 + θ3) ≤ rngl_cos θ1)%L.
Proof.
destruct_ac.
intros * Hzs1 Hzs2 Hzs3 Hzs12 Hzs13.
destruct (rngl_eqb_dec (rngl_cos θ1) (-1)) as [Hc1o| Hc1o]. {
  apply (rngl_eqb_eq Heo) in Hc1o.
  apply eq_rngl_cos_opp_1 in Hc1o.
  subst θ1.
  rewrite rngl_sin_add_straight_l in Hzs13.
  apply (rngl_opp_nonneg_nonpos Hop Hto) in Hzs13.
  apply (rngl_le_antisymm Hor) in Hzs13; [ | easy ].
  symmetry in Hzs13.
  apply eq_rngl_sin_0 in Hzs13.
  destruct Hzs13; subst θ3. {
    rewrite rngl_cos_add_straight_l.
    apply (rngl_le_refl Hor).
  }
  rewrite rngl_sin_add_straight_l in Hzs12.
  apply (rngl_opp_neg_pos Hop Hto) in Hzs12.
  apply (rngl_lt_le_incl Hto) in Hzs12.
  now apply rngl_nlt_ge in Hzs12.
}
apply (rngl_eqb_neq Heo) in Hc1o.
destruct (rngl_leb_dec 0 (rngl_cos θ1)) as [Hzc1| Hzc1]. {
  apply rngl_leb_le in Hzc1.
  apply angle_le_sub_le_add_l_lemma_1; try easy. {
    rewrite angle_sub_diag.
    apply rngl_cos_bound.
  } {
    rewrite angle_sub_diag.
    apply (rngl_le_refl Hor).
  }
}
apply (rngl_leb_gt_iff Hto) in Hzc1.
change_angle_sub_r θ1 π/₂.
progress sin_cos_add_sub_right_hyp T Hzs1.
progress sin_cos_add_sub_right_hyp T Hzc1.
progress sin_cos_add_sub_right_hyp T Hc1o.
progress sin_cos_add_sub_right_hyp T Hzs13.
progress sin_cos_add_sub_right_hyp T Hzs12.
progress sin_cos_add_sub_right_goal T.
assert (H : (rngl_sin θ1 ≠ 1)%L) by now intros H; apply Hc1o; f_equal.
move H before Hc1o; clear Hc1o; rename H into Hs11.
destruct (rngl_leb_dec 0 (rngl_cos θ2)) as [Hzc2| Hzc2]. {
  apply rngl_leb_le in Hzc2.
  change_angle_add_r θ2 π/₂.
  progress sin_cos_add_sub_right_hyp T Hzs2.
  progress sin_cos_add_sub_right_hyp T Hzc2.
  progress sin_cos_add_sub_right_hyp T Hzs12.
  exfalso.
  apply rngl_nle_gt in Hzs12.
  apply Hzs12; clear Hzs12; cbn.
  apply (rngl_le_0_add Hos Hto).
  apply (rngl_mul_nonneg_nonneg Hos Hor).
  now apply (rngl_lt_le_incl Hto).
  now apply (rngl_lt_le_incl Hto).
  now apply (rngl_mul_nonneg_nonneg Hos Hor).
}
apply (rngl_leb_gt_iff Hto) in Hzc2.
change_angle_add_r θ2 π.
progress sin_cos_add_sub_straight_hyp T Hzs2.
progress sin_cos_add_sub_straight_hyp T Hzc2.
progress sin_cos_add_sub_straight_hyp T Hzs12.
destruct (rngl_leb_dec (rngl_cos θ3) 0) as [Hc3z| Hzc3]. {
  apply rngl_leb_le in Hc3z.
  change_angle_sub_r θ3 π/₂.
  progress sin_cos_add_sub_right_hyp T Hzs3.
  progress sin_cos_add_sub_right_hyp T Hzs13.
  progress sin_cos_add_sub_right_hyp T Hc3z.
  progress sin_cos_add_sub_right_goal T.
  apply (rngl_nlt_ge_iff Hto).
  intros Hc31.
  apply rngl_nlt_ge in Hzs13.
  apply Hzs13; clear Hzs13.
  apply (rngl_le_neq Hto).
  split. {
    cbn.
    apply (rngl_le_0_add Hos Hto).
    apply (rngl_mul_nonneg_nonneg Hos Hor); [ | easy ].
    now apply (rngl_lt_le_incl Hto).
    now apply (rngl_mul_nonneg_nonneg Hos Hor).
  }
  intros H; symmetry in H.
  apply eq_rngl_sin_0 in H.
  destruct H as [H| H]. {
    rewrite H in Hc31.
    apply rngl_nle_gt in Hc31.
    apply Hc31; clear Hc31; cbn.
    apply rngl_sin_bound.
  }
  apply angle_add_move_l in H.
  subst θ3.
  clear Hc3z.
  rewrite rngl_cos_sub_straight_l in Hzs3.
  apply (rngl_opp_nonneg_nonpos Hop Hto) in Hzs3.
  apply (rngl_le_antisymm Hor) in Hzs3; [ | easy ].
  symmetry in Hzs3.
  apply eq_rngl_cos_0 in Hzs3.
  destruct Hzs3; subst θ1; [ easy | ].
  apply rngl_nle_gt in Hzc1.
  apply Hzc1; cbn.
  apply (rngl_opp_1_le_0 Hop Hor).
}
apply (rngl_leb_gt_iff Hto) in Hzc3.
move Hzc3 before Hzc2.
apply rngl_cos_cos_sin_sin_nonneg_sin_le_cos_le_iff; try easy. {
  now apply (rngl_lt_le_incl Hto).
} {
  cbn.
  apply (rngl_le_0_add Hos Hto).
  apply (rngl_mul_nonneg_nonneg Hos Hor).
  now apply (rngl_lt_le_incl Hto).
  now apply (rngl_lt_le_incl Hto).
  now apply (rngl_mul_nonneg_nonneg Hos Hor).
}
apply angle_le_sub_le_add_l_lemma_1; try easy.
now apply (rngl_lt_le_incl Hto).
now apply (rngl_lt_le_incl Hto).
rewrite angle_sub_diag.
apply rngl_cos_bound.
rewrite angle_sub_diag.
apply (rngl_le_refl Hor).
cbn.
apply (rngl_le_0_add Hos Hto).
apply (rngl_mul_nonneg_nonneg Hos Hor).
now apply (rngl_lt_le_incl Hto).
now apply (rngl_lt_le_incl Hto).
now apply (rngl_mul_nonneg_nonneg Hos Hor).
Qed.

Theorem angle_add_overflow_le_lemma_7 :
  ∀ θ1 θ2 θ3,
  (0 ≤ rngl_sin θ1)%L
  → (0 < rngl_sin θ2)%L
  → (rngl_sin θ3 < 0)%L
  → (0 < rngl_cos θ1)%L
  → (0 < rngl_cos θ2)%L
  → (0 ≤ rngl_cos θ3)%L
  → (0 < rngl_cos (θ1 + θ2))%L
  → (0 ≤ rngl_sin (θ1 + θ3))%L
  → (rngl_cos θ3 ≤ rngl_sin θ2)%L
  → False.
Proof.
destruct_ac.
intros * Hzs1 Hzc2 Hzs3 Hzc1 Hzs2 Hzc3 Hzs12 Hzs13 H32.
change_angle_opp θ3.
sin_cos_opp_hyp T Hzs3.
sin_cos_opp_hyp T Hzc3.
sin_cos_opp_hyp T H32.
sin_cos_opp_hyp T Hzs13.
change_angle_sub_l θ2 π/₂.
sin_cos_add_sub_right_hyp T Hzc2.
sin_cos_add_sub_right_hyp T Hzs2.
sin_cos_add_sub_right_hyp T H32.
sin_cos_add_sub_right_hyp T Hzs12.
rewrite rngl_sin_sub_anticomm in Hzs12.
sin_cos_add_sub_right_hyp T Hzs12.
apply rngl_nlt_ge in H32.
apply H32; clear H32.
apply (rngl_le_neq Hto).
split. 2: {
  intros H.
  apply rngl_cos_eq in H.
  destruct H; subst θ2. {
    rewrite rngl_sin_sub_anticomm in Hzs12.
    apply (rngl_opp_pos_neg Hop Hor) in Hzs12.
    now apply rngl_nle_gt in Hzs12.
  }
  cbn in Hzs2.
  apply (rngl_opp_pos_neg Hop Hor) in Hzs2.
  apply (rngl_lt_le_incl Hto) in Hzs2.
  now apply rngl_nlt_ge in Hzs2.
}
apply rngl_sin_sub_nonneg_sin_le_sin in Hzs13; try easy.
2: now apply (rngl_lt_le_incl Hto).
apply (rngl_lt_le_incl Hto) in Hzs12.
apply rngl_sin_sub_nonneg_sin_le_sin in Hzs12; try easy; cycle 1.
now apply (rngl_lt_le_incl Hto).
now apply (rngl_lt_le_incl Hto).
apply rngl_cos_cos_sin_sin_nonneg_sin_le_cos_le_iff; try easy.
now apply (rngl_lt_le_incl Hto).
now apply (rngl_lt_le_incl Hto).
now apply (rngl_lt_le_incl Hto).
now apply (rngl_le_trans Hor _ (rngl_sin θ1)).
Qed.

Theorem angle_add_overflow_le_lemma_8 :
  ∀ θ1 θ2 θ3,
  (0 ≤ rngl_sin θ1)%L
  → (rngl_sin θ2 < 0)%L
  → (rngl_sin θ3 < 0)%L
  → (rngl_sin (θ1 + θ2) < 0)%L
  → (0 ≤ rngl_sin (θ1 + θ3))%L
  → (rngl_cos θ3 ≤ rngl_cos θ2)%L
  → False.
Proof.
destruct_ac.
intros * Hzs1 Hzs2 Hzs3 Hzs12 Hzs13 H32.
destruct (rngl_leb_dec (rngl_cos θ2) 0) as [Hc2z| Hzc2]. {
  apply rngl_leb_le in Hc2z.
  change_angle_add_r θ2 π.
  progress sin_cos_add_sub_straight_hyp T Hzs2.
  progress sin_cos_add_sub_straight_hyp T Hzs12.
  progress sin_cos_add_sub_straight_hyp T Hc2z.
  progress sin_cos_add_sub_straight_hyp T H32.
  destruct (rngl_ltb_dec 0 (rngl_cos θ3)) as [Hzc3| Hc3z]. {
    apply rngl_ltb_lt in Hzc3.
    apply rngl_nlt_ge in H32.
    apply H32; clear H32.
    now apply (rngl_lt_0_add Hos Hto).
  }
  apply (rngl_ltb_ge_iff Hto) in Hc3z.
  change_angle_add_r θ3 π.
  progress sin_cos_add_sub_straight_hyp T Hzs3.
  progress sin_cos_add_sub_straight_hyp T Hzs13.
  progress sin_cos_add_sub_straight_hyp T Hc3z.
  progress sin_cos_add_sub_straight_hyp T H32.
  apply -> (rngl_le_sub_0 Hop Hto) in H32.
  destruct (rngl_ltb_dec 0 (rngl_cos θ1)) as [Hzc1| Hc1z]. {
    apply rngl_ltb_lt in Hzc1.
    apply rngl_nlt_ge in Hzs13.
    apply Hzs13; clear Hzs13; cbn.
    apply (rngl_add_nonneg_pos Hos Hor).
    now apply (rngl_mul_nonneg_nonneg Hos Hor).
    now apply (rngl_mul_pos_pos Hop Hiq Hto).
  }
  apply (rngl_ltb_ge_iff Hto) in Hc1z.
  change_angle_sub_r θ1 π/₂.
  progress sin_cos_add_sub_right_hyp T Hzs1.
  progress sin_cos_add_sub_right_hyp T Hzs13.
  progress sin_cos_add_sub_right_hyp T Hzs12.
  progress sin_cos_add_sub_right_hyp T Hc1z.
  apply rngl_nlt_ge in Hzs13.
  apply Hzs13; clear Hzs13.
  eapply (rngl_lt_le_trans Hto); [ apply Hzs12 | ].
  apply angle_le_sub_le_add_l_lemma_1; try easy. {
    cbn.
    apply (rngl_le_0_add Hos Hto).
    now apply (rngl_mul_nonneg_nonneg Hos Hor).
    apply (rngl_mul_nonneg_nonneg Hos Hor); [ easy | ].
    now apply (rngl_lt_le_incl Hto).
  } {
    now apply (rngl_lt_le_incl Hto).
  } {
    rewrite angle_add_comm.
    now rewrite angle_add_sub.
  } {
    rewrite angle_add_comm.
    rewrite angle_add_sub.
    now apply (rngl_lt_le_incl Hto).
  } {
    cbn.
    apply (rngl_le_0_add Hos Hto).
    now apply (rngl_mul_nonneg_nonneg Hos Hor).
    apply (rngl_mul_nonneg_nonneg Hos Hor); [ easy | ].
    now apply (rngl_lt_le_incl Hto).
  }
}
apply (rngl_leb_gt_iff Hto) in Hzc2.
change_angle_add_r θ2 π/₂.
progress sin_cos_add_sub_right_hyp T Hzs2.
progress sin_cos_add_sub_right_hyp T Hzs12.
progress sin_cos_add_sub_right_hyp T Hzc2.
progress sin_cos_add_sub_right_hyp T H32.
destruct (rngl_ltb_dec 0 (rngl_cos θ1)) as [Hzc1| Hc1z]. {
  apply rngl_ltb_lt in Hzc1.
  destruct (rngl_leb_dec 0 (rngl_cos θ3)) as [Hzc3| Hc3z]. {
    apply rngl_leb_le in Hzc3.
    now apply (angle_add_overflow_le_lemma_7 θ1 θ2 θ3).
  }
  apply (rngl_leb_gt_iff Hto) in Hc3z.
  change_angle_add_r θ3 π.
  progress sin_cos_add_sub_straight_hyp T Hzs3.
  progress sin_cos_add_sub_straight_hyp T Hzs13.
  progress sin_cos_add_sub_straight_hyp T H32.
  progress sin_cos_add_sub_straight_hyp T Hc3z.
  apply rngl_nlt_ge in Hzs13.
  apply Hzs13; clear Hzs13; cbn.
  apply (rngl_add_nonneg_pos Hos Hor).
  apply (rngl_mul_nonneg_nonneg Hos Hor); [ easy | ].
  now apply (rngl_lt_le_incl Hto).
  now apply (rngl_mul_pos_pos Hop Hiq Hto).
}
apply (rngl_ltb_ge_iff Hto) in Hc1z.
move Hc1z after Hzs2.
change_angle_sub_r θ1 π/₂.
progress sin_cos_add_sub_right_hyp T Hzs1.
progress sin_cos_add_sub_right_hyp T Hc1z.
progress sin_cos_add_sub_right_hyp T Hzs13.
progress sin_cos_add_sub_right_hyp T Hzs12.
apply rngl_nle_gt in Hzs12.
apply Hzs12; clear Hzs12; cbn.
apply (rngl_le_0_add Hos Hto).
apply (rngl_mul_nonneg_nonneg Hos Hor); [ easy | ].
now apply (rngl_lt_le_incl Hto).
apply (rngl_mul_nonneg_nonneg Hos Hor); [ easy | ].
now apply (rngl_lt_le_incl Hto).
Qed.

Theorem angle_add_overflow_le_lemma_9 :
  ∀ θ1 θ2 θ3,
  (rngl_sin θ1 < 0)%L
  → (0 ≤ rngl_sin θ2)%L
  → (0 ≤ rngl_sin θ3)%L
  → (rngl_sin (θ1 + θ2) < 0)%L
  → (0 ≤ rngl_sin (θ1 + θ3))%L
  → (rngl_cos θ2 ≤ rngl_cos θ3)%L
  → False.
Proof.
destruct_ac.
intros * Hzs1 Hzs2 Hzs3 Hzs12 Hzs13 H32.
destruct (rngl_leb_dec 0 (rngl_cos θ1)) as [Hzc1| Hc1z]. {
  apply rngl_leb_le in Hzc1.
  change_angle_add_r θ1 π/₂.
  progress sin_cos_add_sub_right_hyp T Hzs1.
  progress sin_cos_add_sub_right_hyp T Hzs13.
  progress sin_cos_add_sub_right_hyp T Hzs12.
  progress sin_cos_add_sub_right_hyp T Hzc1.
  destruct (rngl_leb_dec (rngl_cos θ2) 0) as [Hc2z| Hzc2]. {
    apply rngl_leb_le in Hc2z.
    change_angle_sub_r θ2 π/₂.
    progress sin_cos_add_sub_right_hyp T Hzs2.
    progress sin_cos_add_sub_right_hyp T H32.
    progress sin_cos_add_sub_right_hyp T Hzs12.
    progress sin_cos_add_sub_right_hyp T Hc2z.
    apply rngl_nle_gt in Hzs12.
    apply Hzs12; clear Hzs12; cbn.
    apply (rngl_le_0_add Hos Hto).
    now apply (rngl_mul_nonneg_nonneg Hos Hor).
    apply (rngl_mul_nonneg_nonneg Hos Hor); [ | easy ].
    now apply (rngl_lt_le_incl Hto).
  }
  apply (rngl_leb_gt_iff Hto) in Hzc2.
  move Hzc2 before Hzs1.
  destruct (rngl_leb_dec (rngl_cos θ3) 0) as [Hc3z| Hzc3]. {
    apply rngl_leb_le in Hc3z.
    apply rngl_nlt_ge in Hc3z.
    apply Hc3z.
    now apply (rngl_lt_le_trans Hto _ (rngl_cos θ2)).
  }
  apply (rngl_leb_gt_iff Hto) in Hzc3.
  move Hzc3 before Hzc2.
  apply rngl_nlt_ge in Hzs13.
  apply Hzs13; clear Hzs13.
  eapply (rngl_lt_le_trans Hto); [ apply Hzs12 | ].
  specialize rngl_sin_nonneg_cos_le_sin_le as H1.
  specialize (H1 θ2 θ3 Hzs2 Hzs3 H32).
  generalize Hzc2; intros H.
  apply (rngl_lt_le_incl Hto) in H.
  apply rngl_leb_le in H.
  rewrite H in H1; clear H.
  cbn.
  apply (rngl_sub_le_compat Hop Hor).
  apply (rngl_mul_le_mono_nonneg_l Hop Hto); [ | easy ].
  now apply (rngl_lt_le_incl Hto).
  now apply (rngl_mul_le_mono_nonneg_l Hop Hto).
}
apply (rngl_leb_gt_iff Hto) in Hc1z.
change_angle_add_r θ1 π.
progress sin_cos_add_sub_straight_hyp T Hzs1.
progress sin_cos_add_sub_straight_hyp T Hzs13.
progress sin_cos_add_sub_straight_hyp T Hzs12.
progress sin_cos_add_sub_straight_hyp T Hc1z.
destruct (rngl_ltb_dec 0 (rngl_cos θ3)) as [Hzc3| Hc3z]. {
  apply rngl_ltb_lt in Hzc3.
  apply rngl_nlt_ge in Hzs13.
  apply Hzs13; clear Hzs13; cbn.
  apply (rngl_lt_0_add Hos Hto).
  now apply (rngl_mul_pos_pos Hop Hiq Hto).
  apply (rngl_mul_nonneg_nonneg Hos Hor); [ | easy ].
  now apply (rngl_lt_le_incl Hto).
}
apply (rngl_ltb_ge_iff Hto) in Hc3z.
change_angle_sub_r θ3 π/₂.
progress sin_cos_add_sub_right_hyp T Hzs13.
progress sin_cos_add_sub_right_hyp T Hzs3.
progress sin_cos_add_sub_right_hyp T H32.
progress sin_cos_add_sub_right_hyp T Hc3z.
destruct (rngl_ltb_dec 0 (rngl_cos θ2)) as [Hzc2| Hc2z]. {
  apply rngl_ltb_lt in Hzc2.
  apply rngl_nlt_ge in H32.
  apply H32; clear H32.
  now apply (rngl_lt_0_add Hos Hto).
}
apply (rngl_ltb_ge_iff Hto) in Hc2z.
change_angle_sub_r θ2 π/₂.
progress sin_cos_add_sub_right_hyp T Hzs2.
progress sin_cos_add_sub_right_hyp T H32.
progress sin_cos_add_sub_right_hyp T Hzs12.
progress sin_cos_add_sub_right_hyp T Hc2z.
apply rngl_nlt_ge in Hzs13.
apply Hzs13; clear Hzs13.
eapply (rngl_lt_le_trans Hto); [ apply Hzs12 | ].
specialize rngl_cos_cos_sin_sin_nonneg_sin_le_cos_le_iff as H1.
specialize (H1 θ3 θ2 Hc3z Hc2z Hzs3 Hzs2).
specialize (proj1 H1 H32) as H23; clear H1.
cbn.
apply (rngl_sub_le_compat Hop Hor).
apply (rngl_mul_le_mono_nonneg_l Hop Hto); [ | easy ].
now apply (rngl_lt_le_incl Hto).
apply (rngl_mul_le_mono_nonneg_l Hop Hto); [ | easy ].
now apply (rngl_lt_le_incl Hto).
Qed.

Theorem angle_add_overflow_le_lemma_10 :
  ∀ θ1 θ2,
  (rngl_sin θ1 < 0)%L
  → (rngl_sin θ2 < 0)%L
  → (rngl_sin (θ1 + θ2) < 0)%L
  → (rngl_cos θ1 ≤ rngl_cos (θ1 + θ2))%L
  → False.
Proof.
destruct_ac.
intros * Hzs1 Hzs2 Hzs12 H12.
destruct (rngl_leb_dec 0 (rngl_cos θ1)) as [Hzc1| Hc1z]. {
  apply rngl_leb_le in Hzc1.
  change_angle_add_r θ1 π/₂.
  progress sin_cos_add_sub_right_hyp T Hzs1.
  progress sin_cos_add_sub_right_hyp T Hzc1.
  progress sin_cos_add_sub_right_hyp T H12.
  progress sin_cos_add_sub_right_hyp T Hzs12.
  destruct (rngl_leb_dec (rngl_cos θ2) 0) as [Hc2z| Hzc2]. {
    apply rngl_leb_le in Hc2z.
    change_angle_add_r θ2 π.
    progress sin_cos_add_sub_straight_hyp T Hzs2.
    progress sin_cos_add_sub_straight_hyp T Hc2z.
    progress sin_cos_add_sub_straight_hyp T Hzs12.
    progress sin_cos_add_sub_straight_hyp T H12.
    apply rngl_nlt_ge in H12.
    apply H12; clear H12.
    apply (rngl_add_nonneg_pos Hos Hor); [ easy | cbn ].
    apply (rngl_add_nonneg_pos Hos Hor).
    now apply (rngl_mul_nonneg_nonneg Hos Hor).
    now apply (rngl_mul_pos_pos Hop Hiq Hto).
  }
  apply (rngl_leb_gt_iff Hto) in Hzc2.
  change_angle_opp θ2.
  progress sin_cos_opp_hyp T Hzs2.
  progress sin_cos_opp_hyp T Hzc2.
  progress sin_cos_opp_hyp T Hzs12.
  progress sin_cos_opp_hyp T H12.
  apply rngl_nlt_ge in H12.
  apply H12; clear H12.
  now apply rngl_sin_sub_lt_sin_l.
}
apply (rngl_leb_gt_iff Hto) in Hc1z.
change_angle_add_r θ1 π.
progress sin_cos_add_sub_straight_hyp T Hzs1.
progress sin_cos_add_sub_straight_hyp T Hc1z.
progress sin_cos_add_sub_straight_hyp T H12.
progress sin_cos_add_sub_straight_hyp T Hzs12.
rewrite rngl_add_comm in H12.
rewrite (rngl_add_opp_r Hop) in H12.
apply -> (rngl_le_sub_0 Hop Hto) in H12.
destruct (rngl_leb_dec (rngl_cos θ2) 0) as [Hc2z| Hzc2]. {
  apply rngl_leb_le in Hc2z.
  change_angle_add_r θ2 π.
  progress sin_cos_add_sub_straight_hyp T Hzs2.
  progress sin_cos_add_sub_straight_hyp T Hc2z.
  progress sin_cos_add_sub_straight_hyp T Hzs12.
  progress sin_cos_add_sub_straight_hyp T H12.
  apply -> (rngl_le_opp_l Hop Hor) in H12.
  apply rngl_nle_gt in Hzs12.
  apply Hzs12; clear Hzs12; cbn.
  apply (rngl_le_0_add Hos Hto).
  apply (rngl_mul_nonneg_nonneg Hos Hor); [ | easy ].
  now apply (rngl_lt_le_incl Hto).
  apply (rngl_mul_nonneg_nonneg Hos Hor).
  now apply (rngl_lt_le_incl Hto).
  now apply (rngl_lt_le_incl Hto).
}
apply (rngl_leb_gt_iff Hto) in Hzc2.
change_angle_opp θ2.
progress sin_cos_opp_hyp T Hzs2.
progress sin_cos_opp_hyp T Hzc2.
progress sin_cos_opp_hyp T Hzs12.
progress sin_cos_opp_hyp T H12.
apply rngl_nlt_ge in H12.
apply H12; clear H12.
rewrite rngl_cos_sub_comm.
apply rngl_cos_lt_cos_sub; try easy.
now apply (rngl_lt_le_incl Hto).
apply quadrant_1_sin_sub_nonneg_cos_le; try easy.
now apply (rngl_lt_le_incl Hto).
now apply (rngl_lt_le_incl Hto).
now apply (rngl_lt_le_incl Hto).
now apply (rngl_lt_le_incl Hto).
Qed.

Theorem angle_add_overflow_le :
  ∀ θ1 θ2 θ3,
  (θ3 ≤ θ2)%A
  → angle_add_overflow θ1 θ2 = false
  → angle_add_overflow θ1 θ3 = false.
Proof.
destruct_ac.
destruct (Nat.eq_dec (rngl_characteristic T) 1) as [Hc1| Hc1]. {
  specialize (rngl_characteristic_1 Hos Hc1) as H1.
  intros * H32 H12.
  rewrite <- angle_add_overflow_equiv2.
  progress unfold angle_add_overflow2.
  progress unfold angle_ltb.
  rewrite (H1 (rngl_sin θ1)).
  rewrite (rngl_leb_refl Hor).
  rewrite (H1 (rngl_sin (θ1 + θ3))).
  rewrite (rngl_leb_refl Hor).
  apply rngl_ltb_ge.
  rewrite H1.
  rewrite (H1 (rngl_cos _)).
  apply (rngl_le_refl Hor).
}
intros * H32 H12.
generalize H12; intros Haov.
rewrite <- angle_add_overflow_equiv2 in H12 |-*.
progress unfold angle_add_overflow2 in H12.
progress unfold angle_add_overflow2.
progress unfold angle_leb in H32.
progress unfold angle_ltb in H12.
progress unfold angle_ltb.
remember (0 ≤? rngl_sin θ1)%L as zs1 eqn:Hzs1.
remember (0 ≤? rngl_sin θ2)%L as zs2 eqn:Hzs2.
remember (0 ≤? rngl_sin θ3)%L as zs3 eqn:Hzs3.
remember (0 ≤? rngl_sin (θ1 + θ2))%L as zs12 eqn:Hzs12.
remember (0 ≤? rngl_sin (θ1 + θ3))%L as zs13 eqn:Hzs13.
symmetry in Hzs1, Hzs2, Hzs3, Hzs12, Hzs13.
move Hzs1 after Hzs2.
move Hzs12 before Hzs3; move Hzs13 before Hzs12.
destruct zs1. {
  apply rngl_leb_le in Hzs1.
  destruct zs13; [ | easy ].
  apply rngl_leb_le in Hzs13.
  apply rngl_ltb_ge.
  destruct zs3. {
    apply rngl_leb_le in Hzs3.
    destruct zs2. {
      apply rngl_leb_le in Hzs2.
      apply rngl_leb_le in H32.
      destruct zs12. {
        apply rngl_leb_le in Hzs12.
        apply (rngl_ltb_ge_iff Hto) in H12.
        now apply angle_add_overflow_le_lemma_1 with (θ2 := θ2).
      } {
        clear H12.
        apply (rngl_leb_gt_iff Hto) in Hzs12.
        now apply angle_add_overflow_le_lemma_3 with (θ2 := θ2).
      }
    } {
      clear H32.
      destruct zs12. {
        exfalso.
        apply rngl_leb_le in Hzs12.
        apply (rngl_ltb_ge_iff Hto) in H12.
        apply (rngl_leb_gt_iff Hto) in Hzs2.
        clear - Hzs12 H12 Hzs2 Hor ac Hzs1 Haov.
        apply rngl_nle_gt in Hzs2.
        apply Hzs2; clear Hzs2.
        specialize (rngl_sin_nonneg_add_nonneg θ1 θ2 Hzs1 Hzs12) as H1.
        now rewrite Haov in H1.
      }
      clear H12.
      apply (rngl_leb_gt_iff Hto) in Hzs2, Hzs12.
      now apply angle_add_overflow_le_lemma_4 with (θ2 := θ2).
    }
  } {
    exfalso.
    apply (rngl_leb_gt_iff Hto) in Hzs3.
    destruct zs2; [ easy | ].
    apply  (rngl_leb_gt_iff Hto) in Hzs2.
    apply rngl_leb_le in H32.
    destruct zs12. {
      apply rngl_leb_le in Hzs12.
      apply (rngl_ltb_ge_iff Hto) in H12.
      now apply angle_add_overflow_le_lemma_6 in H12.
    }
    clear H12.
    apply (rngl_leb_gt_iff Hto) in Hzs12.
    now apply (angle_add_overflow_le_lemma_8 θ1 θ2 θ3).
  }
}
destruct zs12; [ easy | ].
apply (rngl_leb_gt_iff Hto) in Hzs1, Hzs12.
apply (rngl_ltb_ge_iff Hto) in H12.
destruct zs13. {
  exfalso.
  apply rngl_leb_le in Hzs13.
  destruct zs2. {
    apply rngl_leb_le in Hzs2.
    destruct zs3; [ | easy ].
    apply rngl_leb_le in Hzs3, H32.
    now apply (angle_add_overflow_le_lemma_9 θ1 θ2 θ3).
  } {
    apply (rngl_leb_gt_iff Hto) in Hzs2.
    specialize angle_add_overflow_le_lemma_10 as H1.
    apply (H1 θ1 θ2 Hzs1 Hzs2 Hzs12 H12).
  }
}
apply (rngl_leb_gt_iff Hto) in Hzs13.
apply rngl_ltb_ge.
destruct zs3. {
  apply rngl_leb_le in Hzs3.
  apply (rngl_lt_le_incl Hto) in Hzs1.
  now apply rngl_cos_le_cos_add.
}
destruct zs2; [ easy | ].
apply (rngl_leb_gt_iff Hto) in Hzs2, Hzs3.
apply rngl_leb_le in H32.
apply angle_add_overflow_le_lemma_10 in H12; try easy.
Qed.

End a.
