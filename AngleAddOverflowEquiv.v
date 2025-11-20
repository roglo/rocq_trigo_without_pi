(* equivalent definition of angle_add_overflow *)

Require Import Stdlib.Arith.Arith.
Require Import RingLike.Utf8.

Require Import RingLike.Core.
Require Import Angle AngleDef.
Require Import Order.
Require Import TacChangeAngle.

Section a.

Context {T : Type}.
Context {ro : ring_like_op T}.
Context {rp : ring_like_prop T}.
Context {ac : angle_ctx T}.

Definition angle_add_overflow2 θ1 θ2 := (θ1 + θ2 <? θ1)%A.

Theorem rngl_cos_add_le_cos :
  ∀ θ1 θ2,
  (θ1 ≠ π ∨ θ2 ≠ π ∨ 0 ≤ rngl_cos θ1 ∨ 0 ≤ rngl_cos θ2)%L
  → (0 ≤ rngl_sin θ1)%L
  → (0 ≤ rngl_sin θ2)%L
  → (0 ≤ rngl_sin (θ1 + θ2))%L
  → (rngl_cos (θ1 + θ2) ≤ rngl_cos θ1)%L.
Proof.
destruct_ac.
intros * H12 Hzs1 Hzs2 Hzs12.
rewrite <- or_assoc in H12.
rewrite or_comm in H12.
rewrite or_assoc in H12.
destruct H12 as [H12| H12]. {
  cbn.
  apply (rngl_le_sub_le_add_l Hop Hto).
  apply (rngl_le_0_sub Hop Hto).
  rewrite <- (rngl_add_sub_assoc Hop).
  rewrite (rngl_sub_mul_r_diag_l Hop).
  apply (rngl_le_0_add Hos Hto).
  now apply (rngl_mul_nonneg_nonneg Hos Hor).
  apply (rngl_mul_nonneg_nonneg Hos Hor); [ easy | ].
  apply (rngl_le_0_sub Hop Hto).
  apply rngl_cos_bound.
}
destruct (rngl_leb_dec 0 (rngl_cos θ1)) as [Hzc1| Hc1z]. {
  apply rngl_leb_le in Hzc1.
  cbn.
  apply (rngl_le_sub_le_add_l Hop Hto).
  apply (rngl_le_0_sub Hop Hto).
  rewrite <- (rngl_add_sub_assoc Hop).
  rewrite (rngl_sub_mul_r_diag_l Hop).
  apply (rngl_le_0_add Hos Hto).
  now apply (rngl_mul_nonneg_nonneg Hos Hor).
  apply (rngl_mul_nonneg_nonneg Hos Hor); [ easy | ].
  apply (rngl_le_0_sub Hop Hto).
  apply rngl_cos_bound.
}
apply (rngl_leb_gt_iff Hto) in Hc1z.
destruct (rngl_leb_dec 0 (rngl_cos θ2)) as [Hzc2| Hc2z]. {
  apply rngl_leb_le in Hzc2.
  remember (θ1 - π/₂)%A as θ' eqn:Hθ'.
  apply angle_add_move_r in Hθ'.
  subst θ1; rename θ' into θ1.
  rewrite angle_add_add_swap in Hzs12 |-*.
  rewrite rngl_cos_add_right_r in Hc1z.
  apply (rngl_opp_neg_pos Hop Hto) in Hc1z.
  rewrite rngl_sin_add_right_r in Hzs1, Hzs12.
  do 2 rewrite rngl_cos_add_right_r.
  apply -> (rngl_opp_le_compat Hop Hto).
  apply (rngl_lt_le_incl Hto) in Hc1z.
  apply rngl_cos_cos_sin_sin_nonneg_sin_le_cos_le_iff; try easy.
  now apply rngl_sin_add_nonneg.
  cbn.
  apply (rngl_le_sub_le_add_l Hop Hto).
  apply (rngl_le_0_sub Hop Hto).
  rewrite <- (rngl_add_sub_assoc Hop).
  rewrite (rngl_sub_mul_r_diag_l Hop).
  apply (rngl_le_0_add Hos Hto).
  now apply (rngl_mul_nonneg_nonneg Hos Hor).
  apply (rngl_mul_nonneg_nonneg Hos Hor); [ easy | ].
  apply (rngl_le_0_sub Hop Hto).
  apply rngl_cos_bound.
}
apply rngl_leb_nle in Hc2z.
destruct H12 as [H12| H12]; [ easy | ].
apply (rngl_nle_gt_iff Hto) in Hc2z.
destruct (rngl_eqb_dec (rngl_sin θ1) 0) as [Hs1z| Hs1z]. {
  apply (rngl_eqb_eq Heo) in Hs1z.
  apply eq_rngl_sin_0 in Hs1z.
  destruct Hs1z; subst θ1. {
    rewrite angle_add_0_l.
    apply rngl_cos_bound.
  }
  destruct H12 as [H12| H12]; [ easy | ].
  rewrite rngl_sin_add_straight_l in Hzs12.
  apply (rngl_opp_nonneg_nonpos Hop Hto) in Hzs12.
  apply (rngl_le_antisymm Hor) in Hzs12; [ | easy ].
  symmetry in Hzs12.
  apply eq_rngl_sin_0 in Hzs12.
  destruct Hzs12; subst θ2; [ | easy ].
  rewrite angle_add_0_r.
  apply (rngl_le_refl Hor).
}
apply (rngl_eqb_neq Heo) in Hs1z.
exfalso.
apply (rngl_nlt_ge Hor) in Hzs12.
apply Hzs12; clear Hzs12.
cbn.
apply (rngl_add_neg_nonpos Hop Hto). {
  apply (rngl_mul_pos_neg Hop Hiq Hto); [ | easy ].
  apply not_eq_sym in Hs1z.
  now apply (rngl_le_neq Hto).
} {
  apply (rngl_mul_nonpos_nonneg Hop Hto); [ | easy ].
  now apply (rngl_lt_le_incl Hto).
}
Qed.

Theorem quadrant_1_quadrant_4_cos_lt_cos_add :
  ∀ θ1 θ2,
  (0 ≤ rngl_sin θ1)%L
  → (0 ≤ rngl_cos θ1)%L
  → (rngl_sin θ2 < 0)%L
  → (0 ≤ rngl_cos θ2)%L
  → (0 ≤ rngl_sin (θ1 + θ2))%L
  → (rngl_cos θ1 < rngl_cos (θ1 + θ2))%L.
Proof.
destruct_ac.
intros * Hzs1 Hzc1 Hzs2 Hzc2 Hzs12.
change_angle_opp θ2.
progress sin_cos_opp_hyp T Hzs2.
progress sin_cos_opp_hyp T Hzs12.
progress sin_cos_opp_hyp T Hzc2.
progress sin_cos_opp_goal T.
rewrite rngl_cos_sub_comm.
apply rngl_cos_lt_cos_sub; [ easy | easy | ].
apply (rngl_lt_le_incl Hto) in Hzs2.
now apply quadrant_1_sin_sub_nonneg_cos_le.
Qed.

Theorem quadrant_1_rngl_cos_add_le_cos_l :
  ∀ θ1 θ2,
  (0 ≤ rngl_sin θ1)%L
  → (0 ≤ rngl_sin θ2)%L
  → (0 ≤ rngl_cos θ1)%L
  → (0 ≤ rngl_cos θ2)%L
  → (rngl_cos (θ1 + θ2) ≤ rngl_cos θ1)%L.
Proof.
destruct_ac.
intros * Hzs1 Hzs2 Hzc1 Hzc2.
apply rngl_cos_add_le_cos; try easy.
now right; right; left.
cbn.
apply (rngl_le_0_add Hos Hto).
now apply (rngl_mul_nonneg_nonneg Hos Hor).
now apply (rngl_mul_nonneg_nonneg Hos Hor).
Qed.

Theorem rngl_cos_sub_nonneg :
  ∀ θ1 θ2 : angle T,
  (0 ≤ rngl_sin θ1)%L
  → (0 ≤ rngl_sin θ2)%L
  → (0 ≤ rngl_cos θ1)%L
  → (0 ≤ rngl_cos θ2)%L
  → (0 ≤ rngl_cos (θ1 - θ2))%L.
Proof.
destruct_ac.
intros * Hzs1 Hzs2 Hcs1 Hcs2.
cbn.
rewrite (rngl_mul_opp_r Hop).
rewrite (rngl_sub_opp_r Hop).
apply (rngl_le_0_add Hos Hto).
now apply (rngl_mul_nonneg_nonneg Hos Hor).
now apply (rngl_mul_nonneg_nonneg Hos Hor).
Qed.

Theorem quadrant_1_sin_sub_pos_cos_lt :
  ∀ θ1 θ2,
  (0 ≤ rngl_sin θ1)%L
  → (0 ≤ rngl_sin θ2)%L
  → (0 ≤ rngl_cos θ2)%L
  → (0 < rngl_sin (θ1 - θ2))%L
  → (rngl_cos θ1 < rngl_cos θ2)%L.
Proof.
destruct_ac.
intros * Hs1z Hzs2 Hzc2 Hzs12.
apply (rngl_le_neq Hto).
split. {
  apply quadrant_1_sin_sub_nonneg_cos_le; try easy.
  now apply (rngl_lt_le_incl Hto).
}
intros H.
apply rngl_cos_eq in H.
destruct H; subst θ1. {
  rewrite angle_sub_diag in Hzs12.
  now apply (rngl_lt_irrefl Hor) in Hzs12.
}
cbn in Hs1z.
rewrite <- angle_opp_add_distr in Hzs12.
cbn - [ angle_add ] in Hzs12.
apply (rngl_opp_nonneg_nonpos Hop Hto) in Hs1z.
apply (rngl_le_antisymm Hor) in Hzs2; [ | easy ].
apply eq_rngl_sin_0 in Hzs2.
destruct Hzs2; subst θ2. {
  rewrite angle_add_0_r in Hzs12.
  cbn in Hzs12.
  rewrite (rngl_opp_0 Hop) in Hzs12.
  now apply (rngl_lt_irrefl Hor) in Hzs12.
}
rewrite angle_straight_add_straight in Hzs12.
cbn in Hzs12.
rewrite (rngl_opp_0 Hop) in Hzs12.
now apply (rngl_lt_irrefl Hor) in Hzs12.
Qed.

Theorem angle_add_overflow_equiv2 :
  ∀ θ1 θ2,
  angle_add_overflow2 θ1 θ2 = angle_add_overflow θ1 θ2.
Proof.
destruct_ac.
destruct (Nat.eq_dec (rngl_characteristic T) 1) as [Hc1| Hc1]. {
  specialize (rngl_characteristic_1_angle_0 Hc1) as H1.
  intros.
  rewrite (H1 θ1), (H1 θ2).
  rewrite angle_add_overflow_0_l.
  progress unfold angle_add_overflow2.
  rewrite angle_add_0_l.
  apply Bool.not_true_iff_false.
  apply angle_lt_irrefl.
}
intros.
progress unfold angle_add_overflow2.
progress unfold angle_add_overflow.
remember (θ1 =? 0)%A as z1 eqn:Hz1.
symmetry in Hz1.
destruct z1. {
  cbn.
  apply angle_eqb_eq in Hz1.
  subst θ1.
  rewrite angle_add_0_l.
  apply Bool.not_true_iff_false.
  apply angle_nlt_ge.
  apply angle_nonneg.
}
apply angle_eqb_neq in Hz1.
progress unfold angle_ltb.
progress unfold angle_leb.
cbn - [ angle_add ].
rewrite (rngl_leb_opp_r Hop Hto).
rewrite (rngl_opp_0 Hop).
remember (0 ≤? rngl_sin θ1)%L as zs1 eqn:Hzs1.
remember (rngl_sin θ1 ≤? 0)%L as s1z eqn:Hs1z.
symmetry in Hzs1, Hs1z.
move s1z before zs1.
destruct zs1. {
  destruct s1z. {
    apply rngl_leb_le in Hzs1, Hs1z.
    apply (rngl_le_antisymm Hor) in Hzs1; [ clear Hs1z | easy ].
    apply eq_rngl_sin_0 in Hzs1.
    destruct Hzs1; [ easy | subst θ1 ].
    clear Hz1.
    rewrite rngl_sin_add_straight_l.
    rewrite rngl_cos_add_straight_l.
    cbn.
    rewrite (rngl_leb_opp_r Hop Hto).
    rewrite (rngl_opp_0 Hop).
    remember (0 ≤? rngl_sin θ2)%L as zs2 eqn:Hzs2.
    remember (rngl_sin θ2 ≤? 0)%L as s2z eqn:Hs2z.
    symmetry in Hzs2, Hs2z.
    move s2z before zs2.
    destruct zs2. {
      destruct s2z. {
        apply rngl_leb_le in Hzs2, Hs2z.
        apply (rngl_le_antisymm Hor) in Hzs2; [ clear Hs2z | easy ].
        apply eq_rngl_sin_0 in Hzs2.
        destruct Hzs2; subst θ2; cbn. {
          transitivity false. {
            apply rngl_ltb_ge.
            apply (rngl_le_refl Hor).
          } {
            symmetry.
            apply (rngl_leb_gt_iff Hto).
            apply (rngl_opp_1_lt_1 Hop Hto Hc1).
          }
        }
        cbn.
        rewrite (rngl_opp_involutive Hop).
        transitivity true. {
          apply (rngl_ltb_lt Heo).
          apply (rngl_opp_1_lt_1 Hop Hto Hc1).
        } {
          symmetry.
          apply rngl_leb_le.
          apply (rngl_le_refl Hor).
        }
      }
      symmetry.
      apply (rngl_leb_gt_iff Hto).
      apply (rngl_le_neq Hto).
      split; [ apply rngl_cos_bound | ].
      intros H; symmetry in H.
      apply eq_rngl_cos_opp_1 in H; subst θ2.
      cbn in Hs2z, Hzs2.
      now rewrite Hs2z in Hzs2.
    }
    destruct s2z. {
      apply (rngl_ltb_lt Heo).
      apply (rngl_opp_lt_compat Hop Hto).
      do 2 rewrite (rngl_opp_involutive Hop).
      apply (rngl_le_neq Hto).
      split; [ apply rngl_cos_bound | ].
      intros H.
      apply eq_rngl_cos_1 in H; subst θ2.
      cbn in Hs2z, Hzs2.
      now rewrite Hs2z in Hzs2.
    }
    exfalso.
    apply (rngl_leb_gt_iff Hto) in Hzs2, Hs2z.
    now apply (rngl_lt_asymm Hto) in Hzs2.
  }
  remember (0 ≤? rngl_sin (θ1 + θ2))%L as zs12 eqn:Hzs12.
  remember (0 ≤? rngl_sin θ2)%L as zs2 eqn:Hzs2.
  symmetry in Hzs12, Hzs2.
  destruct zs12. {
    destruct zs2. {
      apply rngl_leb_le in Hzs1, Hzs2, Hzs12.
      apply (rngl_leb_gt_iff Hto) in Hs1z.
      apply rngl_ltb_ge.
      apply rngl_cos_add_le_cos; [ | easy | easy | easy ].
      left.
      intros H; subst θ1.
      cbn in Hs1z.
      now apply (rngl_lt_irrefl Hor) in Hs1z.
    }
    apply rngl_leb_le in Hzs1, Hzs12.
    apply (rngl_leb_gt_iff Hto) in Hs1z, Hzs2.
    destruct (rngl_leb_dec 0 (rngl_cos θ1)) as [Hzc1| Hzc1]. {
      apply rngl_leb_le in Hzc1.
      remember (rngl_cos θ1 ≤? rngl_cos θ2)%L as c12 eqn:Hc12.
      symmetry in Hc12.
      destruct c12. {
        apply rngl_leb_le in Hc12.
        apply (rngl_ltb_lt Heo).
        apply quadrant_1_quadrant_4_cos_lt_cos_add; try easy.
        now apply (rngl_le_trans Hor _ (rngl_cos θ1)).
      }
      apply (rngl_leb_gt_iff Hto) in Hc12.
      apply rngl_ltb_ge.
      destruct (rngl_leb_dec 0 (rngl_cos θ2)) as [Hzc2| Hzc2]. {
        apply rngl_leb_le in Hzc2.
        exfalso.
        change_angle_opp θ2.
        progress sin_cos_opp_hyp T Hzs2.
        progress sin_cos_opp_hyp T Hzs12.
        progress sin_cos_opp_hyp T Hc12.
        progress sin_cos_opp_hyp T Hzc2.
        apply rngl_nle_gt in Hc12.
        apply Hc12; clear Hc12.
        apply quadrant_1_sin_sub_nonneg_cos_le; try easy.
        now apply (rngl_lt_le_incl Hto) in Hzs2.
      }
      exfalso.
      apply (rngl_leb_gt_iff Hto) in Hzc2.
      change_angle_add_r θ2 π.
      progress sin_cos_add_sub_straight_hyp T Hzs2.
      progress sin_cos_add_sub_straight_hyp T Hzs12.
      progress sin_cos_add_sub_straight_hyp T Hc12.
      progress sin_cos_add_sub_straight_hyp T Hzc2.
      apply (rngl_nlt_ge Hor) in Hzs12.
      apply Hzs12; clear Hzs12.
      cbn.
      apply (rngl_lt_0_add Hos Hto).
      now apply (rngl_mul_pos_pos Hop Hiq Hto).
      apply (rngl_lt_le_incl Hto) in Hzs2.
      now apply (rngl_mul_nonneg_nonneg Hos Hor).
    }
    remember (rngl_cos θ1 ≤? rngl_cos θ2)%L as c12 eqn:Hc12.
    symmetry in Hc12.
    destruct c12. {
      apply rngl_leb_le in Hc12.
      apply (rngl_ltb_lt Heo).
      apply (rngl_leb_gt_iff Hto) in Hzc1.
      change_angle_sub_l θ1 π.
      progress sin_cos_add_sub_straight_hyp T Hzs12.
      progress sin_cos_add_sub_straight_hyp T Hs1z.
      progress sin_cos_add_sub_straight_hyp T Hzs1.
      progress sin_cos_add_sub_straight_hyp T Hc12.
      progress sin_cos_add_sub_straight_hyp T Hzc1.
      progress sin_cos_add_sub_straight_goal T.
      rewrite (rngl_add_opp_r Hop).
      apply (rngl_lt_0_sub Hop Hto).
      destruct (rngl_leb_dec 0 (rngl_cos θ2)) as [Hzc2| Hzc2]. {
        apply rngl_leb_le in Hzc2.
        change_angle_opp θ2.
        progress sin_cos_opp_hyp T Hzs2.
        progress sin_cos_opp_hyp T Hc12.
        progress sin_cos_opp_hyp T Hzc2.
        rewrite angle_sub_opp_r in Hzs12 |-*.
        apply (rngl_le_neq Hto).
        split. {
          apply (rngl_lt_le_incl Hto) in Hzs2, Hzc1.
          now apply quadrant_1_rngl_cos_add_le_cos_l.
        }
        intros H.
        apply rngl_cos_eq in H.
        destruct H as [H1| H1]. {
          apply angle_add_move_l in H1.
          rewrite angle_sub_diag in H1; subst θ2.
          cbn in Hzs2.
          now apply (rngl_lt_irrefl Hor) in Hzs2.
        }
        rewrite H1 in Hzs12; cbn in Hzs12.
        apply (rngl_opp_nonneg_nonpos Hop Hto) in Hzs12.
        now apply (rngl_nlt_ge Hor) in Hzs12.
      }
      apply (rngl_leb_gt_iff Hto) in Hzc2.
      change_angle_add_r θ2 π.
      rewrite angle_sub_sub_distr in Hzs12 |-*.
      progress sin_cos_add_sub_straight_hyp T Hzs12.
      progress sin_cos_add_sub_straight_hyp T Hc12.
      progress sin_cos_add_sub_straight_hyp T Hzs2.
      progress sin_cos_add_sub_straight_hyp T Hzc2.
      progress sin_cos_add_sub_straight_goal T.
      apply (rngl_add_nonneg_pos Hos Hto); [ | easy ].
      apply (rngl_lt_le_incl Hto) in Hzs2, Hzc1, Hzc2.
      now apply rngl_cos_sub_nonneg.
    }
    exfalso.
    apply (rngl_leb_gt_iff Hto) in Hzc1.
    apply (rngl_leb_gt_iff Hto) in Hc12.
    change_angle_sub_r θ1 π/₂.
    progress sin_cos_add_sub_right_hyp T Hzs12.
    progress sin_cos_add_sub_right_hyp T Hs1z.
    progress sin_cos_add_sub_right_hyp T Hzs1.
    progress sin_cos_add_sub_right_hyp T Hc12.
    progress sin_cos_add_sub_right_hyp T Hzc1.
    change_angle_add_r θ2 π.
    progress sin_cos_add_sub_straight_hyp T Hzs12.
    progress sin_cos_add_sub_straight_hyp T Hc12.
    progress sin_cos_add_sub_straight_hyp T Hzs2.
    change_angle_sub_l θ2 π/₂.
    progress sin_cos_add_sub_right_hyp T Hzs12.
    progress sin_cos_add_sub_right_hyp T Hc12.
    progress sin_cos_add_sub_right_hyp T Hzs2.
    apply rngl_nle_gt in Hc12.
    apply Hc12; clear Hc12.
    apply (rngl_lt_le_incl Hto) in Hzc1.
    now apply rngl_sin_sub_nonneg_sin_le_sin.
  }
  destruct zs2; [ easy | symmetry ].
  apply rngl_leb_le in Hzs1.
  apply (rngl_leb_gt_iff Hto) in Hs1z, Hzs12, Hzs2.
  apply (rngl_leb_gt_iff Hto).
  destruct (rngl_leb_dec 0 (rngl_cos θ1)) as [Hzc1| Hzc1]. {
    apply rngl_leb_le in Hzc1.
    destruct (rngl_leb_dec 0 (rngl_cos θ2)) as [Hzc2| Hzc2]. {
      apply rngl_leb_le in Hzc2.
      change_angle_opp θ2.
      progress sin_cos_opp_hyp T Hzs2.
      progress sin_cos_opp_hyp T Hzs12.
      progress sin_cos_opp_hyp T Hzc2.
      cbn.
      rewrite rngl_sin_sub_anticomm in Hzs12.
      apply (rngl_opp_neg_pos Hop Hto) in Hzs12.
      apply (rngl_lt_le_incl Hto) in Hzs2.
      now apply quadrant_1_sin_sub_pos_cos_lt.
    }
    apply (rngl_leb_gt_iff Hto) in Hzc2.
    now apply (rngl_lt_le_trans Hto _ 0).
  }
  apply (rngl_leb_gt_iff Hto) in Hzc1.
  change_angle_sub_r θ1 π/₂.
  progress sin_cos_add_sub_right_hyp T Hzs12.
  progress sin_cos_add_sub_right_hyp T Hs1z.
  progress sin_cos_add_sub_right_hyp T Hzs1.
  progress sin_cos_add_sub_right_hyp T Hzc1.
  progress sin_cos_add_sub_right_goal T.
  destruct (rngl_leb_dec 0 (rngl_cos θ2)) as [Hzc2| Hzc2]. {
    apply rngl_leb_le in Hzc2.
    exfalso.
    change_angle_opp θ2.
    progress sin_cos_opp_hyp T Hzs2.
    progress sin_cos_opp_hyp T Hzs12.
    progress sin_cos_opp_hyp T Hzc2.
    apply (rngl_nle_gt_iff Hto) in Hzs12.
    apply Hzs12; clear Hzs12.
    apply (rngl_lt_le_incl Hto) in Hzc1, Hzs2.
    now apply rngl_cos_sub_nonneg.
  }
  apply (rngl_leb_gt_iff Hto) in Hzc2.
  change_angle_add_r θ2 π.
  progress sin_cos_add_sub_straight_hyp T Hzs12.
  progress sin_cos_add_sub_straight_hyp T Hzs2.
  progress sin_cos_add_sub_straight_hyp T Hzc2.
  progress sin_cos_add_sub_straight_goal T.
  rewrite (rngl_add_opp_r Hop).
  change_angle_sub_l θ2 π/₂.
  progress sin_cos_add_sub_right_hyp T Hzs12.
  progress sin_cos_add_sub_right_hyp T Hzs2.
  progress sin_cos_add_sub_right_hyp T Hzc2.
  progress sin_cos_add_sub_right_goal T.
  rewrite rngl_sin_sub_anticomm in Hzs12.
  apply (rngl_opp_neg_pos Hop Hto) in Hzs12.
  apply (rngl_le_neq Hto).
  split. {
    apply (rngl_lt_le_incl Hto) in Hzc2, Hzs2, Hzs12.
    now apply rngl_sin_sub_nonneg_sin_le_sin.
  }
  intros H12.
  apply rngl_sin_eq in H12.
  destruct H12; subst θ1. {
    rewrite angle_sub_diag in Hzs12.
    now apply (rngl_lt_irrefl Hor) in Hzs12.
  }
  rewrite rngl_cos_sub_straight_l in Hzs1.
  apply (rngl_opp_nonneg_nonpos Hop Hto) in Hzs1.
  now apply (rngl_nlt_ge Hor) in Hzs1.
}
destruct s1z. {
  remember (0 ≤? rngl_sin (θ1 + θ2))%L as zs12 eqn:Hzs12.
  remember (0 ≤? rngl_sin θ2)%L as s2z eqn:Hs2z.
  symmetry in Hzs12, Hs2z.
  destruct zs12. {
    destruct s2z; [ symmetry | easy ].
    apply (rngl_leb_gt_iff Hto) in Hzs1.
    apply rngl_leb_le in Hzs12, Hs2z, Hs1z.
    apply rngl_leb_le.
    destruct (rngl_leb_dec 0 (rngl_cos θ1)) as [Hzc1| Hzc1]. {
      change_angle_opp θ1.
      progress sin_cos_opp_hyp T Hs1z.
      progress sin_cos_opp_hyp T Hzs1.
      progress sin_cos_opp_hyp T Hzc1.
      cbn.
      rewrite angle_add_opp_l in Hzs12.
      rewrite rngl_sin_sub_anticomm in Hzs12.
      apply (rngl_opp_nonneg_nonpos Hop Hto) in Hzs12.
      apply (rngl_nlt_ge Hor) in Hzs12.
      apply (rngl_nlt_ge_iff Hto).
      intros H12.
      apply Hzs12; clear Hzs12.
      apply (rngl_le_neq Hto).
      split. {
        apply (rngl_lt_le_incl Hto) in Hzs1, H12.
        now apply rngl_sin_sub_nonneg.
      }
      intros H; symmetry in H.
      apply eq_rngl_sin_0 in H.
      destruct H as [H1| H1]. {
        apply -> angle_sub_move_0_r in H1; subst θ2.
        now apply (rngl_lt_irrefl Hor) in H12.
      }
      apply angle_sub_move_r in H1; subst θ1.
      rewrite rngl_sin_add_straight_l in Hzs1.
      apply (rngl_opp_pos_neg Hop Hto) in Hzs1.
      now apply rngl_nle_gt in Hzs1.
    }
    apply (rngl_leb_gt_iff Hto) in Hzc1.
    change_angle_add_r θ1 π.
    progress sin_cos_add_sub_straight_hyp T Hzs12.
    progress sin_cos_add_sub_straight_hyp T Hs1z.
    progress sin_cos_add_sub_straight_hyp T Hzs1.
    progress sin_cos_add_sub_straight_hyp T Hzc1.
    progress sin_cos_add_sub_straight_goal T.
    destruct (rngl_leb_dec 0 (rngl_cos θ2)) as [Hzc2| Hzc2]. {
      apply rngl_leb_le in Hzc2.
      apply (rngl_nlt_ge_iff Hto).
      intros Hc21.
      apply (rngl_nlt_ge Hor) in Hzs12.
      apply Hzs12; clear Hzs12.
      apply (rngl_le_neq Hto).
      split. {
        apply (rngl_lt_le_incl Hto) in Hzc1.
        now apply rngl_sin_add_nonneg.
      }
      intros H; symmetry in H.
      apply eq_rngl_sin_0 in H.
      destruct H as [H1| H1]. {
        apply -> angle_add_move_0_r in H1; subst θ1.
        apply (rngl_opp_pos_neg Hop Hto) in Hzs1.
        now apply rngl_nle_gt in Hzs1.
      }
      apply angle_add_move_r in H1; subst θ1.
      rewrite rngl_cos_sub_straight_l in Hzc1.
      apply (rngl_opp_pos_neg Hop Hto) in Hzc1.
      now apply rngl_nle_gt in Hzc1.
    }
    apply (rngl_leb_gt_iff Hto) in Hzc2.
    change_angle_sub_l θ2 π.
    progress sin_cos_add_sub_straight_hyp T Hzs12.
    progress sin_cos_add_sub_straight_hyp T Hs2z.
    progress sin_cos_add_sub_straight_hyp T Hzc2.
    progress sin_cos_add_sub_straight_goal T.
    rewrite (rngl_add_opp_l Hop).
    apply (rngl_le_sub_0 Hop Hto).
    apply (rngl_lt_eq_cases Hto).
    destruct (rngl_eqb_dec (rngl_cos θ1) (rngl_cos θ2)) as [Hc12| Hc12]. {
      apply (rngl_eqb_eq Heo) in Hc12.
      now right.
    }
    apply (rngl_eqb_neq Heo) in Hc12.
    left.
    apply (rngl_lt_le_incl Hto) in Hzc1, Hzc2.
    apply quadrant_1_sin_sub_pos_cos_lt; try easy.
    apply (rngl_le_neq Hto).
    split; [ easy | ].
    intros H; symmetry in H.
    apply eq_rngl_sin_0 in H.
    destruct H as [H1| H1]. {
      now apply -> angle_sub_move_0_r in H1; subst θ2.
    }
    apply angle_sub_move_r in H1; subst θ1.
    rewrite rngl_sin_add_straight_l in Hzs1.
    apply (rngl_opp_pos_neg Hop Hto) in Hzs1.
    now apply rngl_nle_gt in Hzs1.
  }
  destruct s2z. {
    remember (rngl_cos θ2 ≤? rngl_cos θ1)%L as c21 eqn:Hc21.
    symmetry in Hc21.
    destruct c21. {
      apply rngl_leb_le in Hs1z, Hs2z, Hc21.
      apply (rngl_leb_gt_iff Hto) in Hzs1, Hzs12.
      apply (rngl_ltb_lt Heo).
      destruct (rngl_leb_dec 0 (rngl_cos θ1)) as [Hzc1| Hzc1]. {
        apply rngl_leb_le in Hzc1.
        change_angle_opp θ1.
        progress sin_cos_opp_hyp T Hs1z.
        progress sin_cos_opp_hyp T Hzs1.
        progress sin_cos_opp_hyp T Hzc1.
        progress sin_cos_opp_hyp T Hc21.
        rewrite angle_add_opp_l in Hzs12.
        rewrite angle_add_opp_l, rngl_cos_opp.
        destruct (rngl_leb_dec 0 (rngl_cos θ2)) as [Hzc2| Hzc2]. {
          apply (rngl_nle_gt_iff Hto).
          intros Hc121.
          apply rngl_nle_gt in Hzs12.
          apply Hzs12; clear Hzs12.
          apply (rngl_lt_le_incl Hto) in Hzs1.
          now apply rngl_sin_sub_nonneg.
        }
        exfalso.
        apply (rngl_leb_gt_iff Hto) in Hzc2.
        change_angle_sub_l θ2 π.
        rewrite <- angle_sub_add_distr in Hzs12.
        progress sin_cos_add_sub_straight_hyp T Hzs12.
        progress sin_cos_add_sub_straight_hyp T Hs2z.
        progress sin_cos_add_sub_straight_hyp T Hzc2.
        progress sin_cos_add_sub_straight_hyp T Hc21.
        apply rngl_nle_gt in Hzs12.
        apply Hzs12; clear Hzs12.
        apply (rngl_lt_le_incl Hto) in Hzs1, Hzc2.
        now apply rngl_sin_add_nonneg.
      }
      exfalso.
      apply (rngl_leb_gt_iff Hto) in Hzc1.
      change_angle_add_r θ1 π.
      progress sin_cos_add_sub_straight_hyp T Hzs12.
      progress sin_cos_add_sub_straight_hyp T Hs1z.
      progress sin_cos_add_sub_straight_hyp T Hzs1.
      progress sin_cos_add_sub_straight_hyp T Hzc1.
      progress sin_cos_add_sub_straight_hyp T Hc21.
      change_angle_sub_l θ2 π.
      progress sin_cos_add_sub_straight_hyp T Hzs12.
      progress sin_cos_add_sub_straight_hyp T Hs2z.
      progress sin_cos_add_sub_straight_hyp T Hc21.
      apply -> (rngl_le_sub_0 Hop Hto) in Hc21.
      apply rngl_nle_gt in Hzs12.
      apply Hzs12; clear Hzs12.
      now apply rngl_sin_sub_nonneg.
    }
    apply rngl_leb_le in Hs1z, Hs2z.
    apply (rngl_leb_gt_iff Hto) in Hzs1, Hzs12, Hc21.
    apply rngl_ltb_ge.
    destruct (rngl_leb_dec 0 (rngl_cos θ1)) as [Hzc1| Hzc1]. {
      apply rngl_leb_le in Hzc1.
      change_angle_add_r θ1 π/₂.
      progress sin_cos_add_sub_right_hyp T Hs1z.
      progress sin_cos_add_sub_right_hyp T Hzs1.
      progress sin_cos_add_sub_right_hyp T Hzc1.
      progress sin_cos_add_sub_right_hyp T Hc21.
      progress sin_cos_add_sub_right_hyp T Hzs12.
      progress sin_cos_add_sub_right_goal T.
      apply rngl_sin_sub_nonneg_sin_le_sin. {
        apply rngl_sin_add_nonneg; try easy.
        apply (rngl_lt_le_incl Hto) in Hc21.
        now apply (rngl_le_trans Hor _ (rngl_sin θ1)).
      } {
        now apply (rngl_lt_le_incl Hto) in Hzs12.
      } {
        now rewrite angle_add_comm, angle_add_sub.
      }
    }
    apply (rngl_leb_gt_iff Hto) in Hzc1.
    change_angle_add_r θ1 π.
    progress sin_cos_add_sub_straight_hyp T Hzs12.
    progress sin_cos_add_sub_straight_hyp T Hs1z.
    progress sin_cos_add_sub_straight_hyp T Hzs1.
    progress sin_cos_add_sub_straight_hyp T Hzc1.
    progress sin_cos_add_sub_straight_hyp T Hc21.
    progress sin_cos_add_sub_straight_goal T.
    apply (rngl_lt_opp_l Hop Hto) in Hc21.
    destruct (rngl_leb_dec 0 (rngl_cos θ2)) as [Hzc2| Hzc2]. {
      apply rngl_leb_le in Hzc2.
      apply (rngl_lt_le_incl Hto) in Hzc1.
      now apply quadrant_1_rngl_cos_add_le_cos_l.
    }
    apply (rngl_leb_gt_iff Hto) in Hzc2.
    change_angle_sub_l θ2 π.
    progress sin_cos_add_sub_straight_hyp T Hzs12.
    progress sin_cos_add_sub_straight_hyp T Hs2z.
    progress sin_cos_add_sub_straight_hyp T Hzc2.
    progress sin_cos_add_sub_straight_hyp T Hc21.
    progress sin_cos_add_sub_straight_goal T.
    apply (rngl_lt_le_incl Hto) in Hzc1, Hzc2.
    apply (rngl_le_0_add Hos Hto); [ | easy ].
    now apply rngl_cos_sub_nonneg.
  }
  apply rngl_leb_le in Hs1z.
  apply (rngl_leb_gt_iff Hto) in Hzs1, Hzs12, Hs2z.
  apply (rngl_ltb_lt Heo).
  destruct (rngl_leb_dec 0 (rngl_cos θ1)) as [Hzc1| Hzc1]. {
    apply rngl_leb_le in Hzc1.
    change_angle_add_r θ1 π/₂.
    progress sin_cos_add_sub_right_hyp T Hzs12.
    progress sin_cos_add_sub_right_hyp T Hs1z.
    progress sin_cos_add_sub_right_hyp T Hzs1.
    progress sin_cos_add_sub_right_hyp T Hzc1.
    progress sin_cos_add_sub_right_goal T.
    destruct (rngl_leb_dec 0 (rngl_cos θ2)) as [Hzc2| Hzc2]. {
      apply rngl_leb_le in Hzc2.
      change_angle_opp θ2.
      progress sin_cos_opp_hyp T Hzs12.
      progress sin_cos_opp_hyp T Hs2z.
      progress sin_cos_opp_hyp T Hzc2.
      progress sin_cos_opp_goal T.
      now apply rngl_sin_sub_lt_sin_l.
    }
    apply (rngl_leb_gt_iff Hto) in Hzc2.
    change_angle_add_r θ2 π.
    progress sin_cos_add_sub_straight_hyp T Hzs12.
    progress sin_cos_add_sub_straight_hyp T Hs2z.
    progress sin_cos_add_sub_straight_hyp T Hzc2.
    progress sin_cos_add_sub_straight_goal T.
    apply (rngl_lt_0_add Hos Hto); [ cbn | easy ].
    apply (rngl_add_nonneg_pos Hos Hto).
    apply (rngl_lt_le_incl Hto) in Hzc2.
    now apply (rngl_mul_nonneg_nonneg Hos Hor).
    now apply (rngl_mul_pos_pos Hop Hiq Hto).
  }
  apply (rngl_leb_gt_iff Hto) in Hzc1.
  change_angle_add_r θ1 π.
  progress sin_cos_add_sub_straight_hyp T Hzs12.
  progress sin_cos_add_sub_straight_hyp T Hs1z.
  progress sin_cos_add_sub_straight_hyp T Hzs1.
  progress sin_cos_add_sub_straight_hyp T Hzc1.
  progress sin_cos_add_sub_straight_goal T.
  rewrite (rngl_add_opp_r Hop).
  apply (rngl_lt_0_sub Hop Hto).
  destruct (rngl_leb_dec 0 (rngl_cos θ2)) as [Hzc2| Hzc2]. {
    apply rngl_leb_le in Hzc2.
    change_angle_opp θ2.
    progress sin_cos_opp_hyp T Hzs12.
    progress sin_cos_opp_hyp T Hs2z.
    progress sin_cos_opp_hyp T Hzc2.
    progress sin_cos_opp_goal T.
    rewrite rngl_cos_sub_comm.
    apply rngl_cos_lt_cos_sub; try easy.
    apply (rngl_lt_le_incl Hto) in Hs2z, Hzc1, Hzs12.
    now apply quadrant_1_sin_sub_nonneg_cos_le.
  }
  exfalso.
  apply (rngl_leb_gt_iff Hto) in Hzc2.
  change_angle_add_r θ2 π.
  progress sin_cos_add_sub_straight_hyp T Hzs12.
  progress sin_cos_add_sub_straight_hyp T Hs2z.
  progress sin_cos_add_sub_straight_hyp T Hzc2.
  apply rngl_nle_gt in Hzs12.
  apply Hzs12; clear Hzs12.
  apply (rngl_lt_le_incl Hto) in Hs2z, Hzc1, Hzc2.
  now apply rngl_sin_add_nonneg.
}
apply (rngl_leb_gt_iff Hto) in Hzs1, Hs1z.
now apply (rngl_lt_asymm Hto) in Hzs1.
Qed.

End a.
