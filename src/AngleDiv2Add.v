Set Nested Proofs Allowed.
Require Import Stdlib.Arith.Arith.
Require Import RingLike.Utf8.

Require Import RingLike.Core.
Require Import RingLike.RealLike.
Require Import RingLike.Misc.

Require Import AngleDef Angle TrigoWithoutPiExt.
Require Import Order.
Require Import AngleAddOverflowLe.
Require Import AngleAddOverflowEquiv.
Require Import AngleAddLeMonoL.
Require Import AngleDiv2.

Require Import TacChangeAngle.

Section a.

Context {T : Type}.
Context {ro : ring_like_op T}.
Context {rp : ring_like_prop T}.
Context {rl : real_like_prop T}.
Context {ac : angle_ctx T}.

Theorem rngl_cos_angle_div_2_add_not_overflow :
  ∀ α1 α2,
  angle_add_overflow α1 α2 = false
  → rngl_cos ((α1 + α2) /₂) = rngl_cos (α1 /₂ + α2 /₂).
Proof.
destruct_ac.
destruct (Nat.eq_dec (rngl_characteristic T) 1) as [Hc1| Hc1]. {
  specialize (rngl_characteristic_1 Hos Hc1) as H1.
  intros * Haov.
  rewrite H1; apply H1.
}
specialize (rngl_0_lt_2 Hos Hc1 Hto) as Hz2.
specialize (rngl_2_neq_0 Hos Hc1 Hto) as H20.
assert (Hze2 : (0 ≤ 2)%L) by now apply rngl_lt_le_incl.
assert (Hz1ac :  ∀ α, (0 ≤ 1 + rngl_cos α)%L). {
  intros.
  apply (rngl_le_sub_le_add_l Hop Hor).
  progress unfold rngl_sub.
  rewrite Hop, rngl_add_0_l.
  apply rngl_cos_bound.
}
assert (Hz1sc : ∀ α, (0 ≤ 1 - rngl_cos α)%L). {
  intros.
  apply (rngl_le_add_le_sub_r Hop Hor).
  rewrite rngl_add_0_l.
  apply rngl_cos_bound.
}
assert (Hs2z : (√2 ≠ 0)%L). {
  intros H.
  apply (f_equal rngl_squ) in H.
  rewrite rngl_squ_sqrt in H; [ | now apply rngl_lt_le_incl ].
  now rewrite (rngl_squ_0 Hos) in H.
}
intros * Haov.
generalize Haov; intros Haov_v.
rewrite <- angle_add_overflow_equiv2 in Haov.
progress unfold angle_add_overflow2 in Haov.
remember (α1 + α2)%A as α3 eqn:Hα3.
cbn.
progress unfold rngl_signp.
remember (0 ≤? rngl_sin α1)%L as zs1 eqn:Hzs1.
remember (0 ≤? rngl_sin α2)%L as zs2 eqn:Hzs2.
remember (0 ≤? rngl_sin α3)%L as zs3 eqn:Hzs3.
symmetry in Hzs1, Hzs2, Hzs3.
destruct zs3. {
  apply rngl_leb_le in Hzs3.
  rewrite rngl_mul_1_l.
  destruct zs1. {
    apply rngl_leb_le in Hzs1.
    rewrite rngl_mul_1_l.
    destruct zs2. {
      apply rngl_leb_le in Hzs2.
      rewrite rngl_mul_1_l.
      subst α3.
      apply rngl_sin_nonneg_sin_nonneg_sin_nonneg; try easy.
      remember (α1 =? π)%A as s1 eqn:Hs1.
      symmetry in Hs1.
      destruct s1. {
        apply angle_eqb_eq in Hs1; right.
        subst α1.
        intros H; subst α2.
        apply Bool.not_true_iff_false in Haov.
        apply Haov; clear Haov.
        rewrite angle_straight_add_straight.
        apply (angle_straight_pos Hc1).
      }
      apply angle_eqb_neq in Hs1.
      now left.
    }
    exfalso.
    apply (rngl_leb_gt_iff Hto) in Hzs2.
    apply (rngl_nle_gt Hor) in Hzs2.
    apply Hzs2; clear Hzs2.
    subst α3.
    specialize (rngl_sin_nonneg_add_nonneg α1 α2 Hzs1 Hzs3) as H1.
    now rewrite Haov_v in H1.
  } {
    apply (rngl_leb_gt_iff Hto) in Hzs1.
    destruct zs2. {
      apply rngl_leb_le in Hzs2.
      exfalso.
      progress unfold angle_ltb in Haov.
      apply (rngl_leb_gt_iff Hto) in Hzs1.
      rewrite Hzs1 in Haov.
      apply rngl_leb_le in Hzs3.
      now rewrite Hzs3 in Haov.
    }
    apply (rngl_leb_gt_iff Hto) in Hzs2.
    apply Bool.not_true_iff_false in Haov.
    apply angle_nlt_ge in Haov.
    apply (angle_le_rngl_sin_nonneg_sin_nonneg _ _ Haov) in Hzs3.
    now apply (rngl_nlt_ge Hor) in Hzs3.
  }
}
apply (rngl_leb_gt_iff Hto) in Hzs3.
rewrite (rngl_mul_opp_l Hop).
rewrite rngl_mul_1_l.
apply (rngl_opp_inj Hop).
rewrite (rngl_opp_involutive Hop).
rewrite (rngl_opp_sub_distr Hop).
destruct zs1. {
  apply rngl_leb_le in Hzs1.
  rewrite rngl_mul_1_l.
  destruct zs2. {
    apply rngl_leb_le in Hzs2.
    rewrite rngl_mul_1_l.
    subst α3.
    apply Bool.not_true_iff_false in Haov.
    apply angle_nlt_ge in Haov.
    now apply rngl_sin_nonneg_sin_nonneg_sin_neg.
  } {
    apply (rngl_leb_gt_iff Hto) in Hzs2.
    rewrite (rngl_mul_opp_l Hop).
    rewrite (rngl_mul_opp_r Hop).
    rewrite (rngl_sub_opp_r Hop).
    rewrite rngl_mul_1_l.
    subst α3.
    apply rngl_lt_le_incl in Hzs2.
    now apply rngl_sin_nonneg_sin_neg_sin_add_neg.
  }
}
apply (rngl_leb_gt_iff Hto) in Hzs1.
destruct zs2. {
  apply rngl_leb_le in Hzs2.
  do 2 rewrite (rngl_mul_opp_l Hop).
  rewrite (rngl_sub_opp_r Hop).
  do 2 rewrite rngl_mul_1_l.
  rewrite angle_add_comm in Hα3.
  subst α3.
  rewrite (rngl_mul_comm Hic).
  rewrite (rngl_mul_comm Hic √((1 + rngl_cos α1) / _))%L.
  apply rngl_lt_le_incl in Hzs1.
  now apply rngl_sin_nonneg_sin_neg_sin_add_neg.
}
apply (rngl_leb_gt_iff Hto) in Hzs2.
rewrite rngl_mul_assoc.
rewrite (rngl_mul_mul_swap Hic (-1))%L.
rewrite (rngl_squ_opp_1 Hop).
rewrite rngl_mul_1_l.
subst α3.
progress unfold angle_ltb in Haov.
apply (rngl_nle_gt Hor) in Hzs1, Hzs3.
apply rngl_leb_nle in Hzs1, Hzs3.
rewrite Hzs1, Hzs3 in Haov.
apply rngl_leb_nle in Hzs1, Hzs3.
apply (rngl_nle_gt_iff Hto) in Hzs1, Hzs3.
apply (rngl_ltb_ge_iff Hto) in Haov.
move Haov at bottom.
(* changing α1 into α1 - π *)
remember (α1 - π)%A as α.
apply angle_add_move_r in Heqα.
subst α1; rename α into α1.
move α1 after α2.
rewrite rngl_sin_add_straight_r in Hzs1.
rewrite rngl_cos_add_straight_r in Haov.
apply (rngl_opp_neg_pos Hop Hor) in Hzs1.
rewrite rngl_cos_add_straight_r.
rewrite (rngl_sub_opp_r Hop).
rewrite (rngl_add_opp_r Hop).
rewrite angle_add_add_swap in Haov, Hzs3 |-*.
(* changing α2 into α2 - π *)
remember (α2 - π)%A as α.
apply angle_add_move_r in Heqα.
subst α2; rename α into α2.
move α2 before α1.
move Hzs3 after Hzs3.
rewrite rngl_sin_add_straight_r in Hzs2.
apply (rngl_opp_neg_pos Hop Hor) in Hzs2.
rewrite (rngl_cos_add_straight_r α2).
rewrite (rngl_sub_opp_r Hop).
rewrite (rngl_add_opp_r Hop).
rewrite angle_add_assoc in Haov, Hzs3 |-*.
rewrite <- angle_add_assoc in Haov, Hzs3 |-*.
rewrite angle_straight_add_straight in Haov, Hzs3 |-*.
rewrite angle_add_0_r in Haov, Hzs3 |-*.
destruct (rngl_leb_dec 0 (rngl_cos α1 + rngl_cos α2))%L as [Hzc12| Hc12z]. {
  apply rngl_leb_le in Hzc12.
  apply rngl_sin_nonneg_sin_nonneg_add_cos_nonneg; try easy.
  now apply rngl_lt_le_incl.
  now apply rngl_lt_le_incl.
}
apply (rngl_leb_gt_iff Hto) in Hc12z.
exfalso.
apply (rngl_nlt_ge Hor) in Haov.
apply Haov; clear Haov.
destruct (rngl_leb_dec (rngl_cos α1) 0) as [Hc1z| Hzc1]. {
  apply rngl_leb_le in Hc1z.
  (* changing α1 into π - α1 *)
  remember (π - α1)%A as α.
  apply angle_sub_move_r in Heqα.
  rewrite angle_sub_opp_r in Heqα.
  apply angle_add_move_l in Heqα.
  subst α1; rename α into α1.
  move α1 after α2.
  rewrite <- angle_sub_sub_distr in Hzs3 |-*.
  rewrite rngl_sin_sub_straight_l in Hzs1, Hzs3.
  rewrite rngl_cos_sub_straight_l in Hc12z, Hc1z.
  do 2 rewrite rngl_cos_sub_straight_l.
  apply -> (rngl_opp_lt_compat Hop Hor).
  rewrite rngl_add_comm in Hc12z.
  rewrite (rngl_add_opp_r Hop) in Hc12z.
  apply (rngl_lt_sub_lt_add_l Hop Hor) in Hc12z.
  rewrite rngl_add_0_r in Hc12z.
  rewrite <- (rngl_opp_0 Hop) in Hc1z.
  apply (rngl_opp_le_compat Hop Hor) in Hc1z.
  rewrite <- (rngl_sub_0_l Hop).
  apply (rngl_lt_sub_lt_add_l Hop Hor).
  cbn.
  rewrite (rngl_mul_opp_r Hop).
  rewrite (rngl_sub_opp_r Hop).
  rewrite rngl_add_assoc.
  apply (rngl_add_nonneg_pos Hos Hor). {
    rewrite rngl_add_mul_r_diag_l.
    apply (rngl_mul_nonneg_nonneg Hos Hor); [ easy | ].
    apply (rngl_le_sub_le_add_l Hop Hor).
    rewrite (rngl_sub_0_l Hop).
    apply rngl_cos_bound.
  }
  now apply (rngl_mul_pos_pos Hop Hiq Hor).
} {
  apply (rngl_leb_gt_iff Hto) in Hzc1.
  move Hzc1 before Hzs2.
  rewrite <- (rngl_sub_0_l Hop).
  apply (rngl_lt_add_lt_sub_l Hop Hor).
  destruct (rngl_leb_dec 0 (rngl_cos α2)) as [Hzc2z| Hc2z]. {
    apply rngl_leb_le in Hzc2z.
    apply (rngl_nle_gt Hor) in Hzs3.
    exfalso.
    apply Hzs3; clear Hzs3; cbn.
    apply (rngl_le_0_add Hos Hor). {
      apply (rngl_mul_nonneg_nonneg Hos Hor); [ | easy ].
      now apply rngl_lt_le_incl.
    } {
      apply (rngl_mul_nonneg_nonneg Hos Hor);
        now apply rngl_lt_le_incl.
    }
  } {
    apply (rngl_leb_gt_iff Hto) in Hc2z.
    (* changing α2 into π - α2 *)
    remember (π - α2)%A as α.
    apply angle_sub_move_r in Heqα.
    rewrite angle_sub_opp_r in Heqα.
    apply angle_add_move_l in Heqα.
    subst α2; rename α into α2.
    move α2 before α1.
    rewrite angle_add_comm in Hzs3 |-*.
    rewrite <- angle_sub_sub_distr in Hzs3 |-*.
    rewrite rngl_sin_sub_straight_l in Hzs2, Hzs3.
    rewrite rngl_cos_sub_straight_l in Hc2z, Hc12z |-*.
    apply (rngl_opp_neg_pos Hop Hor) in Hc2z.
    rewrite (rngl_add_opp_r Hop) in Hc12z |-*.
    apply (rngl_lt_sub_lt_add_l Hop Hor) in Hc12z.
    apply (rngl_lt_sub_lt_add_l Hop Hor).
    rewrite rngl_add_0_r in Hc12z |-*.
    apply rngl_lt_le_incl in Hzs1, Hc12z.
    now apply rngl_cos_lt_cos_sub.
  }
}
Qed.

Theorem rngl_sin_angle_div_2_add_not_overflow :
  ∀ α1 α2,
  angle_add_overflow α1 α2 = false
  → rngl_sin ((α1 + α2) /₂) = rngl_sin (α1 /₂ + α2 /₂).
Proof.
destruct_ac.
destruct (Nat.eq_dec (rngl_characteristic T) 1) as [Hc1| Hc1]. {
  specialize (rngl_characteristic_1 Hos Hc1) as H1.
  intros * Haov.
  rewrite H1; apply H1.
}
specialize (rngl_0_lt_2 Hos Hc1 Hto) as Hz2.
specialize (rngl_2_neq_0 Hos Hc1 Hto) as H20.
intros * Haov.
assert (Hze2 : (0 ≤ 2)%L) by now apply rngl_lt_le_incl.
assert (Hz1ac :  ∀ α, (0 ≤ 1 + rngl_cos α)%L). {
  intros.
  apply (rngl_le_sub_le_add_l Hop Hor).
  progress unfold rngl_sub.
  rewrite Hop, rngl_add_0_l.
  apply rngl_cos_bound.
}
assert (Hz1sc : ∀ α, (0 ≤ 1 - rngl_cos α)%L). {
  intros.
  apply (rngl_le_add_le_sub_r Hop Hor).
  rewrite rngl_add_0_l.
  apply rngl_cos_bound.
}
assert (Hs2z : (√2 ≠ 0)%L). {
  intros H.
  apply (f_equal rngl_squ) in H.
  rewrite rngl_squ_sqrt in H; [ | now apply rngl_lt_le_incl ].
  now rewrite (rngl_squ_0 Hos) in H.
}
generalize Haov; intros Haov_v.
rewrite <- angle_add_overflow_equiv2 in Haov.
progress unfold angle_add_overflow2 in Haov.
remember (α1 + α2)%A as α3 eqn:Hα3.
cbn.
move Haov at bottom.
generalize Haov; intros Haov'.
progress unfold angle_ltb in Haov.
progress unfold rngl_signp.
remember (0 ≤? rngl_sin α1)%L as zs1 eqn:Hzs1.
remember (0 ≤? rngl_sin α2)%L as zs2 eqn:Hzs2.
symmetry in Hzs1, Hzs2.
destruct zs1. {
  apply rngl_leb_le in Hzs1.
  rewrite rngl_mul_1_l.
  destruct zs2. {
    apply rngl_leb_le in Hzs2.
    rewrite rngl_mul_1_l.
    subst α3.
    remember (α2 - π)%A as α.
    apply angle_add_move_r in Heqα.
    subst α2; rename α into α2.
    move α2 before α1.
    rewrite rngl_sin_add_straight_r in Hzs2.
    rewrite <- (rngl_opp_0 Hop) in Hzs2.
    apply (rngl_opp_le_compat Hop Hor) in Hzs2.
    rewrite angle_add_assoc.
    do 2 rewrite rngl_cos_add_straight_r.
    do 2 rewrite (rngl_sub_opp_r Hop).
    rewrite (rngl_add_opp_r Hop).
    now apply rngl_sin_nonneg_sin_neg_sin_add_neg.
  }
  apply (rngl_leb_gt_iff Hto) in Hzs2.
  subst α3.
  remember (0 ≤? rngl_sin (α1 + α2))%L as zs12 eqn:Hzs12.
  symmetry in Hzs12.
  destruct zs12. {
    exfalso.
    apply (rngl_nle_gt Hor) in Hzs2.
    apply Hzs2; clear Hzs2.
    apply rngl_leb_le in Hzs12.
    specialize (rngl_sin_nonneg_add_nonneg α1 α2 Hzs1 Hzs12) as H1.
    now rewrite Haov_v in H1.
  }
  clear Haov.
  apply (rngl_leb_gt_iff Hto) in Hzs12.
  rewrite (rngl_mul_opp_l Hop).
  rewrite rngl_mul_1_l.
  rewrite (rngl_mul_opp_r Hop).
  rewrite (rngl_add_opp_l Hop).
  remember (α2 - π)%A as α.
  apply angle_add_move_r in Heqα.
  subst α2; rename α into α2.
  move α2 before α1.
  rewrite rngl_sin_add_straight_r in Hzs2.
  rewrite angle_add_assoc in Hzs12.
  rewrite rngl_sin_add_straight_r in Hzs12.
  apply (rngl_opp_neg_pos Hop Hor) in Hzs2, Hzs12.
  rewrite angle_add_assoc.
  do 2 rewrite rngl_cos_add_straight_r.
  do 2 rewrite (rngl_sub_opp_r Hop).
  rewrite (rngl_add_opp_r Hop).
  apply rngl_sin_nonneg_sin_nonneg_add_cos_nonneg; try easy. {
    now apply rngl_lt_le_incl.
  }
  destruct (rngl_leb_dec 0 (rngl_cos α1))%L as [Hzc1| Hc1z]. {
    apply rngl_leb_le in Hzc1.
    apply rngl_add_cos_nonneg_when_sin_nonneg; try easy.
    now apply rngl_lt_le_incl.
    now apply rngl_lt_le_incl.
  }
  apply (rngl_leb_gt_iff Hto) in Hc1z.
  destruct (rngl_leb_dec 0 (rngl_cos α2))%L as [Hzc2| Hc2z]. {
    apply rngl_leb_le in Hzc2.
    rewrite rngl_add_comm.
    rewrite angle_add_comm in Hzs12.
    apply rngl_add_cos_nonneg_when_sin_nonneg; try easy.
    now apply rngl_lt_le_incl.
    now apply rngl_lt_le_incl.
  }
  apply (rngl_leb_gt_iff Hto) in Hc2z.
  apply (rngl_nle_gt Hor) in Hzs12.
  exfalso; apply Hzs12; clear Hzs12; cbn.
  apply (rngl_add_nonpos_nonpos Hos Hor). {
    apply rngl_lt_le_incl in Hc2z.
    now apply (rngl_mul_nonneg_nonpos Hop Hor).
  } {
    apply rngl_lt_le_incl in Hzs2, Hc1z.
    now apply (rngl_mul_nonpos_nonneg Hop Hor).
  }
} {
  apply (rngl_leb_gt_iff Hto) in Hzs1.
  rewrite (rngl_mul_opp_l Hop).
  rewrite rngl_mul_1_l.
  rewrite (rngl_mul_opp_l Hop).
  rewrite (rngl_add_opp_r Hop).
  remember (α1 - π)%A as α.
  apply angle_add_move_r in Heqα.
  subst α1; rename α into α1.
  move α1 after α2.
  subst α3.
  rewrite angle_add_add_swap in Haov, Haov' |-*.
  do 2 rewrite rngl_cos_add_straight_r in Haov.
  rewrite rngl_sin_add_straight_r in Hzs1, Haov.
  apply (rngl_opp_neg_pos Hop Hor) in Hzs1.
  do 2 rewrite rngl_cos_add_straight_r.
  do 2 rewrite (rngl_sub_opp_r Hop).
  rewrite (rngl_add_opp_r Hop).
  remember (0 ≤? - rngl_sin (α1 + α2))%L as zs12 eqn:Hzs12.
  symmetry in Hzs12.
  destruct zs12; [ easy | ].
  apply (rngl_leb_gt_iff Hto) in Hzs12.
  apply (rngl_opp_neg_pos Hop Hor) in Hzs12.
  move Hzs12 at bottom.
  apply (rngl_ltb_ge_iff Hto) in Haov.
  apply (rngl_opp_le_compat Hop Hor) in Haov.
  move Haov at bottom.
  destruct zs2. {
    apply rngl_leb_le in Hzs2.
    rewrite rngl_mul_1_l.
    apply rngl_sin_nonneg_sin_nonneg_add_cos_nonneg; try easy. {
      now apply rngl_lt_le_incl.
    }
    destruct (rngl_leb_dec 0 (rngl_cos α1))%L as [Hzc1| Hc1z]. {
      apply rngl_leb_le in Hzc1.
      apply rngl_add_cos_nonneg_when_sin_nonneg; try easy.
      now apply rngl_lt_le_incl.
      now apply rngl_lt_le_incl.
    }
    apply (rngl_leb_gt_iff Hto) in Hc1z.
    destruct (rngl_leb_dec 0 (rngl_cos α2))%L as [Hzc2| Hc2z]. {
      apply rngl_leb_le in Hzc2.
      rewrite rngl_add_comm.
      rewrite angle_add_comm in Hzs12.
      apply rngl_add_cos_nonneg_when_sin_nonneg; try easy.
      now apply rngl_lt_le_incl.
      now apply rngl_lt_le_incl.
    }
    apply (rngl_leb_gt_iff Hto) in Hc2z.
    apply (rngl_nle_gt Hor) in Hzs12.
    exfalso; apply Hzs12; clear Hzs12; cbn.
    apply (rngl_add_nonpos_nonpos Hos Hor). {
      apply rngl_lt_le_incl in Hzs1, Hc2z.
      apply (rngl_mul_nonneg_nonpos Hop Hor); try easy.
    } {
      apply rngl_lt_le_incl in Hc1z.
      now apply (rngl_mul_nonpos_nonneg Hop Hor).
    }
  }
  exfalso. (* because goal is nonneg=nonpos *)
  clear Haov'.
  apply (rngl_leb_gt_iff Hto) in Hzs2.
  destruct (rngl_eqb_dec (rngl_cos α1) 0) as [Hc1ez| Hc1ez]. {
    apply (rngl_eqb_eq Heo) in Hc1ez.
    apply eq_rngl_cos_0 in Hc1ez.
    destruct Hc1ez; subst α1. {
      cbn in Haov.
      rewrite (rngl_mul_0_l Hos) in Haov.
      rewrite (rngl_sub_0_l Hop) in Haov.
      rewrite rngl_mul_1_l in Haov.
      apply (rngl_opp_nonpos_nonneg Hop Hor) in Haov.
      now apply (rngl_nlt_ge Hor) in Haov.
    } {
      apply (rngl_nle_gt Hor) in Hzs1.
      exfalso; apply Hzs1; clear Hzs1.
      apply (rngl_opp_nonpos_nonneg Hop Hor).
      apply (rngl_0_le_1 Hos Hto).
    }
  }
  remember (α2 - π)%A as α.
  apply angle_add_move_r in Heqα.
  subst α2; rename α into α2.
  move α2 before α1.
  rewrite angle_add_assoc in Haov, Hzs12.
  rewrite rngl_cos_add_straight_r in Haov.
  rewrite rngl_sin_add_straight_r in Hzs12, Hzs2.
  apply (rngl_opp_neg_pos Hop Hor) in Hzs12, Hzs2.
  rewrite (rngl_opp_involutive Hop) in Hzs12.
  move Hzs2 before Hzs1.
  destruct (rngl_leb_dec 0 (rngl_cos α1))%L as [Hzc1| Hc1z]. {
    apply rngl_leb_le in Hzc1.
    destruct (rngl_leb_dec 0 (rngl_cos α2))%L as [Hzc2| Hc2z]. {
      apply rngl_leb_le in Hzc2.
      apply (rngl_nle_gt Hor) in Hzs12.
      apply Hzs12; clear Hzs12; cbn.
      apply rngl_lt_le_incl in Hzs1, Hzs2.
      apply (rngl_le_0_add Hos Hor).
      now apply (rngl_mul_nonneg_nonneg Hos Hor).
      now apply (rngl_mul_nonneg_nonneg Hos Hor).
    }
    apply (rngl_leb_gt_iff Hto) in Hc2z.
    remember (π - α2)%A as α.
    apply angle_sub_move_r in Heqα.
    rewrite angle_sub_opp_r in Heqα.
    apply angle_add_move_l in Heqα.
    subst α2; rename α into α2.
    move α2 before α1.
    rewrite angle_add_comm in Hzs12, Haov.
    rewrite <- angle_sub_sub_distr in Hzs12, Haov.
    rewrite rngl_sin_sub_straight_l in Hzs12, Hzs2.
    rewrite rngl_cos_sub_straight_l in Haov, Hc2z.
    rewrite (rngl_opp_involutive Hop) in Haov.
    apply (rngl_opp_neg_pos Hop Hor) in Hc2z.
    move Hzs2 before Hzs1.
    move Hzc1 before Hzs2.
    move Hc2z before Hzc1.
    apply (rngl_nlt_ge Hor) in Haov.
    apply Haov; clear Haov.
    assert (Hc12 : (rngl_cos α1 < rngl_cos α2)%L). {
      apply (rngl_nle_gt_iff Hto).
      apply (rngl_nle_gt Hor) in Hzs12.
      intros H.
      apply Hzs12; clear Hzs12.
      apply rngl_sin_sub_nonneg; try easy.
      now apply rngl_lt_le_incl.
      now apply rngl_lt_le_incl.
    }
    apply rngl_lt_le_incl in Hzs1, Hc12.
    now apply rngl_cos_lt_cos_sub.
  }
  apply (rngl_leb_gt_iff Hto) in Hc1z.
  clear Hc1ez.
  remember (α1 - π/₂)%A as α.
  apply angle_sub_move_r in Heqα.
  rewrite angle_sub_opp_r in Heqα.
  subst α1; rename α into α1.
  move α1 after α2.
  rewrite angle_add_add_swap in Hzs12, Haov.
  rewrite rngl_sin_add_right_r in Hzs1, Hzs12.
  rewrite rngl_cos_add_right_r in Hc1z.
  do 2 rewrite rngl_cos_add_right_r in Haov.
  apply (rngl_opp_neg_pos Hop Hor) in Hc1z.
  rewrite (rngl_opp_involutive Hop) in Haov.
  rename Hzs1 into Hzc1; rename Hc1z into Hzs1.
  move Hzs1 after Hzs2.
  move Hzc1 after Hzs2.
  apply (rngl_le_opp_r Hop Hor) in Haov.
  apply (rngl_nlt_ge Hor) in Haov.
  apply Haov; clear Haov; cbn.
  rewrite <- rngl_add_assoc.
  rewrite rngl_add_comm.
  rewrite <- rngl_add_assoc.
  apply (rngl_lt_0_add Hos Hor). {
    now apply (rngl_mul_pos_pos Hop Hiq Hor).
  }
  rewrite rngl_add_mul_r_diag_l.
  apply (rngl_mul_nonneg_nonneg Hos Hor).
  now apply rngl_lt_le_incl.
  apply (rngl_le_sub_le_add_l Hop Hor).
  rewrite (rngl_sub_0_l Hop).
  apply rngl_cos_bound.
}
Qed.

Theorem rngl_cos_angle_div_2_add_overflow :
  ∀ α1 α2,
  angle_add_overflow α1 α2 = true
  → rngl_cos ((α1 + α2) /₂) = rngl_cos (α1 /₂ + α2 /₂ + π).
Proof.
destruct_ac.
destruct (Nat.eq_dec (rngl_characteristic T) 1) as [Hc1| Hc1]. {
  intros.
  specialize (rngl_characteristic_1 Hos Hc1) as H1.
  rewrite H1; apply H1.
}
intros * Haov.
rewrite rngl_cos_add_straight_r.
cbn - [ angle_add ].
rewrite <- angle_add_overflow_equiv2 in Haov.
progress unfold angle_add_overflow2 in Haov.
progress unfold angle_ltb in Haov.
cbn.
progress unfold rngl_signp.
remember (0 ≤? rngl_sin α1)%L as zs1 eqn:Hzs1.
remember (0 ≤? rngl_sin α2)%L as zs2 eqn:Hzs2.
remember (0 ≤? rngl_sin (α1 + α2))%L as zs12 eqn:Hzs12.
symmetry in Hzs1, Hzs2, Hzs12.
destruct zs12. {
  apply rngl_leb_le in Hzs12.
  destruct zs1. {
    apply rngl_leb_le in Hzs1.
    apply (rngl_ltb_lt Heo) in Haov.
    rewrite rngl_mul_1_l.
    rewrite <- rngl_sin_add.
    rewrite <- rngl_cos_add.
    generalize Hzs12; intros H.
    apply rngl_leb_le in H.
    rewrite H; clear H.
    rewrite rngl_mul_1_l.
    rewrite (rngl_opp_sub_distr Hop).
    destruct zs2. {
      apply rngl_leb_le in Hzs2.
      rewrite rngl_mul_1_l.
      remember (α1 =? π)%A as t1s eqn:Ht1s.
      symmetry in Ht1s.
      destruct t1s. 2: {
        apply angle_eqb_neq in Ht1s.
        exfalso.
        apply (rngl_nle_gt Hor) in Haov.
        apply Haov; clear Haov.
        apply rngl_cos_add_le_cos; [ | easy | easy | easy ].
        now left.
      }
      apply angle_eqb_eq in Ht1s.
      subst α1.
      remember (α2 =? π)%A as t2s eqn:Ht2s.
      symmetry in Ht2s.
      destruct t2s. 2: {
        apply angle_eqb_neq in Ht2s.
        exfalso.
        apply (rngl_nle_gt Hor) in Haov.
        apply Haov; clear Haov.
        apply rngl_cos_add_le_cos; [ | easy | easy | easy ].
        now right; left.
      }
      apply angle_eqb_eq in Ht2s.
      subst α2.
      rewrite angle_straight_add_straight.
      cbn.
      rewrite (rngl_sub_opp_r Hop).
      rewrite (rngl_add_opp_r Hop).
      rewrite (rngl_sub_diag Hos).
      rewrite (rngl_div_diag Hiq). 2: {
        apply (rngl_2_neq_0 Hos Hc1 Hto).
      }
      rewrite (rngl_div_0_l Hos Hi1). 2: {
        apply (rngl_2_neq_0 Hos Hc1 Hto).
      }
      rewrite (rl_sqrt_1 Hop Hiq Hto).
      rewrite (rl_sqrt_0 Hop Hto Hii).
      rewrite (rngl_mul_0_l Hos).
      rewrite (rngl_sub_0_r Hos).
      symmetry.
      apply rngl_mul_1_l.
    }
    apply (rngl_leb_gt_iff Hto) in Hzs2.
    rewrite (rngl_mul_opp_l Hop).
    rewrite rngl_mul_1_l.
    rewrite (rngl_mul_opp_r Hop).
    rewrite (rngl_sub_opp_r Hop).
    apply rngl_lt_le_incl in Hzs2.
    now apply rngl_sin_nonneg_sin_neg_sin_add_neg.
  }
  clear Haov.
  apply (rngl_leb_gt_iff Hto) in Hzs1.
  rewrite (rngl_mul_opp_l Hop).
  rewrite rngl_mul_1_l.
  rewrite (rngl_opp_sub_distr Hop).
  rewrite (rngl_mul_opp_l Hop).
  rewrite (rngl_sub_opp_r Hop).
  rewrite <- rngl_sin_add.
  rewrite <- rngl_cos_add.
  generalize Hzs12; intros H.
  apply rngl_leb_le in H.
  rewrite H; clear H.
  rewrite rngl_mul_1_l.
  destruct zs2. {
    apply rngl_leb_le in Hzs2.
    rewrite rngl_mul_1_l.
    rewrite angle_add_comm.
    rewrite (rngl_mul_comm Hic).
    rewrite (rngl_mul_comm Hic √((1 + _)/2))%L.
    apply rngl_lt_le_incl in Hzs1.
    now apply rngl_sin_nonneg_sin_neg_sin_add_neg.
  }
  apply (rngl_leb_gt_iff Hto) in Hzs2.
  rewrite (rngl_mul_opp_l Hop).
  rewrite rngl_mul_1_l.
  rewrite (rngl_mul_opp_r Hop).
  rewrite (rngl_add_opp_r Hop).
  change_angle_sub_r α1 π.
  progress sin_cos_add_sub_straight_hyp T Hzs12.
  progress sin_cos_add_sub_straight_hyp T Hzs1.
  progress sin_cos_add_sub_straight_goal T.
  change_angle_sub_r α2 π.
  rewrite angle_add_assoc in Hzs12 |-*.
  progress sin_cos_add_sub_straight_hyp T Hzs12.
  progress sin_cos_add_sub_straight_hyp T Hzs2.
  progress sin_cos_add_sub_straight_goal T.
  do 3 rewrite (rngl_sub_opp_r Hop).
  apply rngl_sin_nonneg_sin_nonneg_sin_nonneg; try easy; cycle 1.
  now apply rngl_lt_le_incl.
  now apply rngl_lt_le_incl.
  left; intros H; subst α1.
  cbn in Hzs1.
  now apply rngl_lt_irrefl in Hzs1.
}
destruct zs1; [ easy | ].
apply (rngl_leb_gt_iff Hto) in Hzs1, Hzs12.
apply (rngl_ltb_lt Heo) in Haov.
rewrite (rngl_mul_opp_l Hop).
rewrite rngl_mul_1_l.
rewrite (rngl_opp_sub_distr Hop).
rewrite (rngl_mul_opp_l Hop).
rewrite (rngl_sub_opp_r Hop).
rewrite <- rngl_sin_add.
rewrite <- rngl_cos_add.
generalize Hzs12; intros H.
apply (rngl_leb_gt_iff Hto) in H.
rewrite H; clear H.
rewrite (rngl_mul_opp_l Hop).
rewrite rngl_mul_1_l.
destruct zs2. {
  rewrite rngl_mul_1_l.
  apply rngl_leb_le in Hzs2.
  change_angle_sub_r α1 π.
  progress sin_cos_add_sub_straight_hyp T Haov.
  progress sin_cos_add_sub_straight_hyp T Hzs12.
  progress sin_cos_add_sub_straight_hyp T Hzs1.
  exfalso.
  apply (rngl_nle_gt Hor) in Haov.
  apply Haov; clear Haov.
  apply rngl_cos_add_le_cos; try easy; cycle 1.
  now apply rngl_lt_le_incl.
  now apply rngl_lt_le_incl.
  left; intros H; subst α1.
  now apply rngl_lt_irrefl in Hzs1.
}
apply (rngl_leb_gt_iff Hto) in Hzs2.
rewrite (rngl_mul_opp_l Hop).
rewrite rngl_mul_1_l.
rewrite (rngl_mul_opp_r Hop).
rewrite (rngl_add_opp_r Hop).
apply (rngl_opp_inj Hop).
rewrite (rngl_opp_involutive Hop).
rewrite (rngl_opp_sub_distr Hop).
change_angle_sub_r α1 π.
progress sin_cos_add_sub_straight_hyp T Haov.
progress sin_cos_add_sub_straight_hyp T Hzs12.
progress sin_cos_add_sub_straight_hyp T Hzs1.
progress sin_cos_add_sub_straight_goal T.
change_angle_sub_r α2 π.
rewrite angle_add_assoc in Hzs12, Haov |-*.
progress sin_cos_add_sub_straight_hyp T Hzs12.
progress sin_cos_add_sub_straight_hyp T Haov.
progress sin_cos_add_sub_straight_hyp T Hzs2.
progress sin_cos_add_sub_straight_goal T.
do 3 rewrite (rngl_sub_opp_r Hop).
apply rngl_sin_nonneg_sin_nonneg_sin_neg; try easy; cycle 1.
now apply rngl_lt_le_incl.
now apply rngl_lt_le_incl.
progress unfold angle_leb.
generalize Hzs1; intros H.
apply rngl_lt_le_incl in H.
apply rngl_leb_le in H.
rewrite H; clear H.
generalize Hzs12; intros H.
apply (rngl_leb_gt_iff Hto) in H.
now rewrite H.
Qed.

Theorem rngl_sin_angle_div_2_add_overflow :
  ∀ α1 α2,
  angle_add_overflow α1 α2 = true
  → rngl_sin ((α1 + α2) /₂) = rngl_sin (α1 /₂ + α2 /₂ + π).
Proof.
destruct_ac.
destruct (Nat.eq_dec (rngl_characteristic T) 1) as [Hc1| Hc1]. {
  intros.
  specialize (rngl_characteristic_1 Hos Hc1) as H1.
  rewrite H1; apply H1.
}
intros * Haov.
rewrite rngl_sin_add_straight_r.
cbn - [ angle_add ].
rewrite <- angle_add_overflow_equiv2 in Haov.
progress unfold angle_add_overflow2 in Haov.
progress unfold angle_ltb in Haov.
cbn.
progress unfold rngl_signp.
remember (0 ≤? rngl_sin α1)%L as zs1 eqn:Hzs1.
remember (0 ≤? rngl_sin α2)%L as zs2 eqn:Hzs2.
remember (0 ≤? rngl_sin (α1 + α2))%L as zs12 eqn:Hzs12.
symmetry in Hzs1, Hzs2, Hzs12.
rewrite <- rngl_cos_add.
destruct zs12. {
  apply rngl_leb_le in Hzs12.
  destruct zs1. {
    apply rngl_leb_le in Hzs1.
    apply (rngl_ltb_lt Heo) in Haov.
    rewrite rngl_mul_1_l.
    rewrite (rngl_opp_add_distr Hop).
    rewrite (rngl_opp_sub_swap Hop).
    destruct zs2. {
      apply rngl_leb_le in Hzs2.
      rewrite rngl_mul_1_l.
      remember (α1 =? π)%A as t1s eqn:Ht1s.
      symmetry in Ht1s.
      destruct t1s. 2: {
        apply angle_eqb_neq in Ht1s.
        exfalso.
        apply (rngl_nle_gt Hor) in Haov.
        apply Haov; clear Haov.
        apply rngl_cos_add_le_cos; [ | easy | easy | easy ].
        now left.
      }
      apply angle_eqb_eq in Ht1s.
      subst α1.
      remember (α2 =? π)%A as t2s eqn:Ht2s.
      symmetry in Ht2s.
      destruct t2s. 2: {
        apply angle_eqb_neq in Ht2s.
        exfalso.
        apply (rngl_nle_gt Hor) in Haov.
        apply Haov; clear Haov.
        apply rngl_cos_add_le_cos; [ | easy | easy | easy ].
        now right; left.
      }
      apply angle_eqb_eq in Ht2s.
      subst α2.
      rewrite angle_straight_add_straight.
      cbn.
      rewrite (rngl_sub_opp_r Hop).
      rewrite (rngl_add_opp_r Hop).
      rewrite (rngl_sub_diag Hos).
      rewrite (rngl_div_diag Hiq). 2: {
        apply (rngl_2_neq_0 Hos Hc1 Hto).
      }
      rewrite (rngl_div_0_l Hos Hi1). 2: {
        apply (rngl_2_neq_0 Hos Hc1 Hto).
      }
      rewrite (rl_sqrt_1 Hop Hiq Hto).
      rewrite (rl_sqrt_0 Hop Hto Hii).
      rewrite (rngl_mul_0_l Hos).
      rewrite (rngl_mul_0_r Hos).
      rewrite (rngl_sub_0_r Hos).
      symmetry.
      apply (rngl_opp_0 Hop).
    }
    apply (rngl_leb_gt_iff Hto) in Hzs2.
    rewrite (rngl_mul_opp_l Hop).
    rewrite rngl_mul_1_l.
    rewrite (rngl_mul_opp_r Hop).
    rewrite (rngl_sub_opp_r Hop).
    rewrite (rngl_add_opp_l Hop).
    change_angle_sub_r α2 π.
    progress sin_cos_add_sub_straight_hyp T Hzs2.
    rewrite angle_add_assoc in Haov, Hzs12 |-*.
    progress sin_cos_add_sub_straight_hyp T Haov.
    progress sin_cos_add_sub_straight_hyp T Hzs12.
    progress sin_cos_add_sub_straight_goal T.
    do 2 rewrite (rngl_sub_opp_r Hop).
    destruct (rngl_eqb_dec (rngl_sin (α1 + α2)) 0) as [Hs12| Hs12]. {
      apply (rngl_eqb_eq Heo) in Hs12.
      apply eq_rngl_sin_0 in Hs12.
      destruct Hs12 as [Hs12| Hs12]. {
        exfalso.
        rewrite Hs12 in Haov; cbn in Haov.
        apply (rngl_nle_gt Hor) in Haov.
        apply Haov, rngl_cos_bound.
      }
      rewrite Hs12 in Hzs12; cbn in Hzs12.
      rewrite Hs12 in Haov; cbn in Haov.
      rewrite Hs12.
      cbn.
      apply angle_add_move_l in Hs12.
      subst α2.
      rewrite rngl_cos_sub_straight_l.
      rewrite (rngl_sub_opp_r Hop).
      do 2 rewrite (rngl_add_opp_r Hop).
      rewrite (rngl_mul_comm Hic).
      do 2 rewrite (rngl_sub_diag Hos).
      rewrite (rngl_div_0_l Hos Hi1). 2: {
        apply (rngl_2_neq_0 Hos Hc1 Hto).
      }
      apply (rl_sqrt_0 Hop Hto Hii).
    }
    apply (rngl_eqb_neq Heo) in Hs12.
    apply rngl_sin_nonneg_sin_nonneg_sin_neg; try easy. 2: {
      now apply rngl_lt_le_incl.
    }
    progress unfold angle_leb.
    generalize Hzs1; intros H.
    apply rngl_leb_le in H.
    rewrite H; clear H.
    remember (0 ≤? rngl_sin (α1 + α2))%L as z12 eqn:Hz12.
    symmetry in Hz12.
    destruct z12; [ | easy ].
    apply rngl_leb_le in Hz12.
    now apply (rngl_le_antisymm Hor) in Hz12.
  }
  clear Haov.
  apply (rngl_leb_gt_iff Hto) in Hzs1.
  rewrite (rngl_mul_opp_l Hop).
  rewrite rngl_mul_1_l.
  rewrite (rngl_opp_add_distr Hop).
  rewrite (rngl_opp_sub_swap Hop).
  rewrite (rngl_mul_opp_l Hop).
  rewrite (rngl_opp_involutive Hop).
  destruct zs2. {
    apply rngl_leb_le in Hzs2.
    rewrite rngl_mul_1_l.
    change_angle_sub_r α1 π.
    progress sin_cos_add_sub_straight_hyp T Hzs12.
    progress sin_cos_add_sub_straight_hyp T Hzs1.
    progress sin_cos_add_sub_straight_goal T.
    do 2 rewrite (rngl_sub_opp_r Hop).
    destruct (rngl_eqb_dec (rngl_sin (α1 + α2)) 0) as [Hs12| Hs12]. {
      apply (rngl_eqb_eq Heo) in Hs12.
      apply eq_rngl_sin_0 in Hs12.
      destruct Hs12 as [Hs12| Hs12]. {
        rewrite Hs12.
        apply angle_add_move_l in Hs12.
        rewrite angle_sub_0_l in Hs12.
        subst α2.
        cbn in Hzs2.
        apply (rngl_opp_nonneg_nonpos Hop Hor) in Hzs2.
        now apply (rngl_nlt_ge Hor) in Hzs2.
      }
      rewrite Hs12.
      cbn.
      apply angle_add_move_l in Hs12.
      subst α2.
      rewrite rngl_cos_sub_straight_l.
      rewrite (rngl_sub_opp_r Hop).
      do 2 rewrite (rngl_add_opp_r Hop).
      rewrite (rngl_mul_comm Hic).
      do 2 rewrite (rngl_sub_diag Hos).
      rewrite (rngl_div_0_l Hos Hi1). 2: {
        apply (rngl_2_neq_0 Hos Hc1 Hto).
      }
      apply (rl_sqrt_0 Hop Hto Hii).
    }
    apply (rngl_eqb_neq Heo) in Hs12.
    apply rngl_sin_nonneg_sin_nonneg_sin_neg; try easy. 2: {
      now apply rngl_lt_le_incl.
    }
    progress unfold angle_leb.
    generalize Hzs1; intros H.
    apply rngl_lt_le_incl in H.
    apply rngl_leb_le in H.
    rewrite H; clear H.
    remember (0 ≤? rngl_sin (α1 + α2))%L as z12 eqn:Hz12.
    symmetry in Hz12.
    destruct z12; [ | easy ].
    apply rngl_leb_le in Hz12.
    now apply (rngl_le_antisymm Hor) in Hz12.
  }
  apply (rngl_leb_gt_iff Hto) in Hzs2.
  rewrite (rngl_mul_opp_l Hop).
  rewrite rngl_mul_1_l.
  rewrite (rngl_mul_opp_r Hop).
  rewrite (rngl_sub_opp_r Hop).
  change_angle_sub_r α1 π.
  progress sin_cos_add_sub_straight_hyp T Hzs12.
  progress sin_cos_add_sub_straight_hyp T Hzs1.
  progress sin_cos_add_sub_straight_goal T.
  do 2 rewrite (rngl_sub_opp_r Hop).
  apply rngl_lt_le_incl in Hzs1, Hzs2.
  now apply rngl_sin_nonneg_sin_neg_sin_add_neg.
}
destruct zs1; [ easy | ].
apply (rngl_leb_gt_iff Hto) in Hzs1, Hzs12.
apply (rngl_ltb_lt Heo) in Haov.
rewrite (rngl_mul_opp_l Hop).
rewrite rngl_mul_1_l.
rewrite (rngl_opp_add_distr Hop).
rewrite (rngl_opp_sub_swap Hop).
rewrite (rngl_mul_opp_l Hop).
rewrite (rngl_opp_involutive Hop).
destruct zs2. {
  apply rngl_leb_le in Hzs2.
  rewrite rngl_mul_1_l.
  change_angle_sub_r α1 π.
  progress sin_cos_add_sub_straight_hyp T Haov.
  progress sin_cos_add_sub_straight_hyp T Hzs12.
  progress sin_cos_add_sub_straight_hyp T Hzs1.
  progress sin_cos_add_sub_straight_goal T.
  do 2 rewrite (rngl_sub_opp_r Hop).
  exfalso.
  apply (rngl_nle_gt Hor) in Haov.
  apply Haov; clear Haov.
  apply rngl_cos_add_le_cos; try easy; cycle 1. {
    now apply rngl_lt_le_incl.
  } {
    now apply rngl_lt_le_incl.
  }
  remember (α1 =? π)%A as t1s eqn:Ht1s.
  symmetry in Ht1s.
  destruct t1s. 2: {
    apply angle_eqb_neq in Ht1s.
    now left.
  }
  apply angle_eqb_eq in Ht1s.
  subst α1.
  now apply rngl_lt_irrefl in Hzs1.
}
apply (rngl_leb_gt_iff Hto) in Hzs2.
change_angle_sub_r α1 π.
progress sin_cos_add_sub_straight_hyp T Haov.
progress sin_cos_add_sub_straight_hyp T Hzs12.
progress sin_cos_add_sub_straight_hyp T Hzs1.
progress sin_cos_add_sub_straight_goal T.
do 2 rewrite (rngl_sub_opp_r Hop).
rewrite (rngl_mul_opp_l Hop).
rewrite rngl_mul_1_l.
rewrite (rngl_mul_opp_r Hop).
rewrite (rngl_sub_opp_r Hop).
apply rngl_lt_le_incl in Hzs1, Hzs2.
now apply rngl_sin_nonneg_sin_neg_sin_add_neg.
Qed.

Theorem angle_div_2_add :
  ∀ α1 α2,
  ((α1 + α2) /₂)%A =
    if angle_add_overflow α1 α2 then
      (α1 /₂ + α2 /₂ + π)%A
    else
      (α1 /₂ + α2 /₂)%A.
Proof.
intros.
remember (angle_add_overflow α1 α2) as aov eqn:Haov.
symmetry in Haov.
destruct aov. 2: {
  apply eq_angle_eq.
  f_equal. {
    now apply rngl_cos_angle_div_2_add_not_overflow.
  } {
    now apply rngl_sin_angle_div_2_add_not_overflow.
  }
} {
  apply eq_angle_eq.
  f_equal. {
    now apply rngl_cos_angle_div_2_add_overflow.
  } {
    now apply rngl_sin_angle_div_2_add_overflow.
  }
}
Qed.

Theorem angle_div_2_sub :
  ∀ α1 α2,
  ((α1 - α2) /₂)%A =
    if (α2 ≤? α1)%A then
      (α1 /₂ - α2 /₂)%A
    else
      (α1 /₂ - α2 /₂ + π)%A.
Proof.
intros.
specialize (angle_div_2_add α1 (- α2)) as H1.
rewrite angle_add_opp_r in H1.
rewrite H1; clear H1.
remember (angle_add_overflow α1 (- α2)) as o12 eqn:Ho12.
symmetry in Ho12.
rewrite angle_add_overflow_comm in Ho12.
progress unfold angle_add_overflow in Ho12.
rewrite angle_opp_involutive in Ho12.
destruct o12. {
  apply Bool.andb_true_iff in Ho12.
  destruct Ho12 as (H2z, H21).
  rewrite H21.
  progress unfold angle_sub.
  rewrite angle_opp_div_2.
  remember (α2 =? 0)%A as z2 eqn:Hz2.
  symmetry in Hz2.
  rewrite angle_add_assoc.
  destruct z2; [ | easy ].
  apply angle_eqb_eq in Hz2.
  apply angle_neqb_neq in H2z.
  subst α2.
  now rewrite angle_opp_0 in H2z.
}
apply Bool.andb_false_iff in Ho12.
destruct Ho12 as [H2z| H21]. {
  (* lemma *)
  apply (f_equal negb) in H2z.
  rewrite Bool.negb_involutive in H2z.
  cbn in H2z.
  apply angle_eqb_eq in H2z.
  apply (f_equal angle_opp) in H2z.
  rewrite angle_opp_involutive in H2z.
  rewrite angle_opp_0 in H2z; subst α2.
  rewrite angle_opp_0.
  rewrite angle_0_div_2.
  rewrite angle_nonneg.
  rewrite angle_add_0_r, angle_sub_0_r.
  easy.
}
rewrite H21.
progress unfold angle_sub.
rewrite angle_opp_div_2.
remember (α2 =? 0)%A as z2 eqn:Hz2.
symmetry in Hz2.
destruct z2. {
  apply angle_eqb_eq in Hz2; subst α2.
  apply angle_leb_gt in H21.
  apply angle_nle_gt in H21.
  exfalso; apply H21.
  apply angle_nonneg.
}
rewrite angle_add_assoc.
rewrite <- angle_add_assoc.
rewrite angle_straight_add_straight.
symmetry.
apply angle_add_0_r.
Qed.

Theorem angle_div_2_sub' :
  ∀ α1 α2,
    (α1 /₂ - α2 /₂)%A =
    if (α2 ≤? α1)%A then
      ((α1 - α2) /₂)%A
    else
      ((α1 - α2) /₂ + π)%A.
Proof.
intros.
rewrite angle_div_2_sub.
remember (α2 ≤? α1)%A as tt eqn:Htt.
symmetry in Htt.
destruct tt; [ easy | ].
rewrite <- angle_add_assoc.
rewrite angle_straight_add_straight.
symmetry.
apply angle_add_0_r.
Qed.

Theorem angle_div_2_add_not_overflow :
  ∀ α1 α2,
  angle_add_overflow α1 α2 = false
  → ((α1 + α2) /₂)%A = (α1 /₂ + α2 /₂)%A.
Proof.
intros * Haov.
rewrite angle_div_2_add.
now rewrite Haov.
Qed.

Theorem angle_div_2_add_overflow :
  ∀ α1 α2,
  angle_add_overflow α1 α2 = true
  → ((α1 + α2) /₂)%A = (α1 /₂ + α2 /₂ + π)%A.
Proof.
intros * Haov.
rewrite angle_div_2_add.
now rewrite Haov.
Qed.

Theorem angle_div_2_lt_straight :
  rngl_characteristic T ≠ 1 →
  ∀ α, (α /₂ < π)%A.
Proof.
destruct_ac.
intros Hc1.
intros.
progress unfold angle_ltb.
specialize (rngl_sin_div_2_nonneg α) as H1.
apply rngl_leb_le in H1.
rewrite H1; clear H1.
cbn.
rewrite (rngl_leb_refl Hor).
apply (rngl_ltb_lt Heo).
progress unfold rngl_signp.
remember (0 ≤? rngl_sin α)%L as zs eqn:Hzs.
symmetry in Hzs.
destruct zs. {
  rewrite rngl_mul_1_l.
  apply (rngl_lt_le_trans Hor _ 0). {
    apply (rngl_opp_1_lt_0 Hop Hc1 Hto).
  }
  apply rl_sqrt_nonneg.
  apply (rngl_div_nonneg Hop Hiv Hto). 2: {
    apply (rngl_0_lt_2 Hos Hc1 Hto).
  }
  apply (rngl_le_opp_l Hop Hor).
  apply rngl_cos_bound.
} {
  apply (rngl_leb_gt_iff Hto) in Hzs.
  rewrite (rngl_mul_opp_l Hop).
  apply -> (rngl_opp_lt_compat Hop Hor).
  rewrite rngl_mul_1_l.
  rewrite <- (rl_sqrt_1 Hop Hiq Hto) at 4.
  apply (rl_sqrt_lt_rl_sqrt Hto). {
    apply (rngl_div_nonneg Hop Hiv Hto). 2: {
      apply (rngl_0_lt_2 Hos Hc1 Hto).
    }
    apply (rngl_le_opp_l Hop Hor).
    apply rngl_cos_bound.
  } {
    apply (rngl_lt_div_l Hop Hiv Hto). {
      apply (rngl_0_lt_2 Hos Hc1 Hto).
    }
    rewrite rngl_mul_1_l.
    apply (rngl_add_lt_mono_l Hos Hor).
    apply rngl_le_neq.
    split; [ apply rngl_cos_bound | ].
    intros H.
    apply eq_rngl_cos_1 in H.
    subst α.
    now apply rngl_lt_irrefl in Hzs.
  }
}
Qed.

Theorem angle_add_overflow_lt_le :
  ∀ α α1 α2,
  (α1 < α)%A
  → (α2 ≤ -α)%A
  → angle_add_overflow α1 α2 = false.
Proof.
destruct_ac.
intros * H1 H2.
progress unfold angle_add_overflow.
remember (α1 =? 0)%A as z1 eqn:Hz1.
symmetry in Hz1.
destruct z1; [ easy | ].
apply angle_leb_gt.
apply (angle_le_lt_trans _ (- α))%A; [ easy | ].
apply angle_eqb_neq in Hz1.
apply angle_lt_opp_r; [ easy | ].
now rewrite angle_opp_involutive.
Qed.

Theorem angle_add_not_overflow_lt_straight_le_straight :
  ∀ α1 α2,
  (α1 < π)%A
  → (α2 ≤ π)%A
  → angle_add_overflow α1 α2 = false.
Proof.
intros * H1 H2.
apply (angle_add_overflow_lt_le π); [ easy | ].
now rewrite angle_opp_straight.
Qed.

Theorem angle_add_overflow_ge_straight_ge_straight :
  rngl_characteristic T ≠ 1 →
  ∀ α1 α2,
  (π ≤ α1)%A
  → (π ≤ α2)%A
  → angle_add_overflow α1 α2 = true.
Proof.
destruct_ac.
intros Hc1 * H1 H2.
progress unfold angle_add_overflow.
remember (α1 =? 0)%A as z1 eqn:Hz1.
symmetry in Hz1.
destruct z1. {
  exfalso.
  apply angle_eqb_eq in Hz1; subst α1.
  apply angle_nlt_ge in H1.
  apply H1; clear H1.
  now apply angle_straight_pos.
}
cbn.
progress unfold angle_leb in H1.
progress unfold angle_leb in H2.
progress unfold angle_leb.
cbn in H1, H2 |-*.
rewrite (rngl_leb_refl Hor) in H1, H2.
rewrite (rngl_leb_0_opp Hop Hto).
remember (0 ≤? rngl_sin α1)%L as zs1 eqn:Hzs1.
remember (0 ≤? rngl_sin α2)%L as zs2 eqn:Hzs2.
remember (rngl_sin α1 ≤? 0)%L as s1z eqn:Hs1z.
symmetry in Hzs1, Hzs2, Hs1z.
destruct s1z. {
  destruct zs2; [ | easy ].
  apply rngl_leb_le in Hzs2, Hs1z, H2.
  apply rngl_leb_le.
  apply (rngl_le_trans Hor _ (- 1)); [ easy | ].
  apply rngl_cos_bound.
}
destruct zs1; [ | clear H1 ]. {
  exfalso.
  apply Bool.not_false_iff_true in H1.
  apply H1; clear H1.
  apply (rngl_leb_gt Hor).
  apply rngl_le_neq.
  split; [ apply rngl_cos_bound | ].
  intros H; symmetry in H.
  apply eq_rngl_cos_opp_1 in H; subst α1.
  cbn in Hs1z.
  now rewrite (rngl_leb_refl Hor) in Hs1z.
}
exfalso.
apply (rngl_leb_gt_iff Hto) in Hzs1, Hs1z.
now apply (rngl_lt_asymm Hor) in Hzs1.
Qed.

Theorem angle_add_overflow_gt_straight_ge_straight :
  ∀ α1 α2,
  (π < α1)%A
  → (π ≤ α2)%A
  → angle_add_overflow α1 α2 = true.
Proof.
destruct_ac.
destruct (Nat.eq_dec (rngl_characteristic T) 1) as [Hc1| Hc1]. {
  intros * H1 H2.
  rewrite (rngl_characteristic_1_angle_0 Hc1 π) in H1.
  rewrite (rngl_characteristic_1_angle_0 Hc1 α1) in H1.
  now apply angle_lt_irrefl in H1.
}
intros * H1 H2.
apply (angle_add_overflow_ge_straight_ge_straight Hc1); [ | easy ].
now apply angle_lt_le_incl.
Qed.

Theorem angle_add_overflow_div_2_div_2 :
  ∀ α1 α2, angle_add_overflow (α1 /₂) (α2 /₂) = false.
Proof.
destruct_ac.
destruct (Nat.eq_dec (rngl_characteristic T) 1) as [Hc1| Hc1]. {
  intros.
  rewrite (rngl_characteristic_1_angle_0 Hc1 (α1 /₂)%A).
  rewrite (rngl_characteristic_1_angle_0 Hc1 (α2 /₂)%A).
  apply angle_add_overflow_0_l.
}
intros.
apply angle_add_not_overflow_lt_straight_le_straight.
apply (angle_div_2_lt_straight Hc1).
apply angle_div_2_le_straight.
Qed.

Theorem angle_div_2_le : ∀ α, (α /₂ ≤ α)%A.
Proof.
intros.
remember (α /₂)%A as x.
rewrite <- (angle_div_2_mul_2 α).
rewrite <- angle_mul_1_l in Heqx.
subst x.
apply angle_mul_le_mono_r; [ | now apply -> Nat.succ_le_mono ].
cbn.
apply Nat.eq_add_0.
split; [ now rewrite angle_add_overflow_0_r | ].
rewrite angle_add_0_r.
apply Nat_eq_b2n_0.
apply angle_add_overflow_div_2_div_2.
Qed.

Theorem angle_div_2_pow_le_diag : ∀ n α, (α /₂^n ≤ α)%A.
Proof.
intros.
induction n; [ apply angle_le_refl | cbn ].
apply (angle_le_trans _ (α /₂)). {
  now apply angle_div_2_le_compat.
}
apply angle_div_2_le.
Qed.

Theorem angle_div_2_pow_add :
  ∀ n α1 α2,
  angle_add_overflow α1 α2 = false
  → ((α1 + α2) /₂^n = α1 /₂^n + α2 /₂^n)%A.
Proof.
intros * Haov.
induction n; [ easy | cbn ].
rewrite IHn.
apply angle_div_2_add_not_overflow.
apply angle_add_overflow_le with (α2 := α2). {
  apply angle_div_2_pow_le_diag.
}
rewrite angle_add_overflow_comm.
apply angle_add_overflow_le with (α2 := α1). {
  apply angle_div_2_pow_le_diag.
}
now rewrite angle_add_overflow_comm.
Qed.

Theorem angle_div_2_pow_mul :
  ∀ n m α,
  angle_mul_nat_div_2π m α = 0
  →  ((m * α) /₂^n)%A = (m * (α /₂^n))%A.
Proof.
intros * Haov.
induction m; [ apply angle_0_div_2_pow | cbn ].
cbn in Haov.
destruct m. {
  cbn.
  rewrite angle_add_0_r.
  symmetry; apply angle_add_0_r.
}
apply Nat.eq_add_0 in Haov.
rewrite angle_div_2_pow_add; [ | now apply Nat_eq_b2n_0 ].
f_equal.
now apply IHm.
Qed.

Theorem angle_mul_nat_div_2 :
  ∀ n α,
  angle_mul_nat_div_2π n α = 0
  → (n * (α /₂) = (n * α) /₂)%A.
Proof.
destruct_ac.
intros * Haov.
induction n; cbn. {
  symmetry; apply angle_0_div_2.
}
apply angle_mul_nat_div_2π_succ_l_false in Haov.
rewrite IHn; [ | easy ].
symmetry.
now apply angle_div_2_add_not_overflow.
Qed.

Theorem angle_mul_nat_div_2π_mul_2_div_2 :
  ∀ n α,
  angle_mul_nat_div_2π n α = 0
  → angle_mul_nat_div_2π (2 * n) (α /₂) = 0.
Proof.
destruct_ac.
intros * Hn.
revert α Hn.
induction n; intros; [ easy | ].
apply angle_mul_nat_div_2π_succ_l_false in Hn.
destruct Hn as (Hmn, Han).
cbn - [ angle_mul_nat_div_2π ].
rewrite Nat.add_0_r.
rewrite Nat.add_succ_r.
rewrite <- Nat_mul_2_l.
apply <- angle_mul_nat_div_2π_succ_l_false.
split. {
  apply <- angle_mul_nat_div_2π_succ_l_false.
  split; [ now apply IHn | ].
  rewrite Nat.mul_comm.
  rewrite <- angle_mul_nat_assoc.
  rewrite angle_div_2_mul_2.
  rewrite angle_add_overflow_comm in Han.
  rewrite angle_add_overflow_comm.
  apply (angle_add_overflow_le _ α); [ | easy ].
  apply angle_div_2_le.
}
rewrite <- Nat.add_1_r.
rewrite angle_mul_add_distr_r.
rewrite angle_mul_1_l.
apply angle_add_not_overflow_move_add. {
  apply angle_add_overflow_div_2_div_2.
}
rewrite <- angle_mul_2_l.
rewrite angle_div_2_mul_2.
rewrite Nat.mul_comm.
rewrite <- angle_mul_nat_assoc.
now rewrite angle_div_2_mul_2.
Qed.

Theorem angle_mul_nat_div_2π_pow_div :
  ∀ n α, angle_mul_nat_div_2π (2 ^ n) (α /₂^n) = 0.
Proof.
destruct_ac.
destruct (Nat.eq_dec (rngl_characteristic T) 1) as [Hc1| Hc1]. {
  intros.
  rewrite (rngl_characteristic_1_angle_0 Hc1 (angle_div_2_pow _ _)).
  apply angle_mul_nat_div_2π_0_r.
}
assert (H2z : (2 ≠ 0)%L) by apply (rngl_2_neq_0 Hos Hc1 Hto).
intros.
revert α.
induction n; intros; cbn; [ now rewrite angle_add_overflow_0_r | ].
destruct n. {
  cbn.
  apply Nat.eq_add_0.
  split; [ now rewrite angle_add_overflow_0_r | ].
  rewrite angle_add_0_r.
  now rewrite angle_add_overflow_div_2_div_2.
}
cbn.
do 2 rewrite Nat.add_0_r.
rewrite Nat.add_assoc.
cbn in IHn.
rewrite Nat.add_0_r in IHn.
specialize (IHn α) as H1.
apply angle_mul_nat_div_2π_mul_2_div_2 in H1.
cbn in H1.
rewrite Nat.add_0_r in H1.
now rewrite Nat.add_assoc in H1.
Qed.

End a.
