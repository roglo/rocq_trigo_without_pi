(* just a file for this theorem:
     (α2 ≤ α3)%A → (α1 + α2 ≤ α1 + α3)%A
 *)

Set Nested Proofs Allowed.
Require Import Stdlib.Arith.Arith.
Require Import RingLike.Utf8.

Require Import RingLike.Core.
Require Import Angle AngleDef TrigoWithoutPiExt.
Require Import AngleAddOverflowLe AngleAddOverflowEquiv.
Require Import Order.
Require Import TacChangeAngle.
Require Import AngleAddLeMonoL_1.
Require Import AngleAddLeMonoL_2.
Require Import AngleAddLeMonoL_3.
Require Export AngleAddLeMonoL_prop.

Section a.

Context {T : Type}.
Context {ro : ring_like_op T}.
Context {rp : ring_like_prop T}.
Context {ac : angle_ctx T}.

Theorem angle_add_le_mono_l :
  ∀ α1 α2 α3,
  angle_add_overflow α1 α3 = false
  → (α2 ≤ α3)%A
  → (α1 + α2 ≤ α1 + α3)%A.
Proof.
destruct_ac.
intros * Haov13 H23.
destruct (rngl_leb_dec 0 (rngl_sin (α1 + α2))) as [Hzs12| Hzs12]. {
  apply rngl_leb_le in Hzs12.
  now apply angle_add_le_mono_l_sin_lb_nonneg.
}
apply (rngl_leb_gt_iff Hto) in Hzs12.
destruct (rngl_leb_dec 0 (rngl_sin α2)) as [Hzs2| Hzs2]. {
  apply rngl_leb_le in Hzs2.
  now apply angle_add_le_mono_l_sin_lb_neg_sin_2_nonneg.
} {
  apply (rngl_leb_gt_iff Hto) in Hzs2.
  now apply angle_add_le_mono_l_sin_lb_neg_sin_2_neg.
}
Qed.

Theorem angle_mul_le_mono_l :
  ∀ α1 α2,
  (α1 ≤ α2)%A
  → ∀ n,
  angle_mul_nat_div_2π n α2 = 0
  → (n * α1 ≤ n * α2)%A.
Proof.
destruct_ac.
intros * H12 * Hn2.
revert α1 α2 H12 Hn2.
induction n; intros; [ apply angle_le_refl | cbn ].
apply angle_mul_nat_div_2π_succ_l_false in Hn2.
destruct Hn2 as (Hn2, H2n2).
generalize Hn2; intros Hn12.
apply (IHn α1) in Hn12; [ | easy ].
apply (angle_le_trans _ (α1 + n * α2))%A. {
  apply angle_add_le_mono_l; [ | easy ].
  rewrite angle_add_overflow_comm.
  apply (angle_add_overflow_le _ α2)%A; [ easy | ].
  now rewrite angle_add_overflow_comm.
} {
  rewrite (angle_add_comm α1).
  rewrite (angle_add_comm α2).
  apply angle_add_le_mono_l; [ | easy ].
  now rewrite angle_add_overflow_comm.
}
Qed.

Theorem angle_mul_le_mono_r :
  ∀ a b α, angle_mul_nat_div_2π b α = 0 → a ≤ b → (a * α ≤ b * α)%A.
Proof.
intros * Hb Hab.
revert a Hab.
induction b; intros. {
  apply Nat.le_0_r in Hab; subst a.
  apply angle_le_refl.
}
destruct a; [ apply angle_nonneg | cbn ].
move a after b.
apply Nat.succ_le_mono in Hab.
apply (angle_mul_nat_div_2π_succ_l_false α b) in Hb.
destruct Hb as (H1, H2).
specialize (IHb H1 _ Hab).
now apply angle_add_le_mono_l.
Qed.

Theorem angle_mul_nat_not_overflow_le_l :
  ∀ m n,
  m ≤ n
  → ∀ α, angle_mul_nat_div_2π n α = 0
  → angle_mul_nat_div_2π m α = 0.
Proof.
destruct_ac.
intros * Hmn * Hn.
revert α m Hmn Hn.
induction n; intros. {
  now apply Nat.le_0_r in Hmn; subst m.
}
apply angle_mul_nat_div_2π_succ_l_false in Hn.
destruct m; [ easy | ].
apply Nat.succ_le_mono in Hmn.
apply angle_mul_nat_div_2π_succ_l_false.
split; [ now apply IHn | ].
apply (angle_add_overflow_le _ (n * α)); [ | easy ].
now apply angle_mul_le_mono_r.
Qed.

Theorem angle_mul_nat_div_2π_le_l :
  ∀ n α,
  angle_mul_nat_div_2π n α ≠ 0
  → ∀ m, n ≤ m → angle_mul_nat_div_2π m α ≠ 0.
Proof.
destruct_ac.
intros * Hn * Hnm.
intros H.
now apply (angle_mul_nat_not_overflow_le_l n) in H.
Qed.

Theorem angle_mul_nat_div_2π_distr_add_overflow :
  ∀ m n α,
  angle_mul_nat_div_2π (m + n) α = 0
  → angle_add_overflow (m * α) (n * α) = false.
Proof.
destruct_ac.
intros * Hmov.
revert n Hmov.
induction m; intros; [ apply angle_add_overflow_0_l | ].
rewrite Nat.add_succ_l in Hmov.
cbn in Hmov.
apply Nat.eq_add_0 in Hmov.
destruct Hmov as (Hmov, Hov).
specialize (IHm _ Hmov) as Hov'.
cbn.
rewrite angle_add_overflow_comm.
apply angle_add_not_overflow_move_add. 2: {
  rewrite <- angle_mul_add_distr_r.
  rewrite Nat.add_comm.
  rewrite angle_add_overflow_comm.
  now destruct (angle_add_overflow α _).
}
now rewrite angle_add_overflow_comm.
Qed.

Theorem angle_mul_nat_div_2π_true_assoc :
  ∀ m n α,
  angle_mul_nat_div_2π m (n * α) ≠ 0
  → angle_mul_nat_div_2π (m * n) α ≠ 0.
Proof.
intros * Hmn.
revert n α Hmn.
induction m; intros; [ easy | cbn ].
cbn in Hmn.
apply Nat_neq_add_0 in Hmn.
destruct Hmn as [Hmn| Hmn]. {
  apply (angle_mul_nat_div_2π_le_l (m * n)); [ now apply IHm | ].
  apply Nat.le_add_l.
}
destruct n. {
  cbn in Hmn.
  now rewrite angle_add_overflow_0_l in Hmn.
}
intros H1; apply Hmn; clear Hmn.
rewrite angle_mul_nat_assoc.
apply angle_mul_nat_div_2π_distr_add_overflow in H1.
now rewrite H1.
Qed.

Theorem angle_mul_nat_div_2π_le_r :
  ∀ α1 α2,
  (α1 ≤ α2)%A
  → ∀ n,
  angle_mul_nat_div_2π n α2 = 0
  → angle_mul_nat_div_2π n α1 = 0.
Proof.
destruct_ac.
intros * H12 * H2.
revert α1 α2 H12 H2.
induction n; intros; [ easy | ].
generalize H2; intros H.
apply angle_mul_nat_div_2π_succ_l_false in H.
destruct H as (Hn2, H2n2).
cbn.
destruct n; [ now cbn; rewrite angle_add_overflow_0_r | ].
apply Nat.eq_add_0.
split; [ now apply (IHn _ α2) | ].
remember (S n) as m eqn:Hm.
clear n Hm; rename m into n.
clear H2 IHn.
rewrite angle_add_overflow_comm.
apply Nat_eq_b2n_0.
eapply angle_add_overflow_le; [ apply H12 | ].
rewrite angle_add_overflow_comm.
eapply angle_add_overflow_le; [ | apply H2n2 ].
now apply angle_mul_le_mono_l.
Qed.

Theorem angle_add_lt_mono_l :
  ∀ α1 α2 α3,
  angle_add_overflow α1 α3 = false
  → (α2 < α3)%A → (α1 + α2 < α1 + α3)%A.
Proof.
intros * H13 H23.
apply angle_lt_iff.
split. {
  apply angle_add_le_mono_l; [ easy | ].
  now apply angle_lt_le_incl in H23.
}
intros H.
apply (f_equal (λ α, (α - α1)%A)) in H.
do 2 rewrite angle_add_comm, angle_add_sub in H.
subst α3.
now apply angle_lt_irrefl in H23.
Qed.

Theorem angle_sub_le_mono_l :
  ∀ α2 α3 α1,
  angle_add_overflow α3 (- α1) = false
  → α1 ≠ 0%A
  → (α1 ≤ α2)%A
  → (α3 - α2 ≤ α3 - α1)%A.
Proof.
intros * Hov H1z H12.
apply angle_add_le_mono_l; [ easy | ].
now apply angle_opp_le_compat_if.
Qed.

Theorem angle_sub_le_mono_l'_lemma_1 :
  ∀ α1 α2 α3,
  (α1 ≤ α2 ≤ α3)%A
  → (0 ≤ rngl_sin (α3 - α2))%L
  → (0 ≤ rngl_sin (α3 - α1))%L
  → (rngl_cos (α3 - α1) ≤ rngl_cos (α3 - α2))%L.
Proof.
destruct_ac.
destruct (Nat.eq_dec (rngl_characteristic T) 1) as [Hc1| Hc1]. {
  specialize (rngl_characteristic_1 Hos Hc1) as H1.
  intros * (H12, H23) Hs32 Hs31.
  rewrite (H1 (rngl_cos _)).
  rewrite (H1 (rngl_cos _)).
  apply (rngl_le_refl Hor).
}
intros * (H12, H23) Hs32 Hs31.
progress unfold angle_leb in H12, H23.
remember (0 ≤? rngl_sin α1)%L as zs1 eqn:Hzs1.
remember (0 ≤? rngl_sin α2)%L as zs2 eqn:Hzs2.
remember (0 ≤? rngl_sin α3)%L as zs3 eqn:Hzs3.
symmetry in Hzs1, Hzs2, Hzs3.
destruct zs1. {
  destruct zs2. {
    destruct zs3. {
      apply rngl_leb_le in Hzs1, Hzs2, H12, Hzs3, H23.
      destruct (rngl_ltb_dec 0 (rngl_sin (α3 - α1))) as [Hs31'| Hs31']. {
        apply (rngl_ltb_lt Heo) in Hs31'.
        apply rngl_sin_sub_nonneg_iff; [ easy | easy | ].
        rewrite angle_sub_sub_distr.
        rewrite angle_sub_sub_swap.
        rewrite angle_sub_diag, angle_sub_0_l.
        rewrite angle_add_opp_l.
        now apply rngl_sin_sub_nonneg.
      }
      destruct (rngl_ltb_dec 0 (rngl_sin (α3 - α2))) as [Hs32'| Hs32']. {
        apply (rngl_ltb_ge_iff Hto) in Hs31'.
        apply (rngl_ltb_lt Heo) in Hs32'.
        apply rngl_sin_sub_nonneg_iff'; [ | easy | easy | ]. {
          apply (rngl_le_antisymm Hor) in Hs31; [ | easy ].
          apply eq_rngl_sin_0 in Hs31.
          destruct Hs31 as [Hs31| Hs31]; [ right | left ]. {
            apply -> angle_sub_move_0_r in Hs31; subst α3.
            intros H; rewrite H in Hs32'.
            now apply (rngl_lt_irrefl) in Hs32'.
          }
          rewrite Hs31.
          apply (angle_straight_neq_0 Hc1).
        }
        rewrite angle_sub_sub_distr.
        rewrite angle_sub_sub_swap.
        rewrite angle_sub_diag, angle_sub_0_l.
        rewrite angle_add_opp_l.
        now apply rngl_sin_sub_nonneg.
      }
      apply (rngl_ltb_ge_iff Hto) in Hs31', Hs32'.
      apply (rngl_le_antisymm Hor) in Hs31; [ | easy ].
      apply (rngl_le_antisymm Hor) in Hs32; [ | easy ].
      clear Hs31' Hs32'.
      apply eq_rngl_sin_0 in Hs32, Hs31.
      destruct Hs32 as [Hs32| Hs32]. {
        apply -> angle_sub_move_0_r in Hs32; subst α3.
        rewrite angle_sub_diag.
        apply rngl_cos_bound.
      }
      rewrite Hs32; cbn - [ angle_sub ].
      destruct Hs31 as [Hs31| Hs31]. {
        exfalso.
        apply -> angle_sub_move_0_r in Hs31; subst α3.
        apply angle_sub_move_r in Hs32; subst α1.
        apply (rngl_le_antisymm Hor) in H12; [ | easy ].
        clear H23 Hzs3.
        rewrite rngl_sin_add_straight_l in Hzs1.
        rewrite rngl_cos_add_straight_l in H12.
        apply (rngl_opp_nonneg_nonpos Hop Hor) in Hzs1.
        apply (rngl_le_antisymm Hor) in Hzs2; [ | easy ].
        clear Hzs1.
        apply eq_rngl_sin_0 in Hzs2.
        destruct Hzs2; subst α2.
        now apply (rngl_opp_1_neq_1 Hop Hc1 Hto) in H12.
        symmetry in H12; cbn in H12.
        rewrite (rngl_opp_involutive Hop) in H12.
        now apply (rngl_opp_1_neq_1 Hop Hc1 Hto) in H12.
      }
      rewrite Hs31; cbn.
      apply (rngl_le_refl Hor).
    }
    clear H23.
    apply rngl_leb_le in Hzs1, Hzs2, H12.
    apply (rngl_leb_gt_iff Hto) in Hzs3.
    change_angle_opp α3.
    progress sin_cos_opp_hyp T Hs31.
    progress sin_cos_opp_hyp T Hs32.
    progress sin_cos_opp_hyp T Hzs3.
    do 2 rewrite <- angle_opp_add_distr.
    do 2 rewrite rngl_cos_opp.
    apply (rngl_opp_nonneg_nonpos Hop Hor) in Hs31, Hs32.
    destruct (rngl_ltb_dec 0 (rngl_cos α1)) as [Hco1| Hco1]. {
      apply (rngl_ltb_lt Heo) in Hco1.
      destruct (rngl_leb_dec 0 (rngl_cos α3)) as [Hco3| Hco3]. {
        apply rngl_leb_le in Hco3.
        exfalso.
        apply (rngl_nlt_ge Hor) in Hs31.
        apply Hs31; clear Hs31.
        now apply rngl_sin_add_pos_1.
      }
      apply (rngl_leb_gt_iff Hto) in Hco3.
      change_angle_sub_l α3 π.
      progress sin_cos_add_sub_straight_hyp T Hzs3.
      progress sin_cos_add_sub_straight_hyp T Hs32.
      progress sin_cos_add_sub_straight_hyp T Hs31.
      progress sin_cos_add_sub_straight_hyp T Hco3.
      progress sin_cos_add_sub_straight_goal T.
      apply rngl_sin_sub_nonneg_iff'; [ | easy | easy | ]. {
        right.
        intros H.
        apply angle_sub_move_r in H; subst α1.
        rewrite rngl_sin_add_straight_l in Hzs1.
        apply (rngl_opp_nonneg_nonpos Hop Hor) in Hzs1.
        now apply (rngl_nlt_ge Hor) in Hzs1.
      }
      rewrite angle_sub_sub_distr.
      rewrite angle_sub_sub_swap.
      rewrite angle_sub_add.
      apply rngl_sin_sub_nonneg_iff'; try easy.
      right; intros H; subst α1.
      apply (rngl_nle_gt Hor) in Hco1.
      apply Hco1; clear Hco1; cbn.
      apply (rngl_opp_1_le_0 Hop Hto).
    }
    apply (rngl_ltb_ge_iff Hto) in Hco1.
    change_angle_sub_l α1 π.
    progress sin_cos_add_sub_straight_hyp T Hzs1.
    progress sin_cos_add_sub_straight_hyp T H12.
    progress sin_cos_add_sub_straight_hyp T Hs31.
    progress sin_cos_add_sub_straight_hyp T Hco1.
    progress sin_cos_add_sub_straight_goal T.
    change_angle_sub_l α2 π.
    progress sin_cos_add_sub_straight_hyp T H12.
    progress sin_cos_add_sub_straight_hyp T Hzs2.
    progress sin_cos_add_sub_straight_hyp T Hs32.
    progress sin_cos_add_sub_straight_goal T.
    apply -> (rngl_le_sub_0 Hop Hor) in H12.
    rewrite rngl_sin_sub_anticomm in Hs31, Hs32.
    apply (rngl_opp_nonpos_nonneg Hop Hor) in Hs31, Hs32.
    do 2 rewrite (rngl_cos_sub_comm _ α3).
    apply rngl_sin_sub_nonneg_iff'; [ | easy | easy | ]. {
      right.
      intros H.
      apply angle_sub_move_r in H; subst α3.
      rewrite rngl_sin_add_straight_l in Hzs3.
      apply (rngl_opp_pos_neg Hop Hor) in Hzs3.
      now apply (rngl_nlt_ge Hor) in Hzs1.
    }
    rewrite angle_sub_sub_distr.
    rewrite angle_sub_sub_swap.
    rewrite angle_sub_diag.
    rewrite angle_sub_0_l.
    rewrite angle_add_opp_l.
    apply rngl_sin_sub_nonneg_iff'; [ | easy | easy | easy ].
    right; intros H; subst α2.
    rewrite rngl_sin_sub_straight_r in Hs32.
    apply (rngl_opp_nonneg_nonpos Hop Hor) in Hs32.
    now apply (rngl_nlt_ge Hor) in Hs32.
  }
  clear H12.
  destruct zs3; [ easy | ].
  apply rngl_leb_le in Hzs1, H23.
  apply (rngl_leb_gt_iff Hto) in Hzs2, Hzs3.
  change_angle_add_r α2 π.
  progress sin_cos_add_sub_straight_hyp T Hzs2.
  progress sin_cos_add_sub_straight_hyp T Hs32.
  progress sin_cos_add_sub_straight_hyp T H23.
  rewrite angle_sub_sub_distr.
  progress sin_cos_add_sub_straight_goal T.
  change_angle_opp α3.
  progress sin_cos_opp_hyp T Hs31.
  progress sin_cos_opp_hyp T H23.
  progress sin_cos_opp_hyp T Hs32.
  progress sin_cos_opp_hyp T Hzs3.
  apply (rngl_opp_nonneg_nonpos Hop Hor) in Hs31.
  apply (rngl_le_opp_l Hop Hor) in H23.
  apply (rngl_opp_nonpos_nonneg Hop Hor) in Hs32.
  do 2 rewrite <- angle_opp_add_distr.
  do 2 rewrite rngl_cos_opp.
  apply (rngl_nlt_ge_iff Hto).
  intros Hcc.
  apply (rngl_nlt_ge Hor) in Hs31.
  apply Hs31; clear Hs31.
  move α2 before α1; move α3 before α2.
  destruct (rngl_ltb_dec 0 (rngl_cos α1)) as [Hzc1| Hzc1]. {
    apply (rngl_ltb_lt Heo) in Hzc1.
    destruct (rngl_leb_dec 0 (rngl_cos α3)) as [Hzc3| Hzc3]. {
      apply rngl_leb_le in Hzc3.
      now apply rngl_sin_add_pos_1.
    }
    apply (rngl_leb_gt_iff Hto) in Hzc3.
    change_angle_sub_l α3 π.
    progress sin_cos_add_sub_straight_hyp T Hcc.
    progress sin_cos_add_sub_straight_hyp T Hzs3.
    progress sin_cos_add_sub_straight_hyp T Hs32.
    progress sin_cos_add_sub_straight_hyp T H23.
    progress sin_cos_add_sub_straight_hyp T Hzc3.
    progress sin_cos_add_sub_straight_goal T.
    rewrite (rngl_add_opp_r Hop) in H23.
    apply -> (rngl_le_0_sub Hop Hor) in H23.
    rewrite rngl_add_0_l.
    rewrite rngl_sin_sub_anticomm in Hs32 |-*.
    apply (rngl_opp_nonpos_nonneg Hop Hor) in Hs32.
    apply (rngl_opp_neg_pos Hop Hor).
    apply rngl_le_neq.
    split. {
      destruct (rngl_leb_dec (rngl_cos α3) (rngl_cos α1)) as [Hc31| Hc31]. {
        apply rngl_leb_le in Hc31.
        apply rngl_sin_sub_nonneg; [ | easy | easy ].
        now apply rngl_lt_le_incl.
      }
      apply (rngl_leb_gt_iff Hto) in Hc31.
      exfalso.
      apply (rngl_nle_gt Hor) in Hcc.
      apply Hcc; clear Hcc.
      rewrite rngl_cos_sub_comm.
      apply (rngl_le_0_add Hos Hor). {
        apply rngl_lt_le_incl in Hzs2, Hzs3, Hzc3.
        apply rngl_cos_sub_nonneg; [ easy | easy | easy | ].
        now apply (rngl_le_trans Hor _ (rngl_cos α3)).
      } {
        apply rngl_lt_le_incl in Hzs3, Hzc3, Hzc1.
        now apply rngl_cos_sub_nonneg.
      }
    }
    intros H; symmetry in H.
    apply eq_rngl_sin_0 in H.
    destruct H as [H| H]. {
      apply -> angle_sub_move_0_r in H; subst α3.
      rewrite angle_sub_diag in Hcc.
      cbn - [ angle_sub ] in Hcc.
      apply (rngl_nle_gt Hor) in Hcc.
      apply Hcc; clear Hcc.
      rewrite rngl_add_comm.
      apply (rngl_le_opp_l Hop Hor).
      apply rngl_cos_bound.
    } {
      apply angle_sub_move_r in H; subst α3.
      rewrite rngl_sin_add_straight_l in Hzs3.
      apply (rngl_opp_pos_neg Hop Hor) in Hzs3.
      now apply (rngl_nle_gt Hor) in Hzs3.
    }
  }
  apply (rngl_ltb_ge_iff Hto) in Hzc1.
  change_angle_sub_l α1 π.
  progress sin_cos_add_sub_straight_hyp T Hzs1.
  progress sin_cos_add_sub_straight_hyp T Hzc1.
  progress sin_cos_add_sub_straight_hyp T Hcc.
  progress sin_cos_add_sub_straight_goal T.
  apply -> (rngl_lt_0_sub Hop Hor) in Hcc.
  destruct (rngl_leb_dec (rngl_cos α1) (rngl_cos α3)) as [Hc13| Hc13]. {
    apply rngl_leb_le in Hc13.
    apply rngl_le_neq.
    split. {
      apply rngl_sin_sub_nonneg; try easy.
      now apply rngl_lt_le_incl.
    }
    intros H; symmetry in H.
    apply eq_rngl_sin_0 in H.
    destruct H as [H| H]. {
      apply -> angle_sub_move_0_r in H; subst α3.
      rewrite angle_sub_diag in Hcc.
      apply (rngl_nle_gt Hor) in Hcc.
      apply Hcc, rngl_cos_bound.
    } {
      apply angle_sub_move_r in H; subst α1.
      rewrite rngl_sin_add_straight_l in Hzs1.
      apply (rngl_opp_nonneg_nonpos Hop Hor) in Hzs1.
      now apply (rngl_nle_gt Hor) in Hzs1.
    }
  }
  apply (rngl_leb_gt_iff Hto) in Hc13.
  exfalso.
  apply (rngl_nle_gt Hor) in Hc13.
  apply Hc13; clear Hc13.
  destruct (rngl_leb_dec 0 (rngl_cos α3)) as [Hzc3| Hzc3]. {
    apply rngl_leb_le in Hzc3.
    destruct (rngl_leb_dec 0 (rngl_cos α2)) as [Hzc2| Hzc2]. {
      apply rngl_leb_le in Hzc2.
      clear H23 Hs32. (* pas utiles *)
      destruct (rngl_leb_dec (rngl_cos α2) (rngl_cos α1)) as [Hc21| Hc21]. {
        apply rngl_leb_le in Hc21.
        apply (rngl_nlt_ge_iff Hto).
        intros Hcc'.
        apply (rngl_nle_gt Hor) in Hcc.
        apply Hcc; clear Hcc.
        apply rngl_lt_le_incl in Hzs2, Hzs3.
        clear - Hto Hor Hop Hzc3 Hc21 Hos Hzs1 Hzs2 Hzs3.
        (* lemma *)
        rewrite rngl_cos_add, rngl_cos_sub.
        apply (rngl_le_sub_le_add_r Hop Hor).
        rewrite <- rngl_add_assoc.
        rewrite <- rngl_mul_add_distr_r.
        apply (rngl_le_sub_le_add_l Hop Hor).
        rewrite <- (rngl_mul_sub_distr_r Hop).
        rewrite rngl_add_comm.
        apply (rngl_le_trans Hor _ 0). {
          apply (rngl_mul_nonpos_nonneg Hop Hor); [ | easy ].
          now apply (rngl_le_sub_0 Hop Hor).
        }
        apply (rngl_mul_nonneg_nonneg Hos Hor); [ | easy ].
        now apply (rngl_le_0_add Hos Hor).
      }
      apply (rngl_leb_gt_iff Hto) in Hc21.
      apply (rngl_nlt_ge_iff Hto).
      intros Hc31.
      apply (rngl_nle_gt Hor) in Hcc.
      apply Hcc; clear Hcc.
      apply (rngl_le_trans Hor _ (rngl_cos α3)). {
        rewrite angle_add_comm.
        apply rngl_lt_le_incl in Hzs2, Hzs3.
        now apply quadrant_1_rngl_cos_add_le_cos_l.
      }
      apply rngl_lt_le_incl in Hzs3, Hc21, Hc31.
      now apply rngl_cos_le_cos_sub.
    }
    apply (rngl_leb_gt_iff Hto) in Hzc2.
    clear H23. (* useless *)
    exfalso.
    apply (rngl_nle_gt Hor) in Hcc.
    apply Hcc; clear Hcc.
    apply (rngl_le_trans Hor _ 0). {
      rewrite rngl_cos_add.
      apply (rngl_le_sub_0 Hop Hor).
      apply (rngl_le_trans Hor _ 0). {
        apply rngl_lt_le_incl in Hzc2.
        now apply (rngl_mul_nonpos_nonneg Hop Hor).
      }
      apply rngl_lt_le_incl in Hzs2, Hzs3.
      now apply (rngl_mul_nonneg_nonneg Hos Hor).
    }
    apply rngl_lt_le_incl in Hzs3.
    now apply rngl_cos_sub_nonneg.
  }
  exfalso.
  apply (rngl_leb_gt_iff Hto) in Hzc3.
  change_angle_sub_l α3 π.
  progress sin_cos_add_sub_straight_hyp T Hzs3.
  progress sin_cos_add_sub_straight_hyp T Hs32.
  progress sin_cos_add_sub_straight_hyp T H23.
  progress sin_cos_add_sub_straight_hyp T Hcc.
  progress sin_cos_add_sub_straight_hyp T Hzc3.
  rewrite (rngl_add_opp_r Hop) in H23.
  apply -> (rngl_le_0_sub Hop Hor) in H23.
  rewrite rngl_sin_sub_anticomm in Hs32.
  apply (rngl_opp_nonpos_nonneg Hop Hor) in Hs32.
  apply (rngl_nle_gt Hor) in Hcc.
  apply Hcc; clear Hcc.
  rewrite rngl_cos_sub_comm.
  replace (α1 + α3)%A with (α3 - α2 + (α2 + α1))%A. 2: {
    rewrite angle_add_assoc.
    rewrite angle_sub_add.
    apply angle_add_comm.
  }
  destruct (rngl_leb_dec 0 (rngl_cos (α1 + α2))) as [Hc12| Hc12]. {
    apply rngl_leb_le in Hc12.
    rewrite angle_add_comm in Hc12.
    apply quadrant_1_rngl_cos_add_le_cos_l; [ easy | | | easy ]. {
      apply rngl_lt_le_incl in Hzs2, Hzc3.
      apply rngl_sin_add_nonneg; [ easy | easy | | easy ].
      now apply (rngl_le_trans Hor _ (rngl_cos α3)).
    } {
      apply rngl_lt_le_incl in Hzs2, Hzs3, Hzc3.
      apply rngl_cos_sub_nonneg; [ easy | easy | easy | ].
      now apply (rngl_le_trans Hor _ (rngl_cos α3)).
    }
  }
  apply (rngl_leb_gt_iff Hto) in Hc12.
  apply rngl_cos_add_le_cos; [ | easy | | ]. {
    left; intros H.
    apply angle_sub_move_r in H; subst α3.
    rewrite rngl_sin_add_straight_l in Hzs3.
    apply (rngl_opp_pos_neg Hop Hor) in Hzs3.
    now apply (rngl_lt_asymm Hor) in Hzs3.
  } {
    apply rngl_lt_le_incl in Hzs2, Hzc3.
    apply rngl_sin_add_nonneg; [ easy | easy | | easy ].
    now apply (rngl_le_trans Hor _ (rngl_cos α3)).
  } {
    rewrite angle_add_assoc, angle_sub_add.
    apply rngl_lt_le_incl in Hzs3, Hzc3.
    now apply rngl_sin_add_nonneg.
  }
}
destruct zs2; [ easy | ].
destruct zs3; [ easy | ].
apply rngl_leb_le in H12, H23.
apply (rngl_leb_gt_iff Hto) in Hzs1, Hzs2, Hzs3.
destruct (rngl_leb_dec 0 (rngl_cos α1)) as [Hzc1| Hzc1]. {
  apply rngl_leb_le in Hzc1.
  change_angle_opp α1.
  progress sin_cos_opp_hyp T Hzs1.
  progress sin_cos_opp_hyp T H12.
  progress sin_cos_opp_hyp T Hzc1.
  progress sin_cos_opp_hyp T Hs31.
  progress sin_cos_opp_goal T.
  change_angle_opp α2.
  progress sin_cos_opp_hyp T H12.
  progress sin_cos_opp_hyp T Hzs2.
  progress sin_cos_opp_hyp T Hs32.
  progress sin_cos_opp_hyp T H23.
  progress sin_cos_opp_goal T.
  change_angle_opp α3.
  progress sin_cos_opp_hyp T H23.
  progress sin_cos_opp_hyp T Hs32.
  progress sin_cos_opp_hyp T Hzs3.
  progress sin_cos_opp_hyp T Hs31.
  progress sin_cos_opp_goal T.
  destruct (angle_eq_dec α1 α2) as [He12| He12]. {
    subst α2; apply (rngl_le_refl Hor).
  }
  apply rngl_sin_sub_nonneg_iff; [ | easy | ]. {
    apply rngl_le_neq.
    split; [ easy | ].
    intros H; symmetry in H.
    apply eq_rngl_sin_0 in H.
    destruct H as [H| H]. {
      apply -> angle_sub_move_0_r in H; subst α3.
      apply (rngl_le_antisymm Hor) in H12; [ | easy ].
      apply rngl_cos_eq in H12.
      destruct H12; subst α2; [ easy | ].
      cbn in Hzs2.
      apply (rngl_opp_pos_neg Hop Hor) in Hzs2.
      now apply (rngl_lt_asymm Hor) in Hzs2.
    } {
      apply angle_sub_move_r in H; subst α1.
      rewrite rngl_sin_add_straight_l in Hzs1.
      apply (rngl_opp_pos_neg Hop Hor) in Hzs1.
      now apply (rngl_lt_asymm Hor) in Hzs1.
    }
  } {
    rewrite angle_sub_sub_distr.
    rewrite <- angle_add_sub_swap.
    rewrite angle_sub_add.
    apply rngl_lt_le_incl in Hzs1, Hzs2.
    now apply rngl_sin_sub_nonneg.
  }
} {
  apply (rngl_leb_gt_iff Hto) in Hzc1.
  change_angle_add_r α1 π.
  progress sin_cos_add_sub_straight_hyp T Hzs1.
  progress sin_cos_add_sub_straight_hyp T H12.
  progress sin_cos_add_sub_straight_hyp T Hzc1.
  progress sin_cos_add_sub_straight_hyp T Hs31.
  rewrite angle_sub_sub_distr.
  progress sin_cos_add_sub_straight_goal T.
  destruct (rngl_leb_dec 0 (rngl_cos α2)) as [Hzc2| Hzc2]. {
    apply rngl_leb_le in Hzc2.
    change_angle_opp α2.
    progress sin_cos_opp_hyp T H12.
    progress sin_cos_opp_hyp T Hzs2.
    progress sin_cos_opp_hyp T Hs32.
    progress sin_cos_opp_hyp T H23.
    progress sin_cos_opp_hyp T Hzc2.
    progress sin_cos_opp_goal T.
    change_angle_opp α3.
    progress sin_cos_opp_hyp T H23.
    progress sin_cos_opp_hyp T Hs32.
    progress sin_cos_opp_hyp T Hzs3.
    progress sin_cos_opp_hyp T Hs31.
    progress sin_cos_opp_goal T.
    apply (rngl_opp_nonpos_nonneg Hop Hor) in Hs31.
    rewrite <- angle_opp_add_distr.
    rewrite rngl_cos_opp.
    rewrite rngl_add_comm.
    apply rngl_add_cos_nonneg_when_sin_nonneg; [ easy | easy | | ]. {
      rewrite angle_add_assoc.
      rewrite <- angle_add_sub_swap.
      rewrite angle_sub_add.
      apply rngl_lt_le_incl in Hzs1, Hzs2, Hzc1.
      now apply rngl_sin_add_nonneg.
    }
    apply rngl_lt_le_incl in Hzs2, Hzs3.
    apply rngl_cos_sub_nonneg; [ easy | easy | easy | ].
    now apply (rngl_le_trans Hor _ (rngl_cos α2)).
  }
  apply (rngl_leb_gt_iff Hto) in Hzc2.
  change_angle_add_r α2 π.
  progress sin_cos_add_sub_straight_hyp T H12.
  progress sin_cos_add_sub_straight_hyp T Hzs2.
  progress sin_cos_add_sub_straight_hyp T Hs32.
  progress sin_cos_add_sub_straight_hyp T H23.
  progress sin_cos_add_sub_straight_hyp T Hzc2.
  rewrite angle_sub_sub_distr.
  progress sin_cos_add_sub_straight_goal T.
  rewrite (rngl_add_opp_l Hop) in H12.
  apply -> (rngl_le_sub_0 Hop Hor) in H12.
  rewrite rngl_sin_sub_anticomm in Hs32, Hs31.
  apply (rngl_opp_nonpos_nonneg Hop Hor) in Hs32, Hs31.
  apply (rngl_le_opp_l Hop Hor) in H23.
  destruct (rngl_leb_dec 0 (rngl_cos α3)) as [Hzc3| Hzc3]. {
    apply rngl_leb_le in Hzc3.
    change_angle_opp α3.
    progress sin_cos_opp_hyp T H23.
    progress sin_cos_opp_hyp T Hs32.
    progress sin_cos_opp_hyp T Hzs3.
    progress sin_cos_opp_hyp T Hs31.
    progress sin_cos_opp_hyp T Hzc3.
    do 2 rewrite <- angle_opp_add_distr, rngl_cos_opp.
    do 2 rewrite (angle_add_comm _ α3).
    rewrite (angle_add_comm _ α3) in Hs32.
    rewrite (angle_add_comm _ α3) in Hs31.
    generalize Hzs2; intros H.
    apply rngl_lt_le_incl in Hzs1, Hzs2, Hzs3.
    apply angle_add_le_mono_l_lemma_3; try easy.
    now apply rngl_sin_add_nonneg_angle_add_not_overflow.
  }
  apply (rngl_leb_gt_iff Hto) in Hzc3.
  change_angle_add_r α3 π.
  progress sin_cos_add_sub_straight_hyp T H23.
  progress sin_cos_add_sub_straight_hyp T Hs32.
  progress sin_cos_add_sub_straight_hyp T Hzs3.
  progress sin_cos_add_sub_straight_hyp T Hs31.
  progress sin_cos_add_sub_straight_hyp T Hzc3.
  progress sin_cos_add_sub_straight_goal T.
  rewrite (rngl_add_opp_r Hop) in H23.
  apply -> (rngl_le_0_sub Hop Hor) in H23.
  rewrite rngl_sin_sub_anticomm in Hs32, Hs31.
  apply (rngl_opp_nonpos_nonneg Hop Hor) in Hs32, Hs31.
  replace (α3 - α1)%A with (α3 - α2 + (α2 - α1))%A. 2: {
    rewrite angle_add_sub_assoc.
    now rewrite angle_sub_add.
  }
  apply rngl_lt_le_incl in Hzs2.
  apply (angle_add_overflow_le_lemma_1 _ α2); try easy. {
    apply rngl_lt_le_incl in Hzs1.
    now apply rngl_sin_sub_nonneg.
  } {
    apply rngl_lt_le_incl in Hzs3.
    now rewrite angle_sub_add.
  } {
    rewrite angle_add_sub_assoc.
    now rewrite angle_sub_add.
  } {
    rewrite rngl_cos_sub_comm.
    apply rngl_lt_le_incl in Hzs1.
    now apply rngl_cos_le_cos_sub.
  } {
    rewrite angle_sub_add.
    rewrite rngl_cos_sub_comm.
    apply rngl_lt_le_incl in Hzs3.
    now apply rngl_cos_le_cos_sub.
  }
}
Qed.

Theorem rngl_cos_le_opp_1 : ∀ α, (rngl_cos α ≤ -1)%L → α = π.
Proof.
destruct_ac.
intros * H1.
apply (rngl_le_antisymm Hor) in H1; [ | apply rngl_cos_bound ].
symmetry in H1.
now apply eq_rngl_cos_opp_1 in H1.
Qed.

(* to be completed
Theorem angle_sub_le_mono_l'_lemma_2 :
  ∀ α1 α2 α3,
  (α1 ≤ α2 ≤ α3)%A
  → (0 < rngl_sin (α2 - α3))%L
  → (0 < rngl_sin (α1 - α3))%L
  → (rngl_cos (α2 - α3) ≤ rngl_cos (α1 - α3))%L.
Proof.
destruct_ac.
destruct (Nat.eq_dec (rngl_characteristic T) 1) as [Hc1| Hc1]. {
  specialize (rngl_characteristic_1 Hos Hc1) as H1.
  intros * (H12, H23) Hs23 Hs13.
  rewrite (H1 (rngl_cos _)).
  rewrite (H1 (rngl_cos _)).
  apply (rngl_le_refl Hor).
}
intros * (H12, H23) Hs23 Hs13.
destruct (angle_eq_dec α2 0) as [H2z| H2z]. {
  subst α2.
  apply angle_nonpos in H12; subst α1.
  apply (rngl_le_refl Hor).
}
destruct (angle_eq_dec α3 0) as [H3z| H3z]. {
  subst α3.
  apply angle_nonpos in H23; subst α2.
  apply angle_nonpos in H12; subst α1.
  apply (rngl_le_refl Hor).
}
destruct (angle_eq_dec α2 π) as [H2p| H2p]. {
  subst α2.
  rewrite rngl_sin_sub_straight_l in Hs23.
  progress unfold angle_leb in H23.
  cbn in H23.
  rewrite (rngl_leb_refl Hor) in H23.
  generalize Hs23; intros H.
  apply rngl_lt_le_incl in H.
  apply rngl_leb_le in H.
  rewrite H in H23; clear H.
  apply rngl_leb_le in H23.
  apply rngl_cos_le_opp_1 in H23; subst α3.
  now apply rngl_lt_irrefl in Hs23.
}
progress unfold angle_leb in H12, H23.
remember (0 ≤? rngl_sin α1)%L as zs1 eqn:Hzs1.
remember (0 ≤? rngl_sin α2)%L as zs2 eqn:Hzs2.
remember (0 ≤? rngl_sin α3)%L as zs3 eqn:Hzs3.
symmetry in Hzs1, Hzs2, Hzs3.
destruct zs1. {
  destruct zs2. {
    destruct zs3. {
      apply rngl_leb_le in Hzs1, Hzs2, H12, Hzs3, H23.
      apply rngl_sin_sub_nonneg_iff; [ easy | | ]. {
        now apply rngl_lt_le_incl.
      }
      rewrite angle_sub_sub_distr.
      rewrite <- angle_add_sub_swap.
      rewrite angle_sub_add.
      apply rngl_sin_sub_nonneg_iff; [ | easy | easy ].
      apply rngl_le_neq.
      split; [ easy | ].
      intros H; symmetry in H.
      apply eq_rngl_sin_0 in H.
      now destruct H.
    }
    clear H23.
    apply rngl_leb_le in Hzs1, Hzs2, H12.
    apply (rngl_leb_gt_iff Hto) in Hzs3.
    change_angle_opp α3.
    progress sin_cos_opp_hyp T Hs13.
    progress sin_cos_opp_hyp T Hs23.
    progress sin_cos_opp_hyp T Hzs3.
    progress sin_cos_opp_goal T.
    do 2 rewrite (angle_add_comm _ α3).
    rewrite (angle_add_comm _ α3) in Hs13.
    rewrite (angle_add_comm _ α3) in Hs23.
    apply rngl_lt_le_incl in Hs13, Hs23.
    apply angle_add_le_mono_l_lemma_3; try easy.
    apply rngl_lt_le_incl in Hzs3.
    apply rngl_sin_add_nonneg_angle_add_not_overflow; try easy.
    apply rngl_le_neq.
    split; [ easy | ].
    intros H; symmetry in H.
    apply eq_rngl_sin_0 in H.
    now destruct H.
  }
  clear H12.
  destruct zs3; [ easy | ].
  apply rngl_leb_le in Hzs1, H23.
  apply (rngl_leb_gt_iff Hto) in Hzs2, Hzs3.
  destruct (rngl_leb_dec 0 (rngl_cos α2)) as [Hzc2| Hzc2]. {
    apply rngl_leb_le in Hzc2.
    change_angle_opp α2.
    progress sin_cos_opp_hyp T Hzs2.
    progress sin_cos_opp_hyp T Hs23.
    progress sin_cos_opp_hyp T H23.
    progress sin_cos_opp_hyp T Hzc2.
    rewrite <- angle_opp_add_distr.
    rewrite rngl_cos_opp.
    move α2 before α1.
    destruct (rngl_leb_dec 0 (rngl_cos α3)) as [Hzc3| Hzc3]. {
      apply rngl_leb_le in Hzc3.
      change_angle_opp α3.
      progress sin_cos_opp_hyp T Hs13.
      progress sin_cos_opp_hyp T H23.
      progress sin_cos_opp_hyp T Hs23.
      progress sin_cos_opp_hyp T Hzs3.
      progress sin_cos_opp_hyp T Hzc3.
      progress sin_cos_opp_goal T.
      rewrite <- rngl_sin_sub_anticomm in Hs23.
      rewrite rngl_cos_sub_comm.
      exfalso.
      apply (rngl_nlt_ge Hor) in H23.
      apply H23; clear H23.
      apply rngl_lt_le_incl in Hzs2, Hzs3.
      now apply quadrant_1_sin_sub_pos_cos_lt.
    }
    apply (rngl_leb_gt_iff Hto) in Hzc3.
    change_angle_add_r α3 π.
    rewrite angle_sub_sub_distr.
    progress sin_cos_add_sub_straight_hyp T Hs13.
    progress sin_cos_add_sub_straight_hyp T H23.
    progress sin_cos_add_sub_straight_hyp T Hs23.
    progress sin_cos_add_sub_straight_hyp T Hzs3.
    progress sin_cos_add_sub_straight_hyp T Hzc3.
    progress sin_cos_add_sub_straight_goal T.
    rewrite rngl_add_0_r in Hs23.
    exfalso.
    apply (rngl_nlt_ge Hor) in H23.
    apply H23; clear H23.
    now apply (rngl_add_nonneg_pos Hos Hor).
  }
  apply (rngl_leb_gt_iff Hto) in Hzc2.
  change_angle_add_r α2 π.
  progress sin_cos_add_sub_straight_hyp T Hzs2.
  progress sin_cos_add_sub_straight_hyp T Hs23.
  progress sin_cos_add_sub_straight_hyp T H23.
  progress sin_cos_add_sub_straight_hyp T Hzc2.
  progress sin_cos_add_sub_straight_goal T.
  rewrite rngl_sin_sub_anticomm in Hs23.
  apply (rngl_opp_neg_pos Hop Hor) in Hs23.
  apply (rngl_le_opp_l Hop Hor) in H23.
  move α2 before α1.
  destruct (rngl_leb_dec 0 (rngl_cos α3)) as [Hzc3| Hzc3]. {
    apply rngl_leb_le in Hzc3.
    change_angle_opp α3.
    progress sin_cos_opp_hyp T Hs13.
    progress sin_cos_opp_hyp T H23.
    progress sin_cos_opp_hyp T Hs23.
    progress sin_cos_opp_hyp T Hzs3.
    progress sin_cos_opp_hyp T Hzc3.
    exfalso.
    apply (rngl_nle_gt Hor) in Hs23.
    apply Hs23; clear Hs23.
    apply (rngl_opp_nonpos_nonneg Hop Hor).
    apply rngl_lt_le_incl in Hzs2, Hzs3, Hzc2.
    now apply rngl_sin_add_nonneg.
  }
  apply (rngl_leb_gt_iff Hto) in Hzc3.
  change_angle_add_r α3 π.
  progress sin_cos_add_sub_straight_hyp T Hs13.
  progress sin_cos_add_sub_straight_hyp T H23.
  progress sin_cos_add_sub_straight_hyp T Hs23.
  progress sin_cos_add_sub_straight_hyp T Hzs3.
  progress sin_cos_add_sub_straight_hyp T Hzc3.
  do 2 rewrite angle_sub_sub_distr.
  progress sin_cos_add_sub_straight_goal T.
  rewrite (rngl_add_opp_r Hop) in H23.
  apply -> (rngl_le_0_sub Hop Hor) in H23.
  exfalso.
  apply (rngl_nle_gt Hor) in Hs23.
  apply Hs23; clear Hs23.
  apply rngl_lt_le_incl in Hzs2, Hzs3.
  now apply rngl_sin_sub_nonneg.
}
destruct zs2; [ easy | ].
destruct zs3; [ easy | ].
apply rngl_leb_le in H12, H23.
apply (rngl_leb_gt_iff Hto) in Hzs1, Hzs2, Hzs3.
...
destruct (rngl_leb_dec 0 (rngl_cos α1)) as [Hzc1| Hzc1]. {
  apply rngl_leb_le in Hzc1.
  change_angle_opp α1.
  progress sin_cos_opp_hyp T Hzs1.
  progress sin_cos_opp_hyp T H12.
  progress sin_cos_opp_hyp T Hzc1.
  progress sin_cos_opp_hyp T Hs31.
  progress sin_cos_opp_goal T.
  change_angle_opp α2.
  progress sin_cos_opp_hyp T H12.
  progress sin_cos_opp_hyp T Hzs2.
  progress sin_cos_opp_hyp T Hs32.
  progress sin_cos_opp_hyp T H23.
  progress sin_cos_opp_goal T.
  change_angle_opp α3.
  progress sin_cos_opp_hyp T H23.
  progress sin_cos_opp_hyp T Hs32.
  progress sin_cos_opp_hyp T Hzs3.
  progress sin_cos_opp_hyp T Hs31.
  progress sin_cos_opp_goal T.
  destruct (angle_eq_dec α1 α2) as [He12| He12]. {
    subst α2; apply (rngl_le_refl Hor).
  }
  apply rngl_sin_sub_nonneg_iff; [ | easy | ]. {
    apply rngl_le_neq.
    split; [ easy | ].
    intros H; symmetry in H.
    apply eq_rngl_sin_0 in H.
    destruct H as [H| H]. {
      apply -> angle_sub_move_0_r in H; subst α3.
      apply (rngl_le_antisymm Hor) in H12; [ | easy ].
      apply rngl_cos_eq in H12.
      destruct H12; subst α2; [ easy | ].
      cbn in Hzs2.
      apply (rngl_opp_pos_neg Hop Hor) in Hzs2.
      now apply (rngl_lt_asymm Hor) in Hzs2.
    } {
      apply angle_sub_move_r in H; subst α1.
      rewrite rngl_sin_add_straight_l in Hzs1.
      apply (rngl_opp_pos_neg Hop Hor) in Hzs1.
      now apply (rngl_lt_asymm Hor) in Hzs1.
    }
  } {
    rewrite angle_sub_sub_distr.
    rewrite <- angle_add_sub_swap.
    rewrite angle_sub_add.
    apply rngl_lt_le_incl in Hzs1, Hzs2.
    now apply rngl_sin_sub_nonneg.
  }
} {
  apply (rngl_leb_gt_iff Hto) in Hzc1.
  change_angle_add_r α1 π.
  progress sin_cos_add_sub_straight_hyp T Hzs1.
  progress sin_cos_add_sub_straight_hyp T H12.
  progress sin_cos_add_sub_straight_hyp T Hzc1.
  progress sin_cos_add_sub_straight_hyp T Hs31.
  rewrite angle_sub_sub_distr.
  progress sin_cos_add_sub_straight_goal T.
  destruct (rngl_leb_dec 0 (rngl_cos α2)) as [Hzc2| Hzc2]. {
    apply rngl_leb_le in Hzc2.
    change_angle_opp α2.
    progress sin_cos_opp_hyp T H12.
    progress sin_cos_opp_hyp T Hzs2.
    progress sin_cos_opp_hyp T Hs32.
    progress sin_cos_opp_hyp T H23.
    progress sin_cos_opp_hyp T Hzc2.
    progress sin_cos_opp_goal T.
    change_angle_opp α3.
    progress sin_cos_opp_hyp T H23.
    progress sin_cos_opp_hyp T Hs32.
    progress sin_cos_opp_hyp T Hzs3.
    progress sin_cos_opp_hyp T Hs31.
    progress sin_cos_opp_goal T.
    apply (rngl_opp_nonpos_nonneg Hop Hor) in Hs31.
    rewrite <- angle_opp_add_distr.
    rewrite rngl_cos_opp.
    rewrite rngl_add_comm.
    apply rngl_add_cos_nonneg_when_sin_nonneg; [ easy | easy | | ]. {
      rewrite angle_add_assoc.
      rewrite <- angle_add_sub_swap.
      rewrite angle_sub_add.
      apply rngl_lt_le_incl in Hzs1, Hzs2, Hzc1.
      now apply rngl_sin_add_nonneg.
    }
    apply rngl_lt_le_incl in Hzs2, Hzs3.
    apply rngl_cos_sub_nonneg; [ easy | easy | easy | ].
    now apply (rngl_le_trans Hor _ (rngl_cos α2)).
  }
  apply (rngl_leb_gt_iff Hto) in Hzc2.
  change_angle_add_r α2 π.
  progress sin_cos_add_sub_straight_hyp T H12.
  progress sin_cos_add_sub_straight_hyp T Hzs2.
  progress sin_cos_add_sub_straight_hyp T Hs32.
  progress sin_cos_add_sub_straight_hyp T H23.
  progress sin_cos_add_sub_straight_hyp T Hzc2.
  rewrite angle_sub_sub_distr.
  progress sin_cos_add_sub_straight_goal T.
  rewrite (rngl_add_opp_l Hop) in H12.
  apply -> (rngl_le_sub_0 Hop Hor) in H12.
  rewrite rngl_sin_sub_anticomm in Hs32, Hs31.
  apply (rngl_opp_nonpos_nonneg Hop Hor) in Hs32, Hs31.
  apply (rngl_le_opp_l Hop Hor) in H23.
  destruct (rngl_leb_dec 0 (rngl_cos α3)) as [Hzc3| Hzc3]. {
    apply rngl_leb_le in Hzc3.
    change_angle_opp α3.
    progress sin_cos_opp_hyp T H23.
    progress sin_cos_opp_hyp T Hs32.
    progress sin_cos_opp_hyp T Hzs3.
    progress sin_cos_opp_hyp T Hs31.
    progress sin_cos_opp_hyp T Hzc3.
    do 2 rewrite <- angle_opp_add_distr, rngl_cos_opp.
    do 2 rewrite (angle_add_comm _ α3).
    rewrite (angle_add_comm _ α3) in Hs32.
    rewrite (angle_add_comm _ α3) in Hs31.
    generalize Hzs2; intros H.
    apply rngl_lt_le_incl in Hzs1, Hzs2, Hzs3.
    apply angle_add_le_mono_l_lemma_3; try easy.
    now apply rngl_sin_add_nonneg_angle_add_not_overflow.
  }
  apply (rngl_leb_gt_iff Hto) in Hzc3.
  change_angle_add_r α3 π.
  progress sin_cos_add_sub_straight_hyp T H23.
  progress sin_cos_add_sub_straight_hyp T Hs32.
  progress sin_cos_add_sub_straight_hyp T Hzs3.
  progress sin_cos_add_sub_straight_hyp T Hs31.
  progress sin_cos_add_sub_straight_hyp T Hzc3.
  progress sin_cos_add_sub_straight_goal T.
  rewrite (rngl_add_opp_r Hop) in H23.
  apply -> (rngl_le_0_sub Hop Hor) in H23.
  rewrite rngl_sin_sub_anticomm in Hs32, Hs31.
  apply (rngl_opp_nonpos_nonneg Hop Hor) in Hs32, Hs31.
  replace (α3 - α1)%A with (α3 - α2 + (α2 - α1))%A. 2: {
    rewrite angle_add_sub_assoc.
    now rewrite angle_sub_add.
  }
  apply rngl_lt_le_incl in Hzs2.
  apply (angle_add_overflow_le_lemma_1 _ α2); try easy. {
    apply rngl_lt_le_incl in Hzs1.
    now apply rngl_sin_sub_nonneg.
  } {
    apply rngl_lt_le_incl in Hzs3.
    now rewrite angle_sub_add.
  } {
    rewrite angle_add_sub_assoc.
    now rewrite angle_sub_add.
  } {
    rewrite rngl_cos_sub_comm.
    apply rngl_lt_le_incl in Hzs1.
    now apply rngl_cos_le_cos_sub.
  } {
    rewrite angle_sub_add.
    rewrite rngl_cos_sub_comm.
    apply rngl_lt_le_incl in Hzs3.
    now apply rngl_cos_le_cos_sub.
  }
}
Qed.
...

Theorem angle_sub_le_mono_l' :
  ∀ α1 α2 α3,
  (α1 ≤ α2 ≤ α3)%A
  → (α3 - α2 ≤ α3 - α1)%A.
Proof.
destruct_ac.
destruct (Nat.eq_dec (rngl_characteristic T) 1) as [Hc1| Hc1]. {
  specialize (rngl_characteristic_1_angle_0 Hc1) as H1.
  intros * (H12, H23).
  rewrite (H1 α2), (H1 α1).
  apply angle_le_refl.
}
intros * (H12, H23).
destruct (angle_eq_dec α2 0) as [H2z| H2z]. {
  subst α2.
  apply angle_nonpos in H12; subst α1.
  apply angle_le_refl.
}
destruct (angle_eq_dec α3 0) as [H3z| H3z]. {
  subst α3.
  apply angle_nonpos in H23; subst α2.
  apply angle_nonpos in H12; subst α1.
  apply angle_le_refl.
}
progress unfold angle_leb.
remember (0 ≤? rngl_sin (α3 - α2))%L as s32 eqn:Hs32.
remember (0 ≤? rngl_sin (α3 - α1))%L as s31 eqn:Hs31.
symmetry in Hs32, Hs31.
destruct s32. {
  destruct s31; [ | easy ].
  apply rngl_leb_le in Hs32, Hs31.
  apply rngl_leb_le.
  now apply angle_sub_le_mono_l'_lemma_1.
}
apply (rngl_leb_gt_iff Hto) in Hs32.
rewrite rngl_sin_sub_anticomm in Hs32.
apply (rngl_opp_neg_pos Hop Hor) in Hs32.
destruct s31. {
  exfalso.
  apply rngl_leb_le in Hs31.
  progress unfold angle_leb in H12, H23.
  remember (0 ≤? rngl_sin α1)%L as zs1 eqn:Hzs1.
  remember (0 ≤? rngl_sin α2)%L as zs2 eqn:Hzs2.
  remember (0 ≤? rngl_sin α3)%L as zs3 eqn:Hzs3.
  symmetry in Hzs1, Hzs2, Hzs3.
  destruct zs2. {
    apply rngl_leb_le in Hzs2.
    destruct zs1; [ | easy ].
    apply rngl_leb_le in Hzs1, H12.
    destruct zs3. {
      apply rngl_leb_le in Hzs3, H23.
      apply (rngl_nle_gt Hor) in Hs32.
      apply Hs32; clear Hs32.
      rewrite rngl_sin_sub_anticomm.
      apply (rngl_opp_nonpos_nonneg Hop Hor).
      now apply rngl_sin_sub_nonneg.
    }
    apply (rngl_leb_gt_iff Hto) in Hzs3.
    clear H23.
    change_angle_add_r α3 π.
    progress sin_cos_add_sub_straight_hyp T Hs31.
    progress sin_cos_add_sub_straight_hyp T Hs32.
    progress sin_cos_add_sub_straight_hyp T Hzs3.
    rewrite rngl_sin_sub_anticomm in Hs31, Hs32.
    apply (rngl_opp_nonpos_nonneg Hop Hor) in Hs31.
    apply (rngl_opp_neg_pos Hop Hor) in Hs32.
    apply (rngl_nlt_ge Hor) in H12.
    apply H12; clear H12.
    destruct (angle_eq_dec α1 π) as [H1p| H1p]. {
      subst α1.
      rewrite rngl_sin_sub_straight_l in Hs31.
      cbn.
      apply rngl_le_neq.
      split; [ apply rngl_cos_bound | ].
      intros H.
      symmetry in H.
...
      apply eq_rngl_cos_opp_1 in H; subst α2.
      rewrite rngl_sin_sub_straight_r in Hs32.
      apply (rngl_opp_pos_neg Hop Hor) in Hs32.
      now apply (rngl_nle_gt Hor) in Hs32.
    }
    apply (rngl_le_lt_trans Hor _ (rngl_cos α3)). {
      generalize Hzs3; intros Hzs3'.
      apply rngl_lt_le_incl in Hzs3'.
      apply rngl_sin_sub_nonneg_iff; [ | easy | easy ].
      apply rngl_le_neq.
      split; [ easy | ].
      intros H; symmetry in H.
      apply eq_rngl_sin_0 in H.
      destruct H; subst α1; [ | easy ].
      rewrite angle_sub_0_l in Hs31.
      cbn in Hs31.
      apply (rngl_opp_nonneg_nonpos Hop Hor) in Hs31.
      now apply (rngl_nlt_ge Hor) in Hs31.
    }
    apply rngl_le_neq.
    split. {
      apply rngl_lt_le_incl in Hs32.
      now apply rngl_sin_sub_nonneg_iff.
    }
    intros H.
    apply rngl_cos_eq in H.
    destruct H; subst α3. {
      rewrite angle_sub_diag in Hs32.
      now apply rngl_lt_irrefl in Hs32.
    }
    cbn in Hzs3.
    apply (rngl_opp_pos_neg Hop Hor) in Hzs3.
    now apply (rngl_nle_gt Hor) in Hzs3.
  }
  destruct zs3; [ easy | ].
  apply (rngl_leb_gt_iff Hto) in Hzs2, Hzs3.
  apply rngl_leb_le in H23.
  change_angle_opp α2.
  progress sin_cos_opp_hyp T Hzs2.
  progress sin_cos_opp_hyp T H23.
  progress sin_cos_opp_hyp T Hs32.
  change_angle_opp α3.
  progress sin_cos_opp_hyp T Hzs3.
  progress sin_cos_opp_hyp T H23.
  progress sin_cos_opp_hyp T Hs32.
  apply (rngl_nle_gt Hor) in Hs32.
  apply Hs32; clear Hs32.
  apply (rngl_opp_nonpos_nonneg Hop Hor).
  apply rngl_lt_le_incl in Hzs2, Hzs3.
  now apply rngl_sin_sub_nonneg.
}
apply (rngl_leb_gt_iff Hto) in Hs31.
apply rngl_leb_le.
do 2 rewrite (rngl_cos_sub_comm α3).
rewrite rngl_sin_sub_anticomm in Hs31.
apply (rngl_opp_neg_pos Hop Hor) in Hs31.
... ...
now apply angle_sub_le_mono_l'_lemma_2.
...
*)

End a.
