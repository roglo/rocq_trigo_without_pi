Set Nested Proofs Allowed.
From Stdlib Require Import Utf8 Arith.

Require Import RingLike.Core.
Require Import RingLike.RealLike.

Require Import Core.
Require Import Angle.

Section a.

Context {T : Type}.
Context {ro : ring_like_op T}.
Context {rp : ring_like_prop T}.
Context {rl : real_like_prop T}.
Context {ac : angle_ctx T}.

Definition angle_leb θ1 θ2 :=
  if (0 ≤? rngl_sin θ1)%L then
    if (0 ≤? rngl_sin θ2)%L then (rngl_cos θ2 ≤? rngl_cos θ1)%L
    else true
  else
    if (0 ≤? rngl_sin θ2)%L then false
    else (rngl_cos θ1 ≤? rngl_cos θ2)%L.

End a.

Notation "θ1 ≤? θ2" := (angle_leb θ1 θ2) : angle_scope.
Notation "θ1 <? θ2" := (angle_ltb θ1 θ2) : angle_scope.
Notation "θ1 ≤ θ2" := (angle_leb θ1 θ2 = true) : angle_scope.
Notation "θ1 ≤ θ2 < θ3" :=
  (angle_leb θ1 θ2 = true ∧ angle_ltb θ2 θ3 = true) : angle_scope.
Notation "θ1 ≤ θ2 ≤ θ3" :=
  (angle_leb θ1 θ2 = true ∧ angle_leb θ2 θ3 = true) : angle_scope.
Notation "θ1 < θ2 < θ3" :=
  (angle_ltb θ1 θ2 = true ∧ angle_ltb θ2 θ3 = true) : angle_scope.
Notation "θ1 < θ2 ≤ θ3" :=
  (angle_ltb θ1 θ2 = true ∧ angle_leb θ2 θ3 = true) : angle_scope.

Section a.

Context {T : Type}.
Context {ro : ring_like_op T}.
Context {rp : ring_like_prop T}.
Context {rl : real_like_prop T}.
Context {ac : angle_ctx T}.

Theorem angle_lt_iff : ∀ θ1 θ2, (θ1 < θ2 ↔ θ1 ≤ θ2 ∧ θ1 ≠ θ2)%A.
Proof.
destruct_ac; intros.
progress unfold angle_ltb.
progress unfold angle_leb.
remember (0 ≤? rngl_sin θ1)%L as zs1 eqn:Hzs1.
remember (0 ≤? rngl_sin θ2)%L as zs2 eqn:Hzs2.
symmetry in Hzs1, Hzs2.
destruct zs1. {
  apply rngl_leb_le in Hzs1.
  destruct zs2. {
    apply rngl_leb_le in Hzs2.
    split; intros H12. {
      apply rngl_ltb_lt in H12.
      split. {
        apply rngl_leb_le.
        now apply (rngl_lt_le_incl Hor).
      }
      intros H; subst θ2.
      now apply (rngl_lt_irrefl Hor) in H12.
    } {
      destruct H12 as (Hc12, H12).
      apply rngl_leb_le in Hc12.
      apply rngl_ltb_lt.
      apply (rngl_le_neq Hor).
      split; [ easy | ].
      intros H; symmetry in H.
      apply rngl_cos_eq in H.
      destruct H as [H| H]; [ easy | ].
      subst θ1.
      apply (rngl_opp_nonneg_nonpos Hop Hor) in Hzs1.
      apply (rngl_le_antisymm Hor) in Hzs2; [ | easy ].
      apply eq_rngl_sin_0 in Hzs2.
      destruct Hzs2; subst θ2. {
        apply H12.
        apply eq_angle_eq; cbn.
        now rewrite rngl_opp_0.
      } {
        apply H12.
        apply eq_angle_eq; cbn.
        now rewrite rngl_opp_0.
      }
    }
  }
  split; [ | easy ].
  intros _.
  split; [ easy | ].
  apply (rngl_leb_gt Hor) in Hzs2.
  apply rngl_nle_gt in Hzs2.
  now intros H; subst θ2.
} {
  apply (rngl_leb_gt Hor) in Hzs1.
  destruct zs2; [ easy | ].
  apply (rngl_leb_gt Hor) in Hzs2.
  split; intros H12. {
    apply rngl_ltb_lt in H12.
    split. {
      apply rngl_leb_le.
      now apply (rngl_lt_le_incl Hor).
    }
    intros H; subst θ2.
    now apply (rngl_lt_irrefl Hor) in H12.
  }
  destruct H12 as (Hc12, H12).
  apply rngl_leb_le in Hc12.
  apply rngl_ltb_lt.
  apply (rngl_le_neq Hor).
  split; [ easy | ].
  intros H; apply H12; clear H12.
  apply rngl_cos_eq in H.
  destruct H; subst θ1; [ easy | ].
  cbn in Hzs1.
  apply (rngl_opp_neg_pos Hop Hor) in Hzs1.
  now apply (rngl_lt_le_incl Hor), rngl_nlt_ge in Hzs1.
}
Qed.

Theorem angle_nlt_ge : ∀ θ1 θ2, ¬ (θ1 < θ2)%A ↔ (θ2 ≤ θ1)%A.
Proof.
destruct_ac.
intros.
progress unfold angle_ltb.
progress unfold angle_leb.
destruct (0 ≤? rngl_sin θ1)%L. {
  destruct (0 ≤? rngl_sin θ2)%L; [ | easy ].
  split; intros H. {
    apply Bool.not_true_iff_false in H.
    apply (rngl_ltb_ge_iff Hor) in H.
    now apply rngl_leb_le.
  }
  apply Bool.not_true_iff_false.
  apply rngl_ltb_ge.
  now apply rngl_leb_le.
}
destruct (0 ≤? rngl_sin θ2)%L; [ easy | ].
split; intros H. {
  apply Bool.not_true_iff_false in H.
  apply (rngl_ltb_ge_iff Hor) in H.
  now apply rngl_leb_le.
}
apply Bool.not_true_iff_false.
apply rngl_ltb_ge.
now apply rngl_leb_le.
Qed.

Theorem angle_nle_gt : ∀ θ1 θ2, (θ1 ≤? θ2)%A ≠ true ↔ (θ2 < θ1)%A.
Proof.
destruct_ac.
intros.
progress unfold angle_ltb.
progress unfold angle_leb.
destruct (0 ≤? rngl_sin θ1)%L. {
  destruct (0 ≤? rngl_sin θ2)%L; [ | easy ].
  split; intros H. {
    apply Bool.not_true_iff_false in H.
    apply (rngl_leb_gt Hor) in H.
    now apply rngl_ltb_lt.
  }
  apply Bool.not_true_iff_false.
  apply (rngl_leb_gt Hor).
  now apply rngl_ltb_lt.
}
destruct (0 ≤? rngl_sin θ2)%L; [ easy | ].
split; intros H. {
  apply Bool.not_true_iff_false in H.
  apply (rngl_leb_gt Hor) in H.
  now apply rngl_ltb_lt.
}
apply Bool.not_true_iff_false.
apply (rngl_leb_gt Hor).
now apply rngl_ltb_lt.
Qed.

Theorem angle_straight_pos :
  rngl_characteristic T ≠ 1 → (0 < angle_straight)%A.
Proof.
destruct_ac.
intros Hc1.
progress unfold angle_ltb.
cbn.
rewrite (rngl_leb_refl Hor).
apply rngl_ltb_lt.
apply (rngl_opp_1_lt_1 Hon Hop Hiq Hor Hc1).
Qed.

Theorem angle_straight_nonneg : (0 ≤ angle_straight)%A.
Proof.
destruct_ac.
progress unfold angle_leb.
cbn.
rewrite (rngl_leb_refl Hor).
apply rngl_leb_le.
apply (rngl_opp_1_le_1 Hon Hop Hiq Hor).
Qed.

Theorem angle_leb_gt : ∀ θ1 θ2, (θ1 ≤? θ2)%A = false ↔ (θ2 < θ1)%A.
Proof.
destruct_ac.
intros.
progress unfold angle_leb.
progress unfold angle_ltb.
remember (0 ≤? rngl_sin θ1)%L as zs1 eqn:Hzs1.
remember (0 ≤? rngl_sin θ2)%L as zs2 eqn:Hzs2.
symmetry in Hzs1, Hzs2.
destruct zs1. {
  apply rngl_leb_le in Hzs1.
  destruct zs2; [ | easy ].
  apply rngl_leb_le in Hzs2.
  split; intros H12. {
    apply (rngl_leb_gt Hor) in H12.
    now apply rngl_ltb_lt.
  } {
    apply (rngl_leb_gt Hor).
    now apply rngl_ltb_lt in H12.
  }
} {
  apply (rngl_leb_gt Hor) in Hzs1.
  destruct zs2; [ easy | ].
  split; intros H12. {
    apply (rngl_leb_gt Hor) in H12.
    now apply rngl_ltb_lt.
  } {
    apply (rngl_leb_gt Hor).
    now apply rngl_ltb_lt in H12.
  }
}
Qed.

Theorem angle_lt_irrefl : ∀ θ, ¬ (θ < θ)%A.
Proof.
destruct_ac.
intros * H.
progress unfold angle_ltb in H.
remember (0 ≤? rngl_sin θ)%L as zs eqn:Hzs.
symmetry in Hzs.
destruct zs. {
  apply rngl_ltb_lt in H.
  now apply (rngl_lt_irrefl Hor) in H.
} {
  apply rngl_ltb_lt in H.
  now apply (rngl_lt_irrefl Hor) in H.
}
Qed.

Theorem angle_le_refl : ∀ θ, (θ ≤? θ)%A = true.
Proof.
intros.
destruct_ac.
progress unfold angle_leb.
remember (0 ≤? rngl_sin θ)%L as zs eqn:Hzs.
symmetry in Hzs.
destruct zs; apply (rngl_leb_refl Hor).
Qed.

Theorem angle_nonneg : ∀ θ, (0 ≤ θ)%A.
Proof.
destruct_ac; intros.
progress unfold angle_leb.
cbn.
rewrite (rngl_leb_refl Hor).
destruct (0 ≤? rngl_sin θ)%L; [ | easy ].
apply rngl_leb_le.
apply rngl_cos_bound.
Qed.

Theorem angle_le_rngl_sin_nonneg_sin_nonneg :
  ∀ θ1 θ2,
  (θ2 ≤ θ1)%A
  → (0 ≤ rngl_sin θ1)%L
  → (0 ≤ rngl_sin θ2)%L.
Proof.
destruct_ac.
intros * H21 Hzs1.
apply Bool.not_false_iff_true in H21.
apply (rngl_nlt_ge_iff Hor).
intros Hs2z.
apply H21; clear H21.
apply angle_leb_gt.
progress unfold angle_ltb.
apply rngl_leb_le in Hzs1.
rewrite Hzs1.
apply (rngl_leb_gt Hor) in Hs2z.
now rewrite Hs2z.
Qed.

Theorem rngl_sin_nonneg_sin_nonneg_sin_neg :
  ∀ θ1 θ2,
  (θ1 ≤ θ1 + θ2)%A
  → (0 ≤ rngl_sin θ1)%L
  → (0 ≤ rngl_sin θ2)%L
  → (rngl_sin (θ1 + θ2) < 0)%L
  → √((1 + rngl_cos (θ1 + θ2)) / 2)%L =
       (√((1 - rngl_cos θ1) / 2) * √((1 - rngl_cos θ2) / 2) -
        √((1 + rngl_cos θ1) / 2) * √((1 + rngl_cos θ2) / 2))%L.
Proof.
destruct_ac.
intros * Haov Hzs1 Hzs2 Hzs3.
specialize (rngl_has_inv_and_1_has_inv_and_1_or_pdiv Hon Hiv) as Hi1.
specialize (rngl_int_dom_or_inv_1_quo_and_eq_dec Hi1 Hed) as Hid.
specialize (rngl_int_dom_or_inv_1_quo Hiv Hon) as Hii.
destruct (Nat.eq_dec (rngl_characteristic T) 1) as [Hc1| Hc1]. {
  specialize (rngl_characteristic_1 Hon Hos Hc1) as H1.
  rewrite H1; apply H1.
}
specialize (rngl_0_lt_2 Hon Hos Hiq Hc1 Hor) as Hz2.
specialize (rngl_2_neq_0 Hon Hos Hiq Hc1 Hor) as H20.
assert (Hze2 : (0 ≤ 2)%L) by now apply (rngl_lt_le_incl Hor).
assert (Hz1ac :  ∀ θ, (0 ≤ 1 + rngl_cos θ)%L). {
  intros.
  apply (rngl_le_sub_le_add_l Hop Hor).
  progress unfold rngl_sub.
  rewrite Hop, rngl_add_0_l.
  apply rngl_cos_bound.
}
assert (Hz1sc : ∀ θ, (0 ≤ 1 - rngl_cos θ)%L). {
  intros.
  apply (rngl_le_add_le_sub_r Hop Hor).
  rewrite rngl_add_0_l.
  apply rngl_cos_bound.
}
assert (Hs2z : (√2 ≠ 0)%L). {
  intros H.
  apply (f_equal rngl_squ) in H.
  rewrite (rngl_squ_sqrt Hon) in H; [ | now apply (rngl_lt_le_incl Hor) ].
  now rewrite (rngl_squ_0 Hos) in H.
}
remember (θ1 + θ2)%A as θ3 eqn:Hθ3.
rewrite (rl_sqrt_div Hon Hop Hiv Hor); [ | easy | easy ].
rewrite (rl_sqrt_div Hon Hop Hiv Hor); [ | easy | easy ].
rewrite (rl_sqrt_div Hon Hop Hiv Hor); [ | easy | easy ].
rewrite (rl_sqrt_div Hon Hop Hiv Hor); [ | easy | easy ].
rewrite (rl_sqrt_div Hon Hop Hiv Hor); [ | easy | easy ].
do 2 rewrite (rngl_div_mul_mul_div Hic Hiv).
do 2 rewrite (rngl_mul_div_assoc Hiv).
rewrite <- rl_sqrt_mul; [ | easy | easy ].
rewrite <- rl_sqrt_mul; [ | easy | easy ].
rewrite (rngl_div_div Hon Hos Hiv); [ | easy | easy ].
rewrite (rngl_div_div Hon Hos Hiv); [ | easy | easy ].
rewrite <- rl_sqrt_mul; [ | easy | easy ].
rewrite fold_rngl_squ.
rewrite (rl_sqrt_squ Hon Hop Hor).
rewrite (rngl_abs_nonneg_eq Hop Hor); [ | easy ].
rewrite <- (rngl_div_sub_distr_r Hop Hiv).
apply (rngl_mul_cancel_r Hi1 _ _ 2)%L; [ easy | ].
rewrite (rngl_div_mul Hon Hiv); [ | easy ].
rewrite <- (rngl_abs_nonneg_eq Hop Hor (√_ / _ * _))%L. 2: {
  apply (rngl_mul_nonneg_nonneg Hon Hos Hiq Hor); [ | easy ].
  apply (rngl_div_nonneg Hon Hop Hiv Hor). 2: {
    apply (rngl_le_neq Hor).
    split; [ now apply rl_sqrt_nonneg | ].
    now apply not_eq_sym.
  }
  now apply rl_sqrt_nonneg.
}
remember (√(_ * _))%L as x eqn:Hx.
remember (√(_ * _))%L as y eqn:Hy in |-*.
destruct (rngl_lt_dec Hor x y) as [Hxy| Hxy]. {
  exfalso.
  apply rngl_nle_gt in Hxy.
  apply Hxy; clear Hxy.
  subst x y.
  progress unfold rngl_sub.
  rewrite Hop.
  do 2 rewrite <- (rngl_sub_opp_r Hop).
  do 2 rewrite <- rngl_cos_add_straight_r.
  apply rngl_add_cos_nonneg_sqrt_mul_le. {
    destruct (rngl_le_dec Hor 0 (rngl_cos θ1)) as [Hzc1| Hzc1]. {
      do 2 rewrite rngl_cos_add_straight_r.
      rewrite (rngl_add_opp_r Hop).
      rewrite <- (rngl_opp_add_distr Hop).
      apply (rngl_opp_nonneg_nonpos Hop Hor).
      rewrite Hθ3 in Hzs3.
      apply (rngl_lt_le_incl Hor).
      now apply rngl_add_cos_neg_when_sin_nonneg_neg.
    }
    apply (rngl_nle_gt_iff Hor) in Hzc1.
    (* case rngl_cos θ1 ≤ 0 *)
    apply rngl_add_cos_nonneg_when_sin_nonpos; try easy. {
      rewrite rngl_sin_add_straight_r.
      now apply (rngl_opp_nonpos_nonneg Hop Hor).
    } {
      rewrite rngl_sin_add_straight_r.
      now apply (rngl_opp_nonpos_nonneg Hop Hor).
    } {
      rewrite angle_add_assoc.
      rewrite (angle_add_comm θ1).
      rewrite angle_add_comm.
      do 2 rewrite angle_add_assoc.
      rewrite angle_straight_add_straight.
      rewrite angle_add_0_l.
      rewrite Hθ3 in Hzs3.
      now apply (rngl_lt_le_incl Hor).
    }
    rewrite rngl_cos_add_straight_r.
    apply (rngl_opp_nonneg_nonpos Hop Hor).
    now apply (rngl_lt_le_incl Hor).
  }
}
apply (rngl_nlt_ge_iff Hor) in Hxy.
rewrite <- (rngl_abs_nonneg_eq Hop Hor). 2: {
  now apply (rngl_le_0_sub Hop Hor).
}
apply (eq_rngl_squ_rngl_abs Hop Hor). {
  rewrite Bool.orb_true_iff; right.
  apply (rngl_has_inv_and_1_has_inv_and_1_or_pdiv Hon Hiv).
} {
  apply (rngl_mul_comm Hic).
}
rewrite (rngl_squ_mul Hic).
rewrite (rngl_squ_div Hic Hon Hos Hiv); [ | easy ].
rewrite (rngl_squ_sqrt Hon); [ | easy ].
rewrite (rngl_squ_sqrt Hon); [ | easy ].
progress unfold rngl_squ at 1.
rewrite rngl_mul_assoc.
rewrite (rngl_div_mul Hon Hiv); [ | easy ].
subst x y.
subst θ3.
rewrite <- (rngl_squ_opp Hop).
rewrite (rngl_opp_sub_distr Hop).
apply rngl_sin_nonneg_sin_nonneg_add_1_cos_add_sub.
apply rngl_leb_le in Hzs1, Hzs2.
congruence.
Qed.

Theorem rngl_sin_nonneg_angle_le_straight :
  ∀ θ, (0 ≤ rngl_sin θ)%L ↔ (θ ≤ angle_straight)%A.
Proof.
destruct_ac.
intros.
progress unfold angle_leb.
cbn.
rewrite (rngl_leb_refl Hor).
remember (0 ≤? rngl_sin θ)%L as zs eqn:Hzs.
symmetry in Hzs.
destruct zs. {
  apply rngl_leb_le in Hzs.
  split; [ | easy ].
  intros _; cbn.
  apply rngl_leb_le.
  apply rngl_cos_bound.
}
apply (rngl_leb_gt Hor) in Hzs.
now apply rngl_nle_gt in Hzs.
Qed.

Theorem rngl_sin_neg_angle_gt_straight :
  ∀ θ, (rngl_sin θ < 0)%L ↔ (angle_straight < θ)%A.
Proof.
destruct_ac.
intros.
split; intros H. {
  apply rngl_nle_gt in H.
  apply angle_nle_gt.
  intros H1; apply H; clear H.
  now apply rngl_sin_nonneg_angle_le_straight.
} {
  apply angle_nle_gt in H.
  apply (rngl_nle_gt_iff Hor).
  intros H1; apply H; clear H.
  now apply rngl_sin_nonneg_angle_le_straight.
}
Qed.

End a.
