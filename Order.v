Set Nested Proofs Allowed.
Require Import Stdlib.Arith.Arith.
Require Import RingLike.Utf8.

Require Import RingLike.Core.
Require Import RingLike.RealLike.
Require Import AngleDef Angle.

Section a.

Context {T : Type}.
Context {ro : ring_like_op T}.
Context {rp : ring_like_prop T}.
Context {rl : real_like_prop T}.
Context {ac : angle_ctx T}.

Definition angle_leb α1 α2 :=
  if (0 ≤? rngl_sin α1)%L then
    if (0 ≤? rngl_sin α2)%L then (rngl_cos α2 ≤? rngl_cos α1)%L
    else true
  else
    if (0 ≤? rngl_sin α2)%L then false
    else (rngl_cos α1 ≤? rngl_cos α2)%L.

Definition angle_ltb α1 α2 :=
  if (0 ≤? rngl_sin α1)%L then
    if (0 ≤? rngl_sin α2)%L then (rngl_cos α2 <? rngl_cos α1)%L
    else true
  else
    if (0 ≤? rngl_sin α2)%L then false
    else (rngl_cos α1 <? rngl_cos α2)%L.

End a.

Notation "α1 ≤? α2" := (angle_leb α1 α2) : angle_scope.
Notation "α1 <? α2" := (angle_ltb α1 α2) : angle_scope.
Notation "α1 ≤ α2" := (angle_leb α1 α2 = true) : angle_scope.
Notation "α1 < α2" := (angle_ltb α1 α2 = true) : angle_scope.
Notation "α1 ≤ α2 < α3" :=
  (angle_leb α1 α2 = true ∧ angle_ltb α2 α3 = true) : angle_scope.
Notation "α1 ≤ α2 ≤ α3" :=
  (angle_leb α1 α2 = true ∧ angle_leb α2 α3 = true) : angle_scope.
Notation "α1 < α2 < α3" :=
  (angle_ltb α1 α2 = true ∧ angle_ltb α2 α3 = true) : angle_scope.
Notation "α1 < α2 ≤ α3" :=
  (angle_ltb α1 α2 = true ∧ angle_leb α2 α3 = true) : angle_scope.

Section a.

Context {T : Type}.
Context {ro : ring_like_op T}.
Context {rp : ring_like_prop T}.
Context {rl : real_like_prop T}.
Context {ac : angle_ctx T}.

Definition angle_add_overflow α1 α2 := ((α1 ≠? 0)%A && (- α1 ≤? α2)%A)%bool.

Theorem angle_lt_le_incl :
  ∀ α1 α2, (α1 < α2 → α1 ≤ α2)%A.
Proof.
destruct_ac.
intros * H12.
progress unfold angle_ltb in H12.
progress unfold angle_leb.
remember (0 ≤? rngl_sin α1)%L as z1 eqn:Hz1.
remember (0 ≤? rngl_sin α2)%L as z2 eqn:Hz2.
symmetry in Hz1, Hz2.
destruct z1. {
  destruct z2; [ | easy ].
  apply (rngl_ltb_lt Heo) in H12.
  apply rngl_leb_le.
  now apply rngl_lt_le_incl.
} {
  destruct z2; [ easy | ].
  apply (rngl_ltb_lt Heo) in H12.
  apply rngl_leb_le.
  now apply rngl_lt_le_incl.
}
Qed.

Theorem angle_le_refl : ∀ α, (α ≤? α)%A = true.
Proof.
intros.
destruct_ac.
progress unfold angle_leb.
remember (0 ≤? rngl_sin α)%L as zs eqn:Hzs.
symmetry in Hzs.
destruct zs; apply (rngl_leb_refl Hor).
Qed.

Theorem angle_lt_iff : ∀ α1 α2, (α1 < α2 ↔ α1 ≤ α2 ∧ α1 ≠ α2)%A.
Proof.
destruct_ac; intros.
progress unfold angle_ltb.
progress unfold angle_leb.
remember (0 ≤? rngl_sin α1)%L as zs1 eqn:Hzs1.
remember (0 ≤? rngl_sin α2)%L as zs2 eqn:Hzs2.
symmetry in Hzs1, Hzs2.
destruct zs1. {
  apply rngl_leb_le in Hzs1.
  destruct zs2. {
    apply rngl_leb_le in Hzs2.
    split; intros H12. {
      apply (rngl_ltb_lt Heo) in H12.
      split. {
        apply rngl_leb_le.
        now apply rngl_lt_le_incl.
      }
      intros H; subst α2.
      now apply rngl_lt_irrefl in H12.
    } {
      destruct H12 as (Hc12, H12).
      apply rngl_leb_le in Hc12.
      apply (rngl_ltb_lt Heo).
      apply rngl_le_neq.
      split; [ easy | ].
      intros H; symmetry in H.
      apply rngl_cos_eq in H.
      destruct H as [H| H]; [ easy | ].
      subst α1.
      apply (rngl_opp_nonneg_nonpos Hop Hor) in Hzs1.
      apply (rngl_le_antisymm Hor) in Hzs2; [ | easy ].
      apply eq_rngl_sin_0 in Hzs2.
      destruct Hzs2; subst α2. {
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
  apply (rngl_leb_gt_iff Hto) in Hzs2.
  apply (rngl_nle_gt Hor) in Hzs2.
  now intros H; subst α2.
} {
  apply (rngl_leb_gt_iff Hto) in Hzs1.
  destruct zs2; [ easy | ].
  apply (rngl_leb_gt_iff Hto) in Hzs2.
  split; intros H12. {
    apply (rngl_ltb_lt Heo) in H12.
    split. {
      apply rngl_leb_le.
      now apply rngl_lt_le_incl.
    }
    intros H; subst α2.
    now apply rngl_lt_irrefl in H12.
  }
  destruct H12 as (Hc12, H12).
  apply rngl_leb_le in Hc12.
  apply (rngl_ltb_lt Heo).
  apply rngl_le_neq.
  split; [ easy | ].
  intros H; apply H12; clear H12.
  apply rngl_cos_eq in H.
  destruct H; subst α1; [ easy | ].
  cbn in Hzs1.
  apply (rngl_opp_neg_pos Hop Hor) in Hzs1.
  now apply rngl_lt_le_incl, (rngl_nlt_ge Hor) in Hzs1.
}
Qed.

Theorem angle_le_iff : ∀ α1 α2, (α1 ≤ α2)%A ↔ (α1 < α2)%A ∨ α1 = α2.
Proof.
intros.
split; intros H. {
  destruct (angle_eq_dec α1 α2) as [H12| H12]; [ now right | left ].
  now apply angle_lt_iff.
} {
  destruct H as [H| H]; [ now apply angle_lt_le_incl | subst ].
  apply angle_le_refl.
}
Qed.

Theorem angle_nlt_ge : ∀ α1 α2, ¬ (α1 < α2)%A ↔ (α2 ≤ α1)%A.
Proof.
destruct_ac.
intros.
progress unfold angle_ltb.
progress unfold angle_leb.
destruct (0 ≤? rngl_sin α1)%L. {
  destruct (0 ≤? rngl_sin α2)%L; [ | easy ].
  split; intros H. {
    apply Bool.not_true_iff_false in H.
    apply (rngl_ltb_ge_iff Hto) in H.
    now apply rngl_leb_le.
  }
  apply Bool.not_true_iff_false.
  apply (rngl_ltb_ge Hor).
  now apply rngl_leb_le.
}
destruct (0 ≤? rngl_sin α2)%L; [ easy | ].
split; intros H. {
  apply Bool.not_true_iff_false in H.
  apply (rngl_ltb_ge_iff Hto) in H.
  now apply rngl_leb_le.
}
apply Bool.not_true_iff_false.
apply (rngl_ltb_ge Hor).
now apply rngl_leb_le.
Qed.

Theorem angle_nle_gt : ∀ α1 α2, (α1 ≤? α2)%A ≠ true ↔ (α2 < α1)%A.
Proof.
destruct_ac.
intros.
progress unfold angle_ltb.
progress unfold angle_leb.
destruct (0 ≤? rngl_sin α1)%L. {
  destruct (0 ≤? rngl_sin α2)%L; [ | easy ].
  split; intros H. {
    apply Bool.not_true_iff_false in H.
    apply (rngl_leb_gt_iff Hto) in H.
    now apply (rngl_ltb_lt Heo).
  }
  apply Bool.not_true_iff_false.
  apply (rngl_leb_gt_iff Hto).
  now apply (rngl_ltb_lt Heo).
}
destruct (0 ≤? rngl_sin α2)%L; [ easy | ].
split; intros H. {
  apply Bool.not_true_iff_false in H.
  apply (rngl_leb_gt_iff Hto) in H.
  now apply (rngl_ltb_lt Heo).
}
apply Bool.not_true_iff_false.
apply (rngl_leb_gt_iff Hto).
now apply (rngl_ltb_lt Heo).
Qed.

Theorem angle_nonpos : ∀ α, (α ≤ 0)%A → α = 0%A.
Proof.
destruct_ac.
intros * Hz.
progress unfold angle_leb in Hz.
cbn in Hz.
rewrite (rngl_leb_refl Hor) in Hz.
remember (0 ≤? rngl_sin α)%L as zs eqn:Hzs.
symmetry in Hzs.
destruct zs; [ | easy ].
apply rngl_leb_le in Hz.
specialize (rngl_cos_bound α) as H1.
destruct H1 as (_, H1).
apply (rngl_le_antisymm Hor) in Hz; [ | easy ].
now apply eq_rngl_cos_1 in Hz.
Qed.

Theorem angle_straight_pos :
  rngl_characteristic T ≠ 1 → (0 < π)%A.
Proof.
destruct_ac.
intros Hc1.
progress unfold angle_ltb.
cbn.
rewrite (rngl_leb_refl Hor).
apply (rngl_ltb_lt Heo).
apply (rngl_opp_1_lt_1 Hop Hc1 Hto).
Qed.

Theorem angle_straight_nonneg : (0 ≤ π)%A.
Proof.
destruct_ac.
progress unfold angle_leb.
cbn.
rewrite (rngl_leb_refl Hor).
apply rngl_leb_le.
apply (rngl_opp_1_le_1 Hop Hto).
Qed.

Theorem angle_leb_gt : ∀ α1 α2, (α1 ≤? α2)%A = false ↔ (α2 < α1)%A.
Proof.
destruct_ac.
intros.
progress unfold angle_leb.
progress unfold angle_ltb.
remember (0 ≤? rngl_sin α1)%L as zs1 eqn:Hzs1.
remember (0 ≤? rngl_sin α2)%L as zs2 eqn:Hzs2.
symmetry in Hzs1, Hzs2.
destruct zs1. {
  apply rngl_leb_le in Hzs1.
  destruct zs2; [ | easy ].
  apply rngl_leb_le in Hzs2.
  split; intros H12. {
    apply (rngl_leb_gt_iff Hto) in H12.
    now apply (rngl_ltb_lt Heo).
  } {
    apply (rngl_leb_gt_iff Hto).
    now apply (rngl_ltb_lt Heo) in H12.
  }
} {
  apply (rngl_leb_gt_iff Hto) in Hzs1.
  destruct zs2; [ easy | ].
  split; intros H12. {
    apply (rngl_leb_gt_iff Hto) in H12.
    now apply (rngl_ltb_lt Heo).
  } {
    apply (rngl_leb_gt_iff Hto).
    now apply (rngl_ltb_lt Heo) in H12.
  }
}
Qed.

Theorem angle_lt_irrefl : ∀ α, ¬ (α < α)%A.
Proof.
destruct_ac.
intros * H.
progress unfold angle_ltb in H.
remember (0 ≤? rngl_sin α)%L as zs eqn:Hzs.
symmetry in Hzs.
destruct zs. {
  apply (rngl_ltb_lt Heo) in H.
  now apply rngl_lt_irrefl in H.
} {
  apply (rngl_ltb_lt Heo) in H.
  now apply rngl_lt_irrefl in H.
}
Qed.

Theorem angle_nonneg : ∀ α, (0 ≤ α)%A.
Proof.
destruct_ac; intros.
progress unfold angle_leb.
cbn.
rewrite (rngl_leb_refl Hor).
destruct (0 ≤? rngl_sin α)%L; [ | easy ].
apply rngl_leb_le.
apply rngl_cos_bound.
Qed.

Theorem angle_add_overflow_0_l : ∀ α, angle_add_overflow 0 α = false.
Proof.
intros.
progress unfold angle_add_overflow.
apply Bool.andb_false_iff; left.
apply Bool.negb_false_iff.
now apply angle_eqb_eq.
Qed.

Theorem angle_add_overflow_0_r : ∀ α, angle_add_overflow α 0 = false.
Proof.
intros.
progress unfold angle_add_overflow.
apply Bool.andb_false_iff.
destruct (angle_eq_dec α 0) as [Htz| Htz]. {
  subst α; left.
  apply Bool.negb_false_iff.
  now apply angle_eqb_eq.
}
right.
apply angle_leb_gt.
apply angle_lt_iff.
split; [ apply angle_nonneg | ].
intros H; apply Htz; clear Htz.
apply (f_equal angle_opp) in H.
now rewrite angle_opp_0, angle_opp_involutive in H.
Qed.

Theorem angle_add_overflow_comm :
  ∀ α1 α2,
  angle_add_overflow α1 α2 = angle_add_overflow α2 α1.
Proof.
destruct_ac.
intros.
progress unfold angle_add_overflow.
remember (α1 ≠? 0)%A as z1 eqn:Hz1.
remember (α2 ≠? 0)%A as z2 eqn:Hz2.
symmetry in Hz1, Hz2.
destruct z1. 2: {
  destruct z2; [ | easy ].
  cbn; symmetry.
  apply angle_neqb_neq in Hz2.
  apply Bool.not_true_iff_false in Hz1.
  apply Bool.not_true_iff_false.
  intros H1; apply Hz1; clear Hz1.
  apply angle_neqb_neq.
  intros Hz1; apply Hz2; clear Hz2.
  subst α1.
  apply angle_nonpos in H1.
  apply (f_equal angle_opp) in H1.
  now rewrite angle_opp_involutive, angle_opp_0 in H1.
}
cbn.
destruct z2. {
  cbn.
  apply angle_neqb_neq in Hz1, Hz2.
  progress unfold angle_leb.
  cbn.
  do 2 rewrite (rngl_leb_0_opp Hop Hto).
  remember (rngl_sin α1 ≤? 0)%L as s1z eqn:Hs1z.
  remember (rngl_sin α2 ≤? 0)%L as s2z eqn:Hs2z.
  remember (0 ≤? rngl_sin α1)%L as zs1 eqn:Hzs1.
  remember (0 ≤? rngl_sin α2)%L as zs2 eqn:Hzs2.
  symmetry in Hs1z, Hs2z, Hzs1, Hzs2.
  destruct s1z. {
    destruct zs1. {
      apply rngl_leb_le in Hs1z, Hzs1.
      apply (rngl_le_antisymm Hor) in Hzs1; [ clear Hs1z | easy ].
      apply eq_rngl_sin_0 in Hzs1.
      destruct Hzs1; subst α1; [ easy | ].
      cbn.
      destruct zs2. {
        destruct s2z. {
          apply rngl_leb_le in Hs2z, Hzs2.
          apply (rngl_le_antisymm Hor) in Hzs2; [ clear Hs2z | easy ].
          apply eq_rngl_sin_0 in Hzs2.
          now destruct Hzs2; subst α2.
        }
        apply (rngl_leb_gt_iff Hto).
        apply rngl_le_neq.
        split; [ apply rngl_cos_bound | ].
        intros H; symmetry in H.
        apply eq_rngl_cos_opp_1 in H.
        subst α2.
        cbn in Hs2z.
        now rewrite (rngl_leb_refl Hor) in Hs2z.
      }
      symmetry.
      destruct s2z. {
        apply rngl_leb_le.
        apply rngl_cos_bound.
      }
      exfalso.
      apply (rngl_leb_gt_iff Hto) in Hs2z, Hzs2.
      now apply (rngl_lt_asymm Hor) in Hs2z.
    }
    destruct zs2. {
      destruct s2z; [ | easy ].
      apply rngl_leb_le in Hs2z, Hzs2.
      apply (rngl_le_antisymm Hor) in Hzs2; [ clear Hs2z | easy ].
      apply eq_rngl_sin_0 in Hzs2.
      destruct Hzs2; subst α2; [ easy | cbn ].
      apply rngl_leb_le.
      apply rngl_cos_bound.
    }
    symmetry.
    destruct s2z; [ easy | ].
    apply (rngl_leb_gt_iff Hto) in Hs2z, Hzs2.
    now apply (rngl_lt_asymm Hor) in Hs2z.
  }
  destruct zs1. {
    destruct zs2. {
      symmetry.
      destruct s2z; [ | easy ].
      apply rngl_leb_le in Hs2z, Hzs2.
      apply (rngl_le_antisymm Hor) in Hzs2; [ clear Hs2z | easy ].
      apply eq_rngl_sin_0 in Hzs2.
      destruct Hzs2; subst α2; [ easy | cbn ].
      apply (rngl_leb_gt_iff Hto).
      apply rngl_le_neq.
      split; [ apply rngl_cos_bound | ].
      intros H; symmetry in H.
      apply eq_rngl_cos_opp_1 in H; subst α1.
      cbn in Hs1z.
      now rewrite rngl_leb_refl in Hs1z.
    }
    destruct s2z; [ easy | ].
    apply (rngl_leb_gt_iff Hto) in Hs2z, Hzs2.
    now apply (rngl_lt_asymm Hor) in Hs2z.
  }
  apply (rngl_leb_gt_iff Hto) in Hs1z, Hzs1.
  now apply (rngl_lt_asymm Hor) in Hs1z.
}
apply Bool.negb_false_iff in Hz2.
apply angle_eqb_eq in Hz2.
subst α2; cbn.
(* lemma *)
progress unfold angle_leb.
cbn.
rewrite (rngl_leb_refl Hor).
rewrite (rngl_leb_0_opp Hop Hto).
destruct (rngl_sin α1 ≤? 0)%L; [ | easy ].
apply (rngl_leb_gt_iff Hto).
apply rngl_le_neq.
split; [ apply rngl_cos_bound | ].
intros H.
apply eq_rngl_cos_1 in H.
now apply angle_neqb_neq in Hz1.
Qed.

(* *)

Theorem angle_le_rngl_sin_nonneg_sin_nonneg :
  ∀ α1 α2,
  (α2 ≤ α1)%A
  → (0 ≤ rngl_sin α1)%L
  → (0 ≤ rngl_sin α2)%L.
Proof.
destruct_ac.
intros * H21 Hzs1.
apply Bool.not_false_iff_true in H21.
apply (rngl_nlt_ge_iff Hto).
intros Hs2z.
apply H21; clear H21.
apply angle_leb_gt.
progress unfold angle_ltb.
apply rngl_leb_le in Hzs1.
rewrite Hzs1.
apply (rngl_leb_gt_iff Hto) in Hs2z.
now rewrite Hs2z.
Qed.

Theorem rngl_sin_nonneg_sin_nonneg_sin_neg :
  ∀ α1 α2,
  (α1 ≤ α1 + α2)%A
  → (0 ≤ rngl_sin α1)%L
  → (0 ≤ rngl_sin α2)%L
  → (rngl_sin (α1 + α2) < 0)%L
  → √((1 + rngl_cos (α1 + α2)) / 2)%L =
       (√((1 - rngl_cos α1) / 2) * √((1 - rngl_cos α2) / 2) -
        √((1 + rngl_cos α1) / 2) * √((1 + rngl_cos α2) / 2))%L.
Proof.
destruct_ac.
intros * Haov Hzs1 Hzs2 Hzs3.
destruct (Nat.eq_dec (rngl_characteristic T) 1) as [Hc1| Hc1]. {
  specialize (rngl_characteristic_1 Hos Hc1) as H1.
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
remember (α1 + α2)%A as α3 eqn:Hα3.
rewrite (rl_sqrt_div Hop Hiv Hto); [ | easy | easy ].
rewrite (rl_sqrt_div Hop Hiv Hto); [ | easy | easy ].
rewrite (rl_sqrt_div Hop Hiv Hto); [ | easy | easy ].
rewrite (rl_sqrt_div Hop Hiv Hto); [ | easy | easy ].
rewrite (rl_sqrt_div Hop Hiv Hto); [ | easy | easy ].
do 2 rewrite (rngl_div_mul_mul_div Hic Hiv).
do 2 rewrite (rngl_mul_div_assoc Hiv).
rewrite <- rl_sqrt_mul; [ | easy | easy ].
rewrite <- rl_sqrt_mul; [ | easy | easy ].
rewrite (rngl_div_div Hos Hiv); [ | easy | easy ].
rewrite (rngl_div_div Hos Hiv); [ | easy | easy ].
rewrite <- rl_sqrt_mul; [ | easy | easy ].
rewrite fold_rngl_squ.
rewrite (rl_sqrt_squ Hop Hto).
rewrite (rngl_abs_nonneg_eq Hop Hor); [ | easy ].
rewrite <- (rngl_div_sub_distr_r Hop Hiv).
apply (rngl_mul_cancel_r Hi1 _ _ 2)%L; [ easy | ].
rewrite (rngl_div_mul Hiv); [ | easy ].
rewrite <- (rngl_abs_nonneg_eq Hop Hor (√_ / _ * _))%L. 2: {
  apply (rngl_mul_nonneg_nonneg Hos Hor); [ | easy ].
  apply (rngl_div_nonneg Hop Hiv Hto). 2: {
    apply rngl_le_neq.
    split; [ now apply rl_sqrt_nonneg | ].
    now apply not_eq_sym.
  }
  now apply rl_sqrt_nonneg.
}
remember (√(_ * _))%L as x eqn:Hx.
remember (√(_ * _))%L as y eqn:Hy in |-*.
destruct (rngl_ltb_dec x y) as [Hxy| Hxy]. {
  exfalso.
  apply (rngl_ltb_lt Heo), (rngl_nle_gt Hor) in Hxy.
  apply Hxy; clear Hxy.
  subst x y.
  progress unfold rngl_sub.
  rewrite Hop.
  do 2 rewrite <- (rngl_sub_opp_r Hop).
  do 2 rewrite <- rngl_cos_add_straight_r.
  apply rngl_add_cos_nonneg_sqrt_mul_le. {
    destruct (rngl_leb_dec 0 (rngl_cos α1)) as [Hzc1| Hzc1]. {
      apply rngl_leb_le in Hzc1.
      do 2 rewrite rngl_cos_add_straight_r.
      rewrite (rngl_add_opp_r Hop).
      rewrite <- (rngl_opp_add_distr Hop).
      apply (rngl_opp_nonneg_nonpos Hop Hor).
      rewrite Hα3 in Hzs3.
      apply rngl_lt_le_incl.
      now apply rngl_add_cos_neg_when_sin_nonneg_neg.
    }
    apply (rngl_leb_gt_iff Hto) in Hzc1.
    (* case rngl_cos α1 ≤ 0 *)
    apply rngl_add_cos_nonneg_when_sin_nonpos; try easy. {
      rewrite rngl_sin_add_straight_r.
      now apply (rngl_opp_nonpos_nonneg Hop Hor).
    } {
      rewrite rngl_sin_add_straight_r.
      now apply (rngl_opp_nonpos_nonneg Hop Hor).
    } {
      rewrite angle_add_assoc.
      rewrite (angle_add_comm α1).
      rewrite angle_add_comm.
      do 2 rewrite angle_add_assoc.
      rewrite angle_straight_add_straight.
      rewrite angle_add_0_l.
      rewrite Hα3 in Hzs3.
      now apply rngl_lt_le_incl.
    }
    rewrite rngl_cos_add_straight_r.
    apply (rngl_opp_nonneg_nonpos Hop Hor).
    now apply rngl_lt_le_incl.
  }
}
apply (rngl_ltb_ge_iff Hto) in Hxy.
rewrite <- (rngl_abs_nonneg_eq Hop Hor). 2: {
  now apply (rngl_le_0_sub Hop Hor).
}
apply (eq_rngl_squ_rngl_abs Hop Hto). {
  rewrite Bool.orb_true_iff; right.
  apply (rngl_has_inv_has_inv_or_pdiv Hiv).
} {
  apply (rngl_mul_comm Hic).
}
rewrite (rngl_squ_mul Hic).
rewrite (rngl_squ_div Hic Hos Hiv); [ | easy ].
rewrite rngl_squ_sqrt; [ | easy ].
rewrite rngl_squ_sqrt; [ | easy ].
progress unfold rngl_squ at 1.
rewrite rngl_mul_assoc.
rewrite (rngl_div_mul Hiv); [ | easy ].
subst x y.
subst α3.
rewrite <- (rngl_squ_opp Hop).
rewrite (rngl_opp_sub_distr Hop).
apply rngl_sin_nonneg_sin_nonneg_add_1_cos_add_sub.
apply rngl_leb_le in Hzs1, Hzs2.
congruence.
Qed.

Theorem rngl_sin_nonneg_angle_le_straight :
  ∀ α, (0 ≤ rngl_sin α)%L ↔ (α ≤ π)%A.
Proof.
destruct_ac.
intros.
progress unfold angle_leb.
cbn.
rewrite (rngl_leb_refl Hor).
remember (0 ≤? rngl_sin α)%L as zs eqn:Hzs.
symmetry in Hzs.
destruct zs. {
  apply rngl_leb_le in Hzs.
  split; [ | easy ].
  intros _; cbn.
  apply rngl_leb_le.
  apply rngl_cos_bound.
}
apply (rngl_leb_gt_iff Hto) in Hzs.
now apply (rngl_nle_gt Hor) in Hzs.
Qed.

Theorem rngl_sin_neg_angle_gt_straight :
  ∀ α, (rngl_sin α < 0)%L ↔ (π < α)%A.
Proof.
destruct_ac.
intros.
split; intros H. {
  apply (rngl_nle_gt Hor) in H.
  apply angle_nle_gt.
  intros H1; apply H; clear H.
  now apply rngl_sin_nonneg_angle_le_straight.
} {
  apply angle_nle_gt in H.
  apply (rngl_nle_gt_iff Hto).
  intros H1; apply H; clear H.
  now apply rngl_sin_nonneg_angle_le_straight.
}
Qed.

Theorem angle_le_opp_r : ∀ α1 α2, α1 ≠ 0%A → (α1 ≤ - α2)%A → (α2 ≤ - α1)%A.
Proof.
destruct_ac.
intros * H2z H2.
progress unfold angle_leb in H2.
progress unfold angle_leb.
cbn in H2 |-*.
rewrite (rngl_leb_0_opp Hop Hto) in H2.
rewrite (rngl_leb_opp_r Hop Hto).
rewrite (rngl_opp_0 Hop).
remember (0 ≤? rngl_sin α1)%L as zs2 eqn:Hzs2.
remember (0 ≤? rngl_sin α2)%L as zs eqn:Hzs.
remember (rngl_sin α1 ≤? 0)%L as sz2 eqn:Hsz2.
remember (rngl_sin α2 ≤? 0)%L as sz eqn:Hsz.
symmetry in Hzs2, Hzs, Hsz2, Hsz.
destruct zs. {
  destruct sz2; [ | easy ].
  destruct zs2; [ | now destruct sz ].
  apply rngl_leb_le in Hzs2, Hzs, Hsz2.
  apply rngl_leb_le.
  apply (rngl_le_antisymm Hor) in Hzs2; [ | easy ].
  apply eq_rngl_sin_0 in Hzs2.
  destruct Hzs2; [ easy | subst α1 ].
  apply rngl_cos_bound.
}
destruct zs2. 2: {
  destruct sz; [ easy | ].
  apply (rngl_leb_gt_iff Hto) in Hzs2, Hsz, Hzs.
  now apply (rngl_lt_asymm Hor) in Hzs.
}
apply rngl_leb_le in Hzs2.
apply (rngl_leb_gt_iff Hto) in Hzs.
destruct sz. {
  destruct sz2; [ exfalso | easy ].
  apply rngl_leb_le in Hsz, H2, Hsz2.
  apply (rngl_le_antisymm Hor) in Hzs2; [ | easy ].
  apply eq_rngl_sin_0 in Hzs2.
  destruct Hzs2; [ easy | subst α1 ].
  apply (rngl_nlt_ge Hor) in H2.
  apply H2; clear H2.
  apply rngl_le_neq.
  split; [ apply rngl_cos_bound | ].
  cbn; intros Hcc.
  symmetry in Hcc.
  apply eq_rngl_cos_opp_1 in Hcc.
  subst α2.
  now apply rngl_lt_irrefl in Hzs.
}
clear H2.
destruct sz2. {
  exfalso.
  apply rngl_leb_le in Hsz2.
  apply (rngl_le_antisymm Hor) in Hzs2; [ | easy ].
  apply eq_rngl_sin_0 in Hzs2.
  destruct Hzs2; [ easy | subst α1 ].
  apply (rngl_leb_gt_iff Hto) in Hsz.
  now apply (rngl_lt_asymm Hor) in Hzs.
}
apply (rngl_leb_gt_iff Hto) in Hsz.
now apply (rngl_lt_asymm Hor) in Hzs.
Qed.

Theorem angle_lt_opp_r :
  ∀ α1 α2,
  α1 ≠ 0%A
  → (α1 < - α2)%A
  → (α2 < - α1)%A.
Proof.
destruct_ac.
intros * Hz1 H12.
progress unfold angle_ltb in H12.
progress unfold angle_ltb.
cbn in H12 |-*.
rewrite (rngl_leb_0_opp Hop Hto) in H12.
rewrite (rngl_leb_0_opp Hop Hto).
remember (0 ≤? rngl_sin α1)%L as zs1 eqn:Hzs1.
remember (0 ≤? rngl_sin α2)%L as zs2 eqn:Hzs2.
remember (rngl_sin α1 ≤? 0)%L as s1z eqn:Hs1z.
remember (rngl_sin α2 ≤? 0)%L as s2z eqn:Hs2z.
move zs2 before zs1; move s1z before zs2; move s2z before s1z.
symmetry in Hzs1, Hzs2, Hs1z, Hs2z.
destruct zs2. {
  destruct s1z; [ | easy ].
  destruct zs1; [ | now destruct s2z ].
  apply rngl_leb_le in Hzs1, Hs1z.
  apply (rngl_le_antisymm Hor) in Hzs1; [ clear Hs1z | easy ].
  apply eq_rngl_sin_0 in Hzs1.
  destruct Hzs1; [ easy | subst α1 ].
  destruct s2z. {
    cbn in H12 |-*.
    apply rngl_leb_le in Hzs2, Hs2z.
    apply (rngl_le_antisymm Hor) in Hzs2; [ clear Hs2z | easy ].
    apply eq_rngl_sin_0 in Hzs2.
    destruct Hzs2; subst α2. {
      apply (rngl_ltb_lt Heo) in H12.
      apply (rngl_nle_gt Hor) in H12.
      cbn in H12.
      exfalso; apply H12.
      apply (rngl_opp_1_le_1 Hop Hto).
    }
    apply (rngl_ltb_lt Heo) in H12.
    now apply rngl_lt_irrefl in H12.
  }
  cbn.
  apply (rngl_ltb_lt Heo).
  apply rngl_le_neq.
  split; [ apply rngl_cos_bound | ].
  intros H; symmetry in H.
  apply eq_rngl_cos_opp_1 in H.
  subst α2.
  cbn in Hs2z, Hzs2.
  now rewrite Hs2z in Hzs2.
}
destruct s1z. {
  exfalso.
  destruct zs1. {
    apply rngl_leb_le in Hzs1, Hs1z.
    apply (rngl_le_antisymm Hor) in Hzs1; [ clear Hs1z | easy ].
    apply eq_rngl_sin_0 in Hzs1.
    destruct Hzs1; [ easy | subst α1 ].
    destruct s2z. {
      cbn in H12.
      apply Bool.not_false_iff_true in H12.
      apply H12.
      apply (rngl_ltb_ge Hor).
      apply rngl_cos_bound.
    }
    apply (rngl_leb_gt_iff Hto) in Hs2z, Hzs2.
    now apply (rngl_lt_asymm Hor) in Hs2z.
  }
  destruct s2z; [ easy | ].
  apply (rngl_leb_gt_iff Hto) in Hs2z, Hzs2.
  now apply (rngl_lt_asymm Hor) in Hs2z.
}
destruct zs1. {
  destruct s2z; [ easy | ].
  apply (rngl_leb_gt_iff Hto) in Hs2z, Hzs2.
  now apply (rngl_lt_asymm Hor) in Hs2z.
}
destruct s2z; [ easy | ].
apply (rngl_leb_gt_iff Hto) in Hs2z, Hzs2.
now apply (rngl_lt_asymm Hor) in Hs2z.
Qed.

Theorem angle_le_trans :
  ∀ α1 α2 α3,
  (α1 ≤ α2 → α2 ≤ α3 → α1 ≤ α3)%A.
Proof.
destruct_ac.
intros * H12 H23.
progress unfold angle_leb in H12.
progress unfold angle_leb in H23.
progress unfold angle_leb.
remember (0 ≤? rngl_sin α1)%L as z1 eqn:Hz1.
remember (0 ≤? rngl_sin α2)%L as z2 eqn:Hz2.
remember (0 ≤? rngl_sin α3)%L as z3 eqn:Hz3.
symmetry in Hz1, Hz2, Hz3.
destruct z1. {
  apply rngl_leb_le in Hz1.
  (* c'est bizarre, quand même : si j'avais utilisé rngl_eq_dec,
     il m'aurait fallu que "rngl_has_eq_dec T = true" soit en
     hypothèse. Tandis que là, non *)
  destruct z3; [ | easy ].
  apply rngl_leb_le.
  apply rngl_leb_le in Hz3.
  destruct z2; [ | easy ].
  apply rngl_leb_le in Hz2, H12, H23.
  now apply (rngl_le_trans Hor _ (rngl_cos α2)).
} {
  destruct z2; [ easy | ].
  destruct z3; [ easy | ].
  apply rngl_leb_le in H12, H23.
  apply rngl_leb_le.
  now apply (rngl_le_trans Hor _ (rngl_cos α2)).
}
Qed.

Theorem angle_lt_le_trans :
  ∀ α1 α2 α3,
  (α1 < α2 → α2 ≤ α3 → α1 < α3)%A.
Proof.
destruct_ac.
intros * H12 H23.
progress unfold angle_ltb in H12.
progress unfold angle_leb in H23.
progress unfold angle_ltb.
remember (0 ≤? rngl_sin α1)%L as z1 eqn:Hz1.
remember (0 ≤? rngl_sin α2)%L as z2 eqn:Hz2.
remember (0 ≤? rngl_sin α3)%L as z3 eqn:Hz3.
symmetry in Hz1, Hz2, Hz3.
destruct z1. {
  apply rngl_leb_le in Hz1.
  destruct z3; [ | easy ].
  apply (rngl_ltb_lt Heo).
  apply rngl_leb_le in Hz3.
  destruct z2; [ | easy ].
  apply rngl_leb_le in Hz2, H23.
  apply (rngl_ltb_lt Heo) in H12.
  now apply (rngl_le_lt_trans Hor _ (rngl_cos α2)).
} {
  destruct z2; [ easy | ].
  destruct z3; [ easy | ].
  apply (rngl_ltb_lt Heo) in H12.
  apply rngl_leb_le in H23.
  apply (rngl_ltb_lt Heo).
  now apply (rngl_lt_le_trans Hor _ (rngl_cos α2)).
}
Qed.

Theorem angle_le_lt_trans :
  ∀ α1 α2 α3,
  (α1 ≤ α2 → α2 < α3 → α1 < α3)%A.
Proof.
intros * H12 H23.
apply angle_lt_iff.
split. {
  apply (angle_le_trans _ α2); [ easy | ].
  now apply angle_lt_le_incl in H23.
}
intros H; subst α3.
now apply angle_nle_gt in H23.
Qed.

Theorem angle_lt_trans : ∀ α1 α2 α3, (α1 < α2 → α2 < α3 → α1 < α3)%A.
Proof.
intros * H12 H23.
apply (angle_le_lt_trans _ α2); [ | easy ].
now apply angle_lt_le_incl in H12.
Qed.

Theorem angle_add_overflow_lt_straight_ge_straight :
  ∀ α1 α2,
  angle_add_overflow α1 α2 = true
  → (α1 < π)%A
  → (π ≤ α2)%A.
Proof.
intros * H12 H1s.
apply angle_nlt_ge.
intros H2s.
apply Bool.not_false_iff_true in H12.
apply H12; clear H12.
progress unfold angle_add_overflow.
apply Bool.andb_false_iff.
destruct (angle_eq_dec α1 0) as [H1z| H1z]. {
  left.
  apply Bool.not_true_iff_false.
  subst α1.
  now rewrite angle_eqb_refl.
}
right.
apply angle_leb_gt.
apply (angle_lt_trans _ π); [ easy | ].
apply angle_lt_opp_r; [ easy | ].
now rewrite angle_opp_straight.
Qed.

Theorem rngl_le_0_cos :
  ∀ α,
  (α ≤ π/₂ ∨ π + π/₂ ≤ α)%A
  → (0 ≤ rngl_cos α)%L.
Proof.
destruct_ac.
destruct (Nat.eq_dec (rngl_characteristic T) 1) as [Hc1| Hc1]. {
  specialize (rngl_characteristic_1 Hos Hc1) as H1.
  intros.
  rewrite (H1 (rngl_cos α)).
  apply (rngl_le_refl Hor).
}
intros * Htr.
progress unfold angle_leb in Htr.
rewrite rngl_sin_add_right_r in Htr.
rewrite rngl_cos_add_right_r in Htr.
cbn in Htr.
rewrite (rngl_opp_0 Hop) in Htr.
rewrite (rngl_leb_0_opp Hop Hto) in Htr.
specialize (rngl_0_le_1 Hos Hto) as H1.
apply rngl_leb_le in H1.
rewrite H1 in Htr; clear H1.
specialize (rngl_0_lt_1 Hos Hc1 Hto) as H1.
apply (rngl_leb_gt_iff Hto) in H1.
rewrite H1 in Htr; clear H1.
remember (0 ≤? rngl_sin α)%L as zst eqn:Hzst.
symmetry in Hzst.
apply rngl_leb_le.
now destruct zst; destruct Htr.
Qed.

Theorem rngl_le_cos_0 :
  ∀ α,
  (π/₂ ≤ α ≤ π + π/₂)%A
  → (rngl_cos α ≤ 0)%L.
Proof.
destruct_ac.
destruct (Nat.eq_dec (rngl_characteristic T) 1) as [Hc1| Hc1]. {
  specialize (rngl_characteristic_1 Hos Hc1) as H1.
  intros.
  rewrite (H1 (rngl_cos α)).
  apply (rngl_le_refl Hor).
}
intros * Htr.
progress unfold angle_leb in Htr.
cbn in Htr.
do 2 rewrite (rngl_mul_0_l Hos) in Htr.
do 2 rewrite (rngl_mul_opp_l Hop) in Htr.
do 2 rewrite rngl_mul_1_l in Htr.
rewrite rngl_add_0_l in Htr.
rewrite (rngl_sub_0_r Hos) in Htr.
rewrite (rngl_opp_0 Hop) in Htr.
rewrite (rngl_leb_0_opp Hop Hto) in Htr.
specialize (rngl_0_lt_1 Hos Hc1 Hto) as H1.
apply (rngl_leb_gt_iff Hto) in H1.
rewrite H1 in Htr; clear H1.
rewrite (rngl_0_leb_1 Hos Hto) in Htr.
remember (0 ≤? rngl_sin α)%L as zst eqn:Hzst.
symmetry in Hzst.
destruct zst; [ now apply rngl_leb_le | ].
destruct Htr as (_, Htr).
now apply rngl_leb_le.
Qed.

End a.
