Set Nested Proofs Allowed.
From Stdlib Require Import Utf8 Arith.

Require Import RingLike.Core.
Require Import RingLike.RealLike.
Require Import RingLike.Misc.

Require Import Core.
Require Import Angle.
Require Import Angle_order.
Require Import TacChangeAngle.

Section a.

Context {T : Type}.
Context {ro : ring_like_op T}.
Context {rp : ring_like_prop T}.
Context {ac : angle_ctx T}.

(* *)

Definition angle_add_overflow θ1 θ2 := ((θ1 ≠? 0)%A && (- θ1 ≤? θ2)%A)%bool.

(* equivalent definition *)
Definition angle_add_overflow2 θ1 θ2 := (θ1 + θ2 <? θ1)%A.

Theorem angle_add_overflow_0_l : ∀ θ, angle_add_overflow 0 θ = false.
Proof.
intros.
progress unfold angle_add_overflow.
apply Bool.andb_false_iff; left.
apply Bool.negb_false_iff.
now apply angle_eqb_eq.
Qed.

Theorem angle_add_overflow_0_r : ∀ θ, angle_add_overflow θ 0 = false.
Proof.
intros.
progress unfold angle_add_overflow.
apply Bool.andb_false_iff.
destruct (angle_eq_dec θ 0) as [Htz| Htz]. {
  subst θ; left.
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

Theorem rngl_sin_add_nonneg :
  ∀ θ1 θ2,
  (0 ≤ rngl_sin θ1)%L
  → (0 ≤ rngl_sin θ2)%L
  → (0 ≤ rngl_cos θ1)%L
  → (0 ≤ rngl_cos θ2)%L
  → (0 ≤ rngl_sin (θ1 + θ2))%L.
Proof.
destruct_ac.
intros * Hzs1 Hzs2 Hcs1 Hcs2.
cbn.
apply (rngl_le_0_add Hos Hor).
now apply (rngl_mul_nonneg_nonneg Hon Hos Hiq Hor).
now apply (rngl_mul_nonneg_nonneg Hon Hos Hiq Hor).
Qed.

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
change_angle_add_r θ1 angle_right.
progress sin_cos_add_sub_right_hyp T Hs1z.
progress sin_cos_add_sub_right_hyp T Hzc1.
progress sin_cos_add_sub_right_goal T.
apply (rngl_lt_le_incl Hor) in Hs1z.
now apply rngl_sin_add_nonneg.
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
apply (rngl_le_0_add Hos Hor).
now apply (rngl_mul_nonneg_nonneg Hon Hos Hiq Hor).
now apply (rngl_mul_nonneg_nonneg Hon Hos Hiq Hor).
Qed.

Theorem rngl_cos_add_le_cos :
  ∀ θ1 θ2,
  (θ1 ≠ angle_straight ∨ θ2 ≠ angle_straight ∨
   0 ≤ rngl_cos θ1 ∨ 0 ≤ rngl_cos θ2)%L
  → (0 ≤ rngl_sin θ1)%L
  → (0 ≤ rngl_sin θ2)%L
  → (0 ≤ rngl_sin (θ1 + θ2))%L
  → (rngl_cos (θ1 + θ2) ≤ rngl_cos θ1)%L.
Proof.
destruct_ac.
specialize (rngl_has_eq_dec_or_is_ordered_r Hor) as Heo.
specialize (rngl_has_inv_and_1_has_inv_and_1_or_pdiv Hon Hiv) as Hi1.
specialize (rngl_int_dom_or_inv_1_quo_and_eq_dec Hi1 Hed) as Hid.
intros * H12 Hzs1 Hzs2 Hzs12.
rewrite <- or_assoc in H12.
rewrite or_comm in H12.
rewrite or_assoc in H12.
destruct H12 as [H12| H12]. {
  cbn.
  apply (rngl_le_sub_le_add_l Hop Hor).
  apply (rngl_le_0_sub Hop Hor).
  rewrite <- (rngl_add_sub_assoc Hop).
  rewrite (rngl_sub_mul_r_diag_l Hon Hop).
  apply (rngl_le_0_add Hos Hor).
  now apply (rngl_mul_nonneg_nonneg Hon Hos Hiq Hor).
  apply (rngl_mul_nonneg_nonneg Hon Hos Hiq Hor); [ easy | ].
  apply (rngl_le_0_sub Hop Hor).
  apply rngl_cos_bound.
}
destruct (rngl_le_dec Hor 0 (rngl_cos θ1)) as [Hzc1| Hc1z]. {
  cbn.
  apply (rngl_le_sub_le_add_l Hop Hor).
  apply (rngl_le_0_sub Hop Hor).
  rewrite <- (rngl_add_sub_assoc Hop).
  rewrite (rngl_sub_mul_r_diag_l Hon Hop).
  apply (rngl_le_0_add Hos Hor).
  now apply (rngl_mul_nonneg_nonneg Hon Hos Hiq Hor).
  apply (rngl_mul_nonneg_nonneg Hon Hos Hiq Hor); [ easy | ].
  apply (rngl_le_0_sub Hop Hor).
  apply rngl_cos_bound.
}
apply (rngl_nle_gt_iff Hor) in Hc1z.
destruct (rngl_le_dec Hor 0 (rngl_cos θ2)) as [Hzc2| Hc2z]. {
  remember (θ1 - angle_right)%A as θ' eqn:Hθ'.
  apply angle_add_move_r in Hθ'.
  subst θ1; rename θ' into θ1.
  rewrite angle_add_add_swap in Hzs12 |-*.
  rewrite rngl_cos_add_right_r in Hc1z.
  apply (rngl_opp_neg_pos Hop Hor) in Hc1z.
  rewrite rngl_sin_add_right_r in Hzs1, Hzs12.
  do 2 rewrite rngl_cos_add_right_r.
  apply -> (rngl_opp_le_compat Hop Hor).
  apply (rngl_lt_le_incl Hor) in Hc1z.
  apply rngl_cos_cos_sin_sin_nonneg_sin_le_cos_le_iff; try easy.
  now apply rngl_sin_add_nonneg.
  cbn.
  apply (rngl_le_sub_le_add_l Hop Hor).
  apply (rngl_le_0_sub Hop Hor).
  rewrite <- (rngl_add_sub_assoc Hop).
  rewrite (rngl_sub_mul_r_diag_l Hon Hop).
  apply (rngl_le_0_add Hos Hor).
  now apply (rngl_mul_nonneg_nonneg Hon Hos Hiq Hor).
  apply (rngl_mul_nonneg_nonneg Hon Hos Hiq Hor); [ easy | ].
  apply (rngl_le_0_sub Hop Hor).
  apply rngl_cos_bound.
}
destruct H12 as [H12| H12]; [ easy | ].
apply (rngl_nle_gt_iff Hor) in Hc2z.
destruct (rngl_eq_dec Heo (rngl_sin θ1) 0) as [Hs1z| Hs1z]. {
  apply eq_rngl_sin_0 in Hs1z.
  destruct Hs1z; subst θ1. {
    rewrite angle_add_0_l.
    apply rngl_cos_bound.
  }
  destruct H12 as [H12| H12]; [ easy | ].
  rewrite rngl_sin_add_straight_l in Hzs12.
  apply (rngl_opp_nonneg_nonpos Hop Hor) in Hzs12.
  apply (rngl_le_antisymm Hor) in Hzs12; [ | easy ].
  symmetry in Hzs12.
  apply eq_rngl_sin_0 in Hzs12.
  destruct Hzs12; subst θ2; [ | easy ].
  rewrite angle_add_0_r.
  apply (rngl_le_refl Hor).
}
exfalso.
apply rngl_nlt_ge in Hzs12.
apply Hzs12; clear Hzs12.
cbn.
apply (rngl_add_neg_nonpos Hop Hor). {
  apply (rngl_mul_pos_neg Hon Hop Hiq Hor); [ | easy ].
  apply not_eq_sym in Hs1z.
  now apply (rngl_le_neq Hor).
} {
  apply (rngl_mul_nonpos_nonneg Hon Hop Hiq Hor); [ | easy ].
  now apply (rngl_lt_le_incl Hor).
}
Qed.

Theorem quadrant_1_sin_sub_nonneg_cos_le :
  ∀ θ1 θ2,
  (0 ≤ rngl_sin θ1)%L
  → (0 ≤ rngl_sin θ2)%L
  → (0 ≤ rngl_cos θ2)%L
  → (0 ≤ rngl_sin (θ1 - θ2))%L
  → (rngl_cos θ1 ≤ rngl_cos θ2)%L.
Proof.
destruct_ac.
specialize (rngl_int_dom_or_inv_1_quo Hiv Hon) as Hii.
specialize (rngl_has_eq_dec_or_is_ordered_r Hor) as Heo.
destruct (Nat.eq_dec (rngl_characteristic T) 1) as [Hc1| Hc1]. {
  specialize (rngl_characteristic_1 Hon Hos Hc1) as H1.
  intros.
  do 2 rewrite (H1 (rngl_cos _)).
  apply (rngl_le_refl Hor).
}
intros * Hsz1 Hzs2 Hzc2 Hzs12.
destruct (rngl_eq_dec Heo (rngl_sin θ2) 0) as [Hs2z| Hs2z]. {
  apply eq_rngl_sin_0 in Hs2z.
  destruct Hs2z; subst θ2; [ apply rngl_cos_bound | ].
  exfalso.
  apply rngl_nlt_ge in Hzc2.
  apply Hzc2; clear Hzc2; cbn.
  apply (rngl_opp_1_lt_0 Hon Hop Hiq Hor Hc1).
}
cbn in Hzs12.
rewrite (rngl_mul_opp_r Hop) in Hzs12.
rewrite (rngl_add_opp_r Hop) in Hzs12.
apply -> (rngl_le_0_sub Hop Hor) in Hzs12.
apply (rngl_lt_eq_cases Hor) in Hzs2.
apply not_eq_sym in Hs2z.
destruct Hzs2 as [Hzs2| Hzs2]; [ | easy ].
clear Hs2z.
apply (rngl_mul_le_mono_pos_r Hon Hop Hiq Hor _ _ (rngl_sin θ2) Hzs2) in Hzs12.
rewrite <- rngl_mul_assoc in Hzs12.
rewrite fold_rngl_squ in Hzs12.
specialize (cos2_sin2_1 θ2) as H1.
apply (rngl_add_move_l Hop) in H1.
rewrite H1 in Hzs12; clear H1.
rewrite (rngl_mul_sub_distr_l Hop) in Hzs12.
rewrite (rngl_mul_1_r Hon) in Hzs12.
apply (rngl_le_sub_le_add_l Hop Hor) in Hzs12.
eapply (rngl_le_trans Hor); [ apply Hzs12 | ].
rewrite (rngl_mul_mul_swap Hic).
progress unfold rngl_squ.
rewrite rngl_mul_assoc.
rewrite <- rngl_mul_add_distr_r.
rewrite <- rngl_cos_sub.
rewrite <- (rngl_mul_1_l Hon).
apply (rngl_mul_le_mono_nonneg_r Hon Hop Hiq Hor); [ easy | ].
apply rngl_cos_bound.
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
apply (rngl_lt_le_incl Hor) in Hzs2.
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
apply (rngl_le_0_add Hos Hor).
now apply (rngl_mul_nonneg_nonneg Hon Hos Hiq Hor).
now apply (rngl_mul_nonneg_nonneg Hon Hos Hiq Hor).
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
apply (rngl_le_neq Hor).
split. {
  apply quadrant_1_sin_sub_nonneg_cos_le; try easy.
  now apply (rngl_lt_le_incl Hor).
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
apply (rngl_opp_nonneg_nonpos Hop Hor) in Hs1z.
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

Theorem rngl_sin_sub_lt_sin_l :
  ∀ θ1 θ2,
  (0 ≤ rngl_sin θ1)%L
  → (0 < rngl_sin θ2)%L
  → (0 < rngl_cos θ1)%L
  → (rngl_sin (θ1 - θ2) < rngl_sin θ1)%L.
Proof.
destruct_ac.
specialize (rngl_int_dom_or_inv_1_quo Hiv Hon) as Hii.
intros * Hc1z Hzs2 Hzc1.
cbn.
rewrite (rngl_mul_opp_r Hop).
rewrite (rngl_add_opp_r Hop).
apply (rngl_lt_sub_lt_add_r Hop Hor).
eapply (rngl_le_lt_trans Hor _ (rngl_sin θ1)). {
  apply (rngl_le_0_sub Hop Hor).
  rewrite (rngl_sub_mul_r_diag_l Hon Hop).
  apply (rngl_mul_nonneg_nonneg Hon Hos Hiq Hor); [ easy | ].
  apply (rngl_le_0_sub Hop Hor).
  apply rngl_cos_bound.
}
apply (rngl_lt_add_r Hos Hor).
now apply (rngl_mul_pos_pos Hon Hop Hiq Hor).
Qed.

Theorem angle_add_overflow_equiv2 :
  ∀ θ1 θ2,
  angle_add_overflow2 θ1 θ2 = angle_add_overflow θ1 θ2.
Proof.
destruct_ac.
specialize (rngl_int_dom_or_inv_1_quo Hiv Hon) as Hii.
specialize (rngl_has_eq_dec_or_is_ordered_l Hed) as Heo.
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
rewrite (rngl_leb_opp_r Hop Hor).
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
    rewrite (rngl_leb_opp_r Hop Hor).
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
            apply (rngl_leb_gt Hor).
            apply (rngl_opp_1_lt_1 Hon Hop Hiq Hor Hc1).
          }
        }
        cbn.
        rewrite (rngl_opp_involutive Hop).
        transitivity true. {
          apply rngl_ltb_lt.
          apply (rngl_opp_1_lt_1 Hon Hop Hiq Hor Hc1).
        } {
          symmetry.
          apply rngl_leb_le.
          apply (rngl_le_refl Hor).
        }
      }
      symmetry.
      apply (rngl_leb_gt Hor).
      apply (rngl_le_neq Hor).
      split; [ apply rngl_cos_bound | ].
      intros H; symmetry in H.
      apply eq_rngl_cos_opp_1 in H; subst θ2.
      cbn in Hs2z, Hzs2.
      now rewrite Hs2z in Hzs2.
    }
    destruct s2z. {
      apply rngl_ltb_lt.
      apply (rngl_opp_lt_compat Hop Hor).
      do 2 rewrite (rngl_opp_involutive Hop).
      apply (rngl_le_neq Hor).
      split; [ apply rngl_cos_bound | ].
      intros H.
      apply eq_rngl_cos_1 in H; subst θ2.
      cbn in Hs2z, Hzs2.
      now rewrite Hs2z in Hzs2.
    }
    exfalso.
    apply (rngl_leb_gt Hor) in Hzs2, Hs2z.
    now apply (rngl_lt_asymm Hor) in Hzs2.
  }
  remember (0 ≤? rngl_sin (θ1 + θ2))%L as zs12 eqn:Hzs12.
  remember (0 ≤? rngl_sin θ2)%L as zs2 eqn:Hzs2.
  symmetry in Hzs12, Hzs2.
  destruct zs12. {
    destruct zs2. {
      apply rngl_leb_le in Hzs1, Hzs2, Hzs12.
      apply (rngl_leb_gt Hor) in Hs1z.
      apply rngl_ltb_ge.
      apply rngl_cos_add_le_cos; [ | easy | easy | easy ].
      left.
      intros H; subst θ1.
      cbn in Hs1z.
      now apply (rngl_lt_irrefl Hor) in Hs1z.
    }
    apply rngl_leb_le in Hzs1, Hzs12.
    apply (rngl_leb_gt Hor) in Hs1z, Hzs2.
    destruct (rngl_le_dec Hor 0 (rngl_cos θ1)) as [Hzc1| Hzc1]. {
      remember (rngl_cos θ1 ≤? rngl_cos θ2)%L as c12 eqn:Hc12.
      symmetry in Hc12.
      destruct c12. {
        apply rngl_leb_le in Hc12.
        apply rngl_ltb_lt.
        apply quadrant_1_quadrant_4_cos_lt_cos_add; try easy.
        now apply (rngl_le_trans Hor _ (rngl_cos θ1)).
      }
      apply (rngl_leb_gt Hor) in Hc12.
      apply rngl_ltb_ge.
      destruct (rngl_le_dec Hor 0 (rngl_cos θ2)) as [Hzc2| Hzc2]. {
        exfalso.
        change_angle_opp θ2.
        progress sin_cos_opp_hyp T Hzs2.
        progress sin_cos_opp_hyp T Hzs12.
        progress sin_cos_opp_hyp T Hc12.
        progress sin_cos_opp_hyp T Hzc2.
        apply rngl_nle_gt in Hc12.
        apply Hc12; clear Hc12.
        apply quadrant_1_sin_sub_nonneg_cos_le; try easy.
        now apply (rngl_lt_le_incl Hor) in Hzs2.
      }
      exfalso.
      apply (rngl_nle_gt_iff Hor) in Hzc2.
      change_angle_add_r θ2 angle_straight.
      progress sin_cos_add_sub_straight_hyp T Hzs2.
      progress sin_cos_add_sub_straight_hyp T Hzs12.
      progress sin_cos_add_sub_straight_hyp T Hc12.
      progress sin_cos_add_sub_straight_hyp T Hzc2.
      apply rngl_nlt_ge in Hzs12.
      apply Hzs12; clear Hzs12.
      cbn.
      apply (rngl_lt_0_add Hos Hor).
      now apply (rngl_mul_pos_pos Hon Hop Hiq Hor).
      apply (rngl_lt_le_incl Hor) in Hzs2.
      now apply (rngl_mul_nonneg_nonneg Hon Hos Hiq Hor).
    }
    remember (rngl_cos θ1 ≤? rngl_cos θ2)%L as c12 eqn:Hc12.
    symmetry in Hc12.
    destruct c12. {
      apply rngl_leb_le in Hc12.
      apply rngl_ltb_lt.
      apply (rngl_nle_gt_iff Hor) in Hzc1.
      change_angle_sub_l θ1 angle_straight.
      progress sin_cos_add_sub_straight_hyp T Hzs12.
      progress sin_cos_add_sub_straight_hyp T Hs1z.
      progress sin_cos_add_sub_straight_hyp T Hzs1.
      progress sin_cos_add_sub_straight_hyp T Hc12.
      progress sin_cos_add_sub_straight_hyp T Hzc1.
      progress sin_cos_add_sub_straight_goal T.
      rewrite (rngl_add_opp_r Hop).
      apply (rngl_lt_0_sub Hop Hor).
      destruct (rngl_le_dec Hor 0 (rngl_cos θ2)) as [Hzc2| Hzc2]. {
        change_angle_opp θ2.
        progress sin_cos_opp_hyp T Hzs2.
        progress sin_cos_opp_hyp T Hc12.
        progress sin_cos_opp_hyp T Hzc2.
        rewrite angle_sub_opp_r in Hzs12 |-*.
        apply (rngl_le_neq Hor).
        split. {
          apply (rngl_lt_le_incl Hor) in Hzs2, Hzc1.
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
        apply (rngl_opp_nonneg_nonpos Hop Hor) in Hzs12.
        now apply rngl_nlt_ge in Hzs12.
      }
      apply (rngl_nle_gt_iff Hor) in Hzc2.
      change_angle_add_r θ2 angle_straight.
      rewrite angle_sub_sub_distr in Hzs12 |-*.
      progress sin_cos_add_sub_straight_hyp T Hzs12.
      progress sin_cos_add_sub_straight_hyp T Hc12.
      progress sin_cos_add_sub_straight_hyp T Hzs2.
      progress sin_cos_add_sub_straight_hyp T Hzc2.
      progress sin_cos_add_sub_straight_goal T.
      apply (rngl_add_nonneg_pos Hos Hor); [ | easy ].
      apply (rngl_lt_le_incl Hor) in Hzs2, Hzc1, Hzc2.
      now apply rngl_cos_sub_nonneg.
    }
    exfalso.
    apply (rngl_nle_gt_iff Hor) in Hzc1.
    apply (rngl_leb_gt Hor) in Hc12.
    change_angle_sub_r θ1 angle_right.
    progress sin_cos_add_sub_right_hyp T Hzs12.
    progress sin_cos_add_sub_right_hyp T Hs1z.
    progress sin_cos_add_sub_right_hyp T Hzs1.
    progress sin_cos_add_sub_right_hyp T Hc12.
    progress sin_cos_add_sub_right_hyp T Hzc1.
    change_angle_add_r θ2 angle_straight.
    progress sin_cos_add_sub_straight_hyp T Hzs12.
    progress sin_cos_add_sub_straight_hyp T Hc12.
    progress sin_cos_add_sub_straight_hyp T Hzs2.
    change_angle_sub_l θ2 angle_right.
    progress sin_cos_add_sub_right_hyp T Hzs12.
    progress sin_cos_add_sub_right_hyp T Hc12.
    progress sin_cos_add_sub_right_hyp T Hzs2.
    apply rngl_nle_gt in Hc12.
    apply Hc12; clear Hc12.
    apply (rngl_lt_le_incl Hor) in Hzc1.
    now apply rngl_sin_sub_nonneg_sin_le_sin.
  }
  destruct zs2; [ easy | symmetry ].
  apply rngl_leb_le in Hzs1.
  apply (rngl_leb_gt Hor) in Hs1z, Hzs12, Hzs2.
  apply (rngl_leb_gt Hor).
  destruct (rngl_le_dec Hor 0 (rngl_cos θ1)) as [Hzc1| Hzc1]. {
    destruct (rngl_le_dec Hor 0 (rngl_cos θ2)) as [Hzc2| Hzc2]. {
      change_angle_opp θ2.
      progress sin_cos_opp_hyp T Hzs2.
      progress sin_cos_opp_hyp T Hzs12.
      progress sin_cos_opp_hyp T Hzc2.
      cbn.
      rewrite rngl_sin_sub_anticomm in Hzs12.
      apply (rngl_opp_neg_pos Hop Hor) in Hzs12.
      apply (rngl_lt_le_incl Hor) in Hzs2.
      now apply quadrant_1_sin_sub_pos_cos_lt.
    }
    apply (rngl_nle_gt_iff Hor) in Hzc2.
    now apply (rngl_lt_le_trans Hor _ 0).
  }
  apply (rngl_nle_gt_iff Hor) in Hzc1.
  change_angle_sub_r θ1 angle_right.
  progress sin_cos_add_sub_right_hyp T Hzs12.
  progress sin_cos_add_sub_right_hyp T Hs1z.
  progress sin_cos_add_sub_right_hyp T Hzs1.
  progress sin_cos_add_sub_right_hyp T Hzc1.
  progress sin_cos_add_sub_right_goal T.
  destruct (rngl_le_dec Hor 0 (rngl_cos θ2)) as [Hzc2| Hzc2]. {
    exfalso.
    change_angle_opp θ2.
    progress sin_cos_opp_hyp T Hzs2.
    progress sin_cos_opp_hyp T Hzs12.
    progress sin_cos_opp_hyp T Hzc2.
    apply (rngl_nle_gt_iff Hor) in Hzs12.
    apply Hzs12; clear Hzs12.
    apply (rngl_lt_le_incl Hor) in Hzc1, Hzs2.
    now apply rngl_cos_sub_nonneg.
  }
  apply (rngl_nle_gt_iff Hor) in Hzc2.
  change_angle_add_r θ2 angle_straight.
  progress sin_cos_add_sub_straight_hyp T Hzs12.
  progress sin_cos_add_sub_straight_hyp T Hzs2.
  progress sin_cos_add_sub_straight_hyp T Hzc2.
  progress sin_cos_add_sub_straight_goal T.
  rewrite (rngl_add_opp_r Hop).
  change_angle_sub_l θ2 angle_right.
  progress sin_cos_add_sub_right_hyp T Hzs12.
  progress sin_cos_add_sub_right_hyp T Hzs2.
  progress sin_cos_add_sub_right_hyp T Hzc2.
  progress sin_cos_add_sub_right_goal T.
  rewrite rngl_sin_sub_anticomm in Hzs12.
  apply (rngl_opp_neg_pos Hop Hor) in Hzs12.
  apply (rngl_le_neq Hor).
  split. {
    apply (rngl_lt_le_incl Hor) in Hzc2, Hzs2, Hzs12.
    now apply rngl_sin_sub_nonneg_sin_le_sin.
  }
  intros H12.
  apply rngl_sin_eq in H12.
  destruct H12; subst θ1. {
    rewrite angle_sub_diag in Hzs12.
    now apply (rngl_lt_irrefl Hor) in Hzs12.
  }
  rewrite rngl_cos_sub_straight_l in Hzs1.
  apply (rngl_opp_nonneg_nonpos Hop Hor) in Hzs1.
  now apply rngl_nlt_ge in Hzs1.
}
destruct s1z. {
  remember (0 ≤? rngl_sin (θ1 + θ2))%L as zs12 eqn:Hzs12.
  remember (0 ≤? rngl_sin θ2)%L as s2z eqn:Hs2z.
  symmetry in Hzs12, Hs2z.
  destruct zs12. {
    destruct s2z; [ symmetry | easy ].
    apply (rngl_leb_gt Hor) in Hzs1.
    apply rngl_leb_le in Hzs12, Hs2z, Hs1z.
    apply rngl_leb_le.
    destruct (rngl_le_dec Hor 0 (rngl_cos θ1)) as [Hzc1| Hzc1]. {
      change_angle_opp θ1.
      progress sin_cos_opp_hyp T Hs1z.
      progress sin_cos_opp_hyp T Hzs1.
      progress sin_cos_opp_hyp T Hzc1.
      cbn.
      rewrite angle_add_opp_l in Hzs12.
      rewrite rngl_sin_sub_anticomm in Hzs12.
      apply (rngl_opp_nonneg_nonpos Hop Hor) in Hzs12.
      apply rngl_nlt_ge in Hzs12.
      apply (rngl_nlt_ge_iff Hor).
      intros H12.
      apply Hzs12; clear Hzs12.
      apply (rngl_le_neq Hor).
      split. {
        apply (rngl_lt_le_incl Hor) in Hzs1, H12.
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
      apply (rngl_opp_pos_neg Hop Hor) in Hzs1.
      now apply rngl_nle_gt in Hzs1.
    }
    apply (rngl_nle_gt_iff Hor) in Hzc1.
    change_angle_add_r θ1 angle_straight.
    progress sin_cos_add_sub_straight_hyp T Hzs12.
    progress sin_cos_add_sub_straight_hyp T Hs1z.
    progress sin_cos_add_sub_straight_hyp T Hzs1.
    progress sin_cos_add_sub_straight_hyp T Hzc1.
    progress sin_cos_add_sub_straight_goal T.
    destruct (rngl_le_dec Hor 0 (rngl_cos θ2)) as [Hzc2| Hzc2]. {
      apply (rngl_nlt_ge_iff Hor).
      intros Hc21.
      apply rngl_nlt_ge in Hzs12.
      apply Hzs12; clear Hzs12.
      apply (rngl_le_neq Hor).
      split. {
        apply (rngl_lt_le_incl Hor) in Hzc1.
        now apply rngl_sin_add_nonneg.
      }
      intros H; symmetry in H.
      apply eq_rngl_sin_0 in H.
      destruct H as [H1| H1]. {
        apply -> angle_add_move_0_r in H1; subst θ1.
        apply (rngl_opp_pos_neg Hop Hor) in Hzs1.
        now apply rngl_nle_gt in Hzs1.
      }
      apply angle_add_move_r in H1; subst θ1.
      rewrite rngl_cos_sub_straight_l in Hzc1.
      apply (rngl_opp_pos_neg Hop Hor) in Hzc1.
      now apply rngl_nle_gt in Hzc1.
    }
    apply (rngl_nle_gt_iff Hor) in Hzc2.
    change_angle_sub_l θ2 angle_straight.
    progress sin_cos_add_sub_straight_hyp T Hzs12.
    progress sin_cos_add_sub_straight_hyp T Hs2z.
    progress sin_cos_add_sub_straight_hyp T Hzc2.
    progress sin_cos_add_sub_straight_goal T.
    rewrite (rngl_add_opp_l Hop).
    apply (rngl_le_sub_0 Hop Hor).
    apply (rngl_lt_eq_cases Hor).
    destruct (rngl_eq_dec Heo (rngl_cos θ1) (rngl_cos θ2)) as [Hc12| Hc12]. {
      now right.
    }
    left.
    apply (rngl_lt_le_incl Hor) in Hzc1, Hzc2.
    apply quadrant_1_sin_sub_pos_cos_lt; try easy.
    apply (rngl_le_neq Hor).
    split; [ easy | ].
    intros H; symmetry in H.
    apply eq_rngl_sin_0 in H.
    destruct H as [H1| H1]. {
      now apply -> angle_sub_move_0_r in H1; subst θ2.
    }
    apply angle_sub_move_r in H1; subst θ1.
    rewrite rngl_sin_add_straight_l in Hzs1.
    apply (rngl_opp_pos_neg Hop Hor) in Hzs1.
    now apply rngl_nle_gt in Hzs1.
  }
  destruct s2z. {
    remember (rngl_cos θ2 ≤? rngl_cos θ1)%L as c21 eqn:Hc21.
    symmetry in Hc21.
    destruct c21. {
      apply rngl_leb_le in Hs1z, Hs2z, Hc21.
      apply (rngl_leb_gt Hor) in Hzs1, Hzs12.
      apply rngl_ltb_lt.
      destruct (rngl_le_dec Hor 0 (rngl_cos θ1)) as [Hzc1| Hzc1]. {
        change_angle_opp θ1.
        progress sin_cos_opp_hyp T Hs1z.
        progress sin_cos_opp_hyp T Hzs1.
        progress sin_cos_opp_hyp T Hzc1.
        progress sin_cos_opp_hyp T Hc21.
        rewrite angle_add_opp_l in Hzs12.
        rewrite angle_add_opp_l, rngl_cos_opp.
        destruct (rngl_le_dec Hor 0 (rngl_cos θ2)) as [Hzc2| Hzc2]. {
          apply (rngl_nle_gt_iff Hor).
          intros Hc121.
          apply rngl_nle_gt in Hzs12.
          apply Hzs12; clear Hzs12.
          apply (rngl_lt_le_incl Hor) in Hzs1.
          now apply rngl_sin_sub_nonneg.
        }
        exfalso.
        apply (rngl_nle_gt_iff Hor) in Hzc2.
        change_angle_sub_l θ2 angle_straight.
        rewrite <- angle_sub_add_distr in Hzs12.
        progress sin_cos_add_sub_straight_hyp T Hzs12.
        progress sin_cos_add_sub_straight_hyp T Hs2z.
        progress sin_cos_add_sub_straight_hyp T Hzc2.
        progress sin_cos_add_sub_straight_hyp T Hc21.
        apply rngl_nle_gt in Hzs12.
        apply Hzs12; clear Hzs12.
        apply (rngl_lt_le_incl Hor) in Hzs1, Hzc2.
        now apply rngl_sin_add_nonneg.
      }
      exfalso.
      apply (rngl_nle_gt_iff Hor) in Hzc1.
      change_angle_add_r θ1 angle_straight.
      progress sin_cos_add_sub_straight_hyp T Hzs12.
      progress sin_cos_add_sub_straight_hyp T Hs1z.
      progress sin_cos_add_sub_straight_hyp T Hzs1.
      progress sin_cos_add_sub_straight_hyp T Hzc1.
      progress sin_cos_add_sub_straight_hyp T Hc21.
      change_angle_sub_l θ2 angle_straight.
      progress sin_cos_add_sub_straight_hyp T Hzs12.
      progress sin_cos_add_sub_straight_hyp T Hs2z.
      progress sin_cos_add_sub_straight_hyp T Hc21.
      apply -> (rngl_le_sub_0 Hop Hor) in Hc21.
      apply rngl_nle_gt in Hzs12.
      apply Hzs12; clear Hzs12.
      now apply rngl_sin_sub_nonneg.
    }
    apply rngl_leb_le in Hs1z, Hs2z.
    apply (rngl_leb_gt Hor) in Hzs1, Hzs12, Hc21.
    apply rngl_ltb_ge.
    destruct (rngl_le_dec Hor 0 (rngl_cos θ1)) as [Hzc1| Hzc1]. {
      change_angle_add_r θ1 angle_right.
      progress sin_cos_add_sub_right_hyp T Hs1z.
      progress sin_cos_add_sub_right_hyp T Hzs1.
      progress sin_cos_add_sub_right_hyp T Hzc1.
      progress sin_cos_add_sub_right_hyp T Hc21.
      progress sin_cos_add_sub_right_hyp T Hzs12.
      progress sin_cos_add_sub_right_goal T.
      apply rngl_sin_sub_nonneg_sin_le_sin. {
        apply (rngl_sin_add_nonneg); try easy.
        apply (rngl_lt_le_incl Hor) in Hc21.
        now apply (rngl_le_trans Hor _ (rngl_sin θ1)).
      } {
        now apply (rngl_lt_le_incl Hor) in Hzs12.
      } {
        now rewrite angle_add_comm, angle_add_sub.
      }
    }
    apply (rngl_nle_gt_iff Hor) in Hzc1.
    change_angle_add_r θ1 angle_straight.
    progress sin_cos_add_sub_straight_hyp T Hzs12.
    progress sin_cos_add_sub_straight_hyp T Hs1z.
    progress sin_cos_add_sub_straight_hyp T Hzs1.
    progress sin_cos_add_sub_straight_hyp T Hzc1.
    progress sin_cos_add_sub_straight_hyp T Hc21.
    progress sin_cos_add_sub_straight_goal T.
    apply (rngl_lt_opp_l Hop Hor) in Hc21.
    destruct (rngl_le_dec Hor 0 (rngl_cos θ2)) as [Hzc2| Hzc2]. {
      apply (rngl_lt_le_incl Hor) in Hzc1.
      now apply quadrant_1_rngl_cos_add_le_cos_l.
    }
    apply (rngl_nle_gt_iff Hor) in Hzc2.
    change_angle_sub_l θ2 angle_straight.
    progress sin_cos_add_sub_straight_hyp T Hzs12.
    progress sin_cos_add_sub_straight_hyp T Hs2z.
    progress sin_cos_add_sub_straight_hyp T Hzc2.
    progress sin_cos_add_sub_straight_hyp T Hc21.
    progress sin_cos_add_sub_straight_goal T.
    apply (rngl_lt_le_incl Hor) in Hzc1, Hzc2.
    apply (rngl_le_0_add Hos Hor); [ | easy ].
    now apply rngl_cos_sub_nonneg.
  }
  apply rngl_leb_le in Hs1z.
  apply (rngl_leb_gt Hor) in Hzs1, Hzs12, Hs2z.
  apply rngl_ltb_lt.
  destruct (rngl_le_dec Hor 0 (rngl_cos θ1)) as [Hzc1| Hzc1]. {
    change_angle_add_r θ1 angle_right.
    progress sin_cos_add_sub_right_hyp T Hzs12.
    progress sin_cos_add_sub_right_hyp T Hs1z.
    progress sin_cos_add_sub_right_hyp T Hzs1.
    progress sin_cos_add_sub_right_hyp T Hzc1.
    progress sin_cos_add_sub_right_goal T.
    destruct (rngl_le_dec Hor 0 (rngl_cos θ2)) as [Hzc2| Hzc2]. {
      change_angle_opp θ2.
      progress sin_cos_opp_hyp T Hzs12.
      progress sin_cos_opp_hyp T Hs2z.
      progress sin_cos_opp_hyp T Hzc2.
      progress sin_cos_opp_goal T.
      now apply rngl_sin_sub_lt_sin_l.
    }
    apply (rngl_nle_gt_iff Hor) in Hzc2.
    change_angle_add_r θ2 angle_straight.
    progress sin_cos_add_sub_straight_hyp T Hzs12.
    progress sin_cos_add_sub_straight_hyp T Hs2z.
    progress sin_cos_add_sub_straight_hyp T Hzc2.
    progress sin_cos_add_sub_straight_goal T.
    apply (rngl_lt_0_add Hos Hor); [ cbn | easy ].
    apply (rngl_add_nonneg_pos Hos Hor).
    apply (rngl_lt_le_incl Hor) in Hzc2.
    now apply (rngl_mul_nonneg_nonneg Hon Hos Hiq Hor).
    now apply (rngl_mul_pos_pos Hon Hop Hiq Hor).
  }
  apply (rngl_nle_gt_iff Hor) in Hzc1.
  change_angle_add_r θ1 angle_straight.
  progress sin_cos_add_sub_straight_hyp T Hzs12.
  progress sin_cos_add_sub_straight_hyp T Hs1z.
  progress sin_cos_add_sub_straight_hyp T Hzs1.
  progress sin_cos_add_sub_straight_hyp T Hzc1.
  progress sin_cos_add_sub_straight_goal T.
  rewrite (rngl_add_opp_r Hop).
  apply (rngl_lt_0_sub Hop Hor).
  destruct (rngl_le_dec Hor 0 (rngl_cos θ2)) as [Hzc2| Hzc2]. {
    change_angle_opp θ2.
    progress sin_cos_opp_hyp T Hzs12.
    progress sin_cos_opp_hyp T Hs2z.
    progress sin_cos_opp_hyp T Hzc2.
    progress sin_cos_opp_goal T.
    rewrite rngl_cos_sub_comm.
    apply rngl_cos_lt_cos_sub; try easy.
    apply (rngl_lt_le_incl Hor) in Hs2z, Hzc1, Hzs12.
    now apply quadrant_1_sin_sub_nonneg_cos_le.
  }
  exfalso.
  apply (rngl_nle_gt_iff Hor) in Hzc2.
  change_angle_add_r θ2 angle_straight.
  progress sin_cos_add_sub_straight_hyp T Hzs12.
  progress sin_cos_add_sub_straight_hyp T Hs2z.
  progress sin_cos_add_sub_straight_hyp T Hzc2.
  apply rngl_nle_gt in Hzs12.
  apply Hzs12; clear Hzs12.
  apply (rngl_lt_le_incl Hor) in Hs2z, Hzc1, Hzc2.
  now apply rngl_sin_add_nonneg.
}
apply (rngl_leb_gt Hor) in Hzs1, Hs1z.
now apply (rngl_lt_asymm Hor) in Hzs1.
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
apply (rngl_leb_gt Hor) in Haov.
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
specialize (rngl_int_dom_or_inv_1_quo Hiv Hon) as Hii.
specialize (rngl_has_eq_dec_or_is_ordered_r Hor) as Heo.
destruct (Nat.eq_dec (rngl_characteristic T) 1) as [Hc1| Hc1]. {
  specialize (rngl_characteristic_1 Hon Hos Hc1) as H1.
  intros.
  rewrite H1, (H1 (rngl_cos _)).
  apply (rngl_le_refl Hor).
}
intros * Hzs1 Hzs2 Hzs3 Hzc2 Hc123 Hzs12 Hzs23.
destruct (rngl_le_dec Hor 0 (rngl_cos θ3))%L as [Hzc3| Hc3z]. {
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
apply (rngl_nle_gt_iff Hor) in Hc3z.
change_angle_sub_r θ3 angle_right.
progress sin_cos_add_sub_right_hyp T Hzs3.
progress sin_cos_add_sub_right_hyp T Hc123.
progress sin_cos_add_sub_right_hyp T Hc3z.
progress sin_cos_add_sub_right_hyp T Hzs23.
progress sin_cos_add_sub_right_goal T.
destruct (rngl_le_dec Hor 0 (rngl_cos θ1))%L as [Hzc1| Hc1z]. {
  move Hzc1 before Hc3z.
  apply (rngl_le_0_add Hos Hor); [ | easy ].
  apply (rngl_lt_le_incl Hor) in Hc3z.
  now apply (rngl_sin_add_nonneg).
}
apply (rngl_nle_gt_iff Hor) in Hc1z.
change_angle_sub_r θ1 angle_right.
progress sin_cos_add_sub_right_hyp T Hzs1.
progress sin_cos_add_sub_right_hyp T Hzs12.
progress sin_cos_add_sub_right_hyp T Hc123.
progress sin_cos_add_sub_right_hyp T Hc1z.
progress sin_cos_add_sub_right_goal T.
destruct (rngl_eq_dec Heo (rngl_cos θ2) 0) as [Hc2z| Hc2z]. {
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
rename Hc123 into Hs123.
destruct (rngl_le_dec Hor (rngl_cos θ1) (rngl_cos (θ2 + θ3)))
    as [Hc123| Hc231]. {
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
apply (rngl_nle_gt_iff Hor) in Hc231.
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
destruct (rngl_le_dec Hor 0 (rngl_cos θ1)) as [Hzc1| Hc1z]. {
  change_angle_add_r θ1 angle_right.
  progress sin_cos_add_sub_right_hyp T Hzs1.
  progress sin_cos_add_sub_right_hyp T Hzc1.
  progress sin_cos_add_sub_right_hyp T Hzs12.
  progress sin_cos_add_sub_right_goal T.
  destruct (rngl_le_dec Hor 0 (rngl_cos θ2)) as [Hzc2| Hc2z]. {
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
  apply (rngl_nle_gt_iff Hor) in Hc2z.
  exfalso.
  change_angle_sub_r θ2 angle_right.
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
apply (rngl_nle_gt_iff Hor) in Hc1z.
change_angle_sub_r θ1 angle_straight.
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
change_angle_sub_r θ1 angle_right.
progress sin_cos_add_sub_right_hyp T Hzs1.
progress sin_cos_add_sub_right_hyp T Hco1.
progress sin_cos_add_sub_right_hyp T Hzs12.
progress sin_cos_add_sub_right_hyp T Hc1z.
progress sin_cos_add_sub_right_goal T.
destruct (rngl_le_dec Hor (rngl_cos θ2) 0) as [Hc2z| Hzc2]. {
  change_angle_sub_r θ2 angle_right.
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
apply (rngl_nle_gt_iff Hor) in Hzc2.
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
specialize (rngl_has_eq_dec_or_is_ordered_r Hor) as Heo.
intros * Hc11 Hzs1 Hzs2 Hzc1 Hzs12 H12.
specialize (rngl_int_dom_or_inv_1_quo Hiv Hon) as Hii.
destruct (rngl_lt_dec Hor 0 (rngl_cos θ2)) as [Hzc2| Hzc2]. {
  change_angle_opp θ2.
  progress sin_cos_opp_hyp T Hzs2.
  progress sin_cos_opp_hyp T H12.
  progress sin_cos_opp_hyp T Hzs12.
  progress sin_cos_opp_hyp T Hzc2.
  apply rngl_nlt_ge in H12.
  apply H12; clear H12.
  rewrite rngl_cos_sub_comm.
  destruct (rngl_eq_dec Heo (rngl_cos θ1) (rngl_cos θ2)) as [Hc1c2| Hc1c2]. {
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
apply (rngl_nlt_ge_iff Hor) in Hzc2.
change_angle_add_r θ2 angle_straight.
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
specialize (rngl_has_eq_dec_or_is_ordered_r Hor) as Heo.
destruct (Nat.eq_dec (rngl_characteristic T) 1) as [Hc1| Hc1]. {
  specialize (rngl_characteristic_1 Hon Hos Hc1) as H1.
  intros * Hzs1 Hzs2 Hzs12 H12.
  rewrite (H1 (rngl_sin _)) in Hzs2.
  now apply (rngl_lt_irrefl Hor) in Hzs2.
}
intros * Hzs1 Hzs2 Hzs12 H12.
destruct (rngl_lt_dec Hor 0 (rngl_cos θ1)) as [Hzc1| Hzc1]. {
  destruct (rngl_eq_dec Heo (rngl_cos θ1) 1) as [H| H]. {
    apply eq_rngl_cos_1 in H.
    subst θ1.
    rewrite angle_add_0_l in Hzs12.
    now apply rngl_nlt_ge in Hzs12.
  } {
    apply angle_add_overflow_le_lemma_5 in H12; try easy.
  }
}
apply (rngl_nlt_ge_iff Hor) in Hzc1.
change_angle_sub_r θ1 angle_right.
progress sin_cos_add_sub_right_hyp T Hzs1.
progress sin_cos_add_sub_right_hyp T Hzc1.
progress sin_cos_add_sub_right_hyp T H12.
progress sin_cos_add_sub_right_hyp T Hzs12.
destruct (rngl_lt_dec Hor 0 (rngl_cos θ2)) as [Hzc2| Hzc2]. {
  change_angle_opp θ2.
  progress sin_cos_opp_hyp T Hzs2.
  progress sin_cos_opp_hyp T Hzc2.
  progress sin_cos_opp_hyp T Hzs12.
  progress sin_cos_opp_hyp T H12.
  apply rngl_nlt_ge in H12.
  apply H12; clear H12.
  rename Hzs12 into Hzc12.
  destruct (rngl_lt_dec Hor (rngl_sin (θ1 - θ2)) 0) as [Hs12z| Hzs12]. {
    eapply (rngl_lt_le_trans Hor); [ apply Hs12z | easy ].
  }
  apply (rngl_nlt_ge_iff Hor) in Hzs12.
  destruct (rngl_eq_dec Heo (rngl_cos θ2) 1) as [Hc21| Hc21]. {
    apply eq_rngl_cos_1 in Hc21.
    subst θ2.
    now apply (rngl_lt_irrefl Hor) in Hzs2.
  }
  destruct (rngl_eq_dec Heo (rngl_cos θ1) 0) as [Hc1z| Hc1z]. {
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
  apply rngl_sin_sub_lt_sin_l; [ easy | easy | ].
  apply (rngl_le_neq Hor).
  now apply not_eq_sym in Hc1z.
}
apply (rngl_nlt_ge_iff Hor) in Hzc2.
change_angle_add_r θ2 angle_straight.
progress sin_cos_add_sub_straight_hyp T Hzs2.
progress sin_cos_add_sub_straight_hyp T Hzc2.
progress sin_cos_add_sub_straight_hyp T Hzs12.
progress sin_cos_add_sub_straight_hyp T H12.
apply rngl_nlt_ge in H12.
apply H12; clear H12.
destruct (rngl_eq_dec Heo (rngl_sin θ1) 0) as [Hs1z| Hs1z]. {
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

Theorem angle_nonpos : ∀ θ, (θ ≤ 0)%A → θ = 0%A.
Proof.
destruct_ac.
intros * Hz.
progress unfold angle_leb in Hz.
cbn in Hz.
rewrite (rngl_leb_refl Hor) in Hz.
remember (0 ≤? rngl_sin θ)%L as zs eqn:Hzs.
symmetry in Hzs.
destruct zs; [ | easy ].
apply rngl_leb_le in Hz.
specialize (rngl_cos_bound θ) as H1.
destruct H1 as (_, H1).
apply (rngl_le_antisymm Hor) in Hz; [ | easy ].
now apply eq_rngl_cos_1 in Hz.
Qed.

Theorem angle_add_overflow_comm :
  ∀ θ1 θ2,
  angle_add_overflow θ1 θ2 = angle_add_overflow θ2 θ1.
Proof.
destruct_ac.
intros.
progress unfold angle_add_overflow.
remember (θ1 ≠? 0)%A as z1 eqn:Hz1.
remember (θ2 ≠? 0)%A as z2 eqn:Hz2.
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
  subst θ1.
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
  do 2 rewrite (rngl_leb_0_opp Hop Hor).
  remember (rngl_sin θ1 ≤? 0)%L as s1z eqn:Hs1z.
  remember (rngl_sin θ2 ≤? 0)%L as s2z eqn:Hs2z.
  remember (0 ≤? rngl_sin θ1)%L as zs1 eqn:Hzs1.
  remember (0 ≤? rngl_sin θ2)%L as zs2 eqn:Hzs2.
  symmetry in Hs1z, Hs2z, Hzs1, Hzs2.
  destruct s1z. {
    destruct zs1. {
      apply rngl_leb_le in Hs1z, Hzs1.
      apply (rngl_le_antisymm Hor) in Hzs1; [ clear Hs1z | easy ].
      apply eq_rngl_sin_0 in Hzs1.
      destruct Hzs1; subst θ1; [ easy | ].
      cbn.
      destruct zs2. {
        destruct s2z. {
          apply rngl_leb_le in Hs2z, Hzs2.
          apply (rngl_le_antisymm Hor) in Hzs2; [ clear Hs2z | easy ].
          apply eq_rngl_sin_0 in Hzs2.
          now destruct Hzs2; subst θ2.
        }
        apply (rngl_leb_gt Hor).
        apply (rngl_le_neq Hor).
        split; [ apply rngl_cos_bound | ].
        intros H; symmetry in H.
        apply eq_rngl_cos_opp_1 in H.
        subst θ2.
        cbn in Hs2z.
        now rewrite (rngl_leb_refl Hor) in Hs2z.
      }
      symmetry.
      destruct s2z. {
        apply rngl_leb_le.
        apply rngl_cos_bound.
      }
      exfalso.
      apply (rngl_leb_gt Hor) in Hs2z, Hzs2.
      now apply (rngl_lt_asymm Hor) in Hs2z.
    }
    destruct zs2. {
      destruct s2z; [ | easy ].
      apply rngl_leb_le in Hs2z, Hzs2.
      apply (rngl_le_antisymm Hor) in Hzs2; [ clear Hs2z | easy ].
      apply eq_rngl_sin_0 in Hzs2.
      destruct Hzs2; subst θ2; [ easy | cbn ].
      apply rngl_leb_le.
      apply rngl_cos_bound.
    }
    symmetry.
    destruct s2z; [ easy | ].
    apply (rngl_leb_gt Hor) in Hs2z, Hzs2.
    now apply (rngl_lt_asymm Hor) in Hs2z.
  }
  destruct zs1. {
    destruct zs2. {
      symmetry.
      destruct s2z; [ | easy ].
      apply rngl_leb_le in Hs2z, Hzs2.
      apply (rngl_le_antisymm Hor) in Hzs2; [ clear Hs2z | easy ].
      apply eq_rngl_sin_0 in Hzs2.
      destruct Hzs2; subst θ2; [ easy | cbn ].
      apply (rngl_leb_gt Hor).
      apply (rngl_le_neq Hor).
      split; [ apply rngl_cos_bound | ].
      intros H; symmetry in H.
      apply eq_rngl_cos_opp_1 in H; subst θ1.
      cbn in Hs1z.
      now rewrite rngl_leb_refl in Hs1z.
    }
    destruct s2z; [ easy | ].
    apply (rngl_leb_gt Hor) in Hs2z, Hzs2.
    now apply (rngl_lt_asymm Hor) in Hs2z.
  }
  apply (rngl_leb_gt Hor) in Hs1z, Hzs1.
  now apply (rngl_lt_asymm Hor) in Hs1z.
}
apply Bool.negb_false_iff in Hz2.
apply angle_eqb_eq in Hz2.
subst θ2; cbn.
(* lemma *)
progress unfold angle_leb.
cbn.
rewrite (rngl_leb_refl Hor).
rewrite (rngl_leb_0_opp Hop Hor).
destruct (rngl_sin θ1 ≤? 0)%L; [ | easy ].
apply (rngl_leb_gt Hor).
apply (rngl_le_neq Hor).
split; [ apply rngl_cos_bound | ].
intros H.
apply eq_rngl_cos_1 in H.
now apply angle_neqb_neq in Hz1.
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

Theorem angle_le_trans :
  ∀ θ1 θ2 θ3,
  (θ1 ≤ θ2 → θ2 ≤ θ3 → θ1 ≤ θ3)%A.
Proof.
destruct_ac.
intros * H12 H23.
progress unfold angle_leb in H12.
progress unfold angle_leb in H23.
progress unfold angle_leb.
remember (0 ≤? rngl_sin θ1)%L as z1 eqn:Hz1.
remember (0 ≤? rngl_sin θ2)%L as z2 eqn:Hz2.
remember (0 ≤? rngl_sin θ3)%L as z3 eqn:Hz3.
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
  now apply (rngl_le_trans Hor _ (rngl_cos θ2)).
} {
  destruct z2; [ easy | ].
  destruct z3; [ easy | ].
  apply rngl_leb_le in H12, H23.
  apply rngl_leb_le.
  now apply (rngl_le_trans Hor _ (rngl_cos θ2)).
}
Qed.

Definition angle_eucl_distance :=
  {| d_dist := angle_eucl_dist; d_prop := angle_eucl_dist_is_dist |}.

Definition angle_taxi_distance :=
  {| d_dist := angle_taxi_dist; d_prop := angle_taxi_dist_is_dist |}.

Definition angle_lim := is_limit_when_seq_tends_to_inf angle_eucl_dist.

Theorem angle_eucl_dist_opp_opp :
  ∀ θ1 θ2, angle_eucl_dist (- θ1) (- θ2) = angle_eucl_dist θ1 θ2.
Proof.
destruct_ac.
intros.
progress unfold angle_eucl_dist.
progress unfold rl_modl.
cbn.
f_equal.
f_equal.
rewrite (rngl_sub_opp_r Hop).
rewrite rngl_add_comm.
rewrite (rngl_add_opp_r Hop).
rewrite <- (rngl_opp_sub_distr Hop).
apply (rngl_squ_opp Hop).
Qed.

Theorem angle_eucl_dist_sub_l_diag :
  ∀ θ Δθ, angle_eucl_dist (θ - Δθ) θ = angle_eucl_dist Δθ 0.
Proof.
destruct_ac.
intros.
progress unfold angle_eucl_dist.
progress unfold rl_modl.
remember (θ - Δθ)%A as x; cbn; subst x.
do 4 rewrite (rngl_squ_sub Hop Hic Hon).
rewrite (rngl_squ_1 Hon).
rewrite (rngl_mul_1_r Hon).
rewrite (rngl_squ_0 Hos).
rewrite (rngl_mul_0_r Hos).
rewrite (rngl_mul_0_l Hos).
rewrite (rngl_sub_diag Hos).
rewrite rngl_add_0_l.
rewrite rngl_add_assoc.
rewrite (rngl_add_sub_assoc Hop).
rewrite rngl_add_add_swap.
rewrite <- (rngl_add_sub_swap Hop (rngl_cos θ)²)%L.
rewrite cos2_sin2_1.
rewrite <- (rngl_add_sub_swap Hop).
rewrite <- rngl_add_assoc.
rewrite cos2_sin2_1.
rewrite <- (rngl_add_sub_swap Hop 1)%L.
do 2 rewrite <- rngl_mul_assoc.
rewrite (rngl_sub_mul_r_diag_l Hon Hop).
rewrite <- (rngl_mul_sub_distr_l Hop).
rewrite <- (rngl_sub_add_distr Hos).
remember (θ - Δθ)%A as x.
replace (_ * _ + _ * _)%L with (rngl_cos (θ - x))%A. 2: {
  cbn.
  rewrite (rngl_mul_opp_r Hop).
  now rewrite rngl_sub_opp_r.
}
subst x.
rewrite angle_sub_sub_distr.
rewrite angle_sub_diag.
rewrite angle_add_0_l.
rewrite <- rngl_add_assoc.
rewrite cos2_sin2_1.
rewrite <- (rngl_add_sub_swap Hop).
now rewrite (rngl_sub_mul_r_diag_l Hon Hop).
Qed.

Theorem angle_eucl_dist_move_0_l :
  ∀ θ1 θ2, angle_eucl_dist θ1 θ2 = angle_eucl_dist (θ2 - θ1) 0.
Proof.
destruct_ac.
intros.
replace θ1 with (θ2 - (θ2 - θ1))%A. 2: {
  rewrite angle_sub_sub_distr.
  rewrite angle_sub_diag.
  apply angle_add_0_l.
}
rewrite angle_eucl_dist_sub_l_diag.
rewrite angle_sub_sub_distr.
rewrite angle_sub_diag.
f_equal; symmetry.
apply angle_add_0_l.
Qed.

Theorem angle_eucl_dist_move_0_r :
  ∀ θ1 θ2, angle_eucl_dist θ1 θ2 = angle_eucl_dist (θ1 - θ2) 0.
Proof.
destruct_ac.
intros.
rewrite angle_eucl_dist_move_0_l.
rewrite <- angle_eucl_dist_opp_opp.
rewrite angle_opp_0.
f_equal.
apply angle_opp_sub_distr.
Qed.

Theorem angle_eucl_dist_0_r_cos_sin :
  ∀ θ, ((angle_eucl_dist θ 0)² = (1 - rngl_cos θ)² + (rngl_sin θ)²)%L.
Proof.
destruct_ac.
intros.
progress unfold angle_eucl_dist.
progress unfold rl_modl; cbn.
rewrite (rngl_sub_0_l Hop).
rewrite (rngl_squ_opp Hop).
apply (rngl_squ_sqrt Hon).
apply (rngl_le_0_add Hos Hor);
apply (rngl_squ_nonneg Hon Hos Hiq Hor).
Qed.

Theorem angle_eucl_dist_straight_r_cos_sin :
  ∀ θ,
  ((angle_eucl_dist θ angle_straight)² = (1 + rngl_cos θ)² + (rngl_sin θ)²)%L.
Proof.
destruct_ac.
intros.
progress unfold angle_eucl_dist.
progress unfold rl_modl; cbn.
rewrite (rngl_sub_0_l Hop).
rewrite (rngl_squ_opp Hop).
rewrite <- (rngl_opp_add_distr Hop).
rewrite (rngl_squ_opp Hop).
rewrite (rngl_add_comm 1).
apply (rngl_squ_sqrt Hon).
apply (rngl_le_0_add Hos Hor);
apply (rngl_squ_nonneg Hon Hos Hiq Hor).
Qed.

Theorem rngl_cos_angle_eucl_dist_0_r :
  ∀ θ, (rngl_cos θ = 1 - (angle_eucl_dist θ 0)² / 2)%L.
Proof.
destruct_ac.
specialize (rngl_has_inv_and_1_has_inv_and_1_or_pdiv Hon Hiv) as Hi1.
destruct (Nat.eq_dec (rngl_characteristic T) 1) as [Hc1| Hc1]. {
  specialize (rngl_characteristic_1 Hon Hos Hc1) as H1.
  intros.
  rewrite H1; apply H1.
}
intros.
specialize (angle_eucl_dist_0_r_cos_sin θ) as H1.
rewrite (rngl_squ_sub Hop Hic Hon) in H1.
rewrite (rngl_squ_1 Hon) in H1.
rewrite (rngl_mul_1_r Hon) in H1.
rewrite <- rngl_add_assoc in H1.
rewrite cos2_sin2_1 in H1.
rewrite <- (rngl_add_sub_swap Hop) in H1.
rewrite (rngl_sub_mul_r_diag_l Hon Hop) in H1.
symmetry in H1.
apply (rngl_mul_move_l Hic Hi1) in H1. 2: {
  apply (rngl_2_neq_0 Hon Hos Hiq Hc1 Hor).
}
now apply (rngl_sub_move_l Hop) in H1.
Qed.

Theorem rngl_cos_angle_eucl_dist_straight_r :
  ∀ θ, (rngl_cos θ = (angle_eucl_dist θ angle_straight)² / 2 - 1)%L.
Proof.
destruct_ac.
specialize (rngl_has_inv_and_1_has_inv_and_1_or_pdiv Hon Hiv) as Hi1.
destruct (Nat.eq_dec (rngl_characteristic T) 1) as [Hc1| Hc1]. {
  specialize (rngl_characteristic_1 Hon Hos Hc1) as H1.
  intros.
  rewrite H1; apply H1.
}
intros.
specialize (angle_eucl_dist_straight_r_cos_sin θ) as H1.
rewrite (rngl_squ_add Hic Hon) in H1.
rewrite (rngl_squ_1 Hon) in H1.
rewrite (rngl_mul_1_r Hon) in H1.
rewrite <- rngl_add_assoc in H1.
rewrite cos2_sin2_1 in H1.
rewrite <- rngl_add_add_swap in H1.
rewrite (rngl_add_mul_r_diag_l Hon) in H1.
symmetry in H1.
apply (rngl_mul_move_l Hic Hi1) in H1. 2: {
  apply (rngl_2_neq_0 Hon Hos Hiq Hc1 Hor).
}
now apply (rngl_add_move_l Hop) in H1.
Qed.

Theorem angle_eucl_dist_diag : ∀ θ, angle_eucl_dist θ θ = 0%L.
Proof.
intros.
apply (dist_diag angle_eucl_dist_is_dist).
Qed.

Theorem angle_eucl_dist_nonneg : ∀ θ1 θ2, (0 ≤ angle_eucl_dist θ1 θ2)%L.
Proof.
destruct_ac.
intros.
apply (dist_nonneg Hon Hop Hiv Hor angle_eucl_dist_is_dist).
Qed.

Theorem angle_taxi_dist_nonneg : ∀ θ1 θ2, (0 ≤ angle_taxi_dist θ1 θ2)%L.
Proof.
destruct_ac.
intros.
apply (dist_nonneg Hon Hop Hiv Hor angle_taxi_dist_is_dist).
Qed.

Theorem angle_lim_const :
  ∀ θ1 θ2, angle_lim (λ _, θ1) θ2 → θ2 = θ1.
Proof.
destruct_ac.
destruct (Nat.eq_dec (rngl_characteristic T) 1) as [Hc1| Hc1]. {
  intros.
  specialize (rngl_characteristic_1_angle_0 Hc1) as H1.
  rewrite (H1 θ1); apply H1.
}
intros * H1.
progress unfold angle_lim in H1.
progress unfold is_limit_when_seq_tends_to_inf in H1.
apply angle_eucl_dist_separation.
rewrite angle_eucl_dist_symmetry.
specialize (angle_eucl_dist_nonneg θ1 θ2) as Hzx.
cbn in H1.
remember (angle_eucl_dist θ1 θ2) as x eqn:Hx.
clear θ1 θ2 Hx.
specialize (proj1 (rngl_lt_eq_cases Hor _ x) Hzx) as H3.
destruct H3 as [H3| H3]; [ | easy ].
clear Hzx; exfalso.
specialize (H1 (x / 2)%L).
assert (H : (0 < x / 2)%L). {
  apply (rngl_div_pos Hon Hop Hiv Hor); [ easy | ].
  apply (rngl_0_lt_2 Hon Hos Hiq Hc1 Hor).
}
specialize (H1 H); clear H.
destruct H1 as (N, HN).
specialize (HN N (Nat.le_refl _)).
apply rngl_nle_gt in HN.
apply HN; clear HN.
apply (rngl_le_div_l Hon Hop Hiv Hor).
apply (rngl_0_lt_2 Hon Hos Hiq Hc1 Hor).
rewrite (rngl_mul_2_r Hon).
apply (rngl_le_add_l Hos Hor).
now apply (rngl_lt_le_incl Hor).
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
  rewrite (rl_sqrt_0 Hon Hop Hor); [ easy | ].
  rewrite Hi1.
  apply Bool.orb_true_r.
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
  ∀ θ1 θ2, (θ1 ≤ θ2 ≤ angle_straight)%A → (rngl_cos θ2 ≤ rngl_cos θ1)%L.
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
  ∀ θ1 θ2, (θ1 < θ2 ≤ angle_straight)%A → (rngl_cos θ2 < rngl_cos θ1)%L.
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

Theorem rngl_cos_acos :
  ∀ x, (-1 ≤ x ≤ 1)%L → rngl_cos (rngl_acos x) = x.
Proof.
destruct_ac.
intros * Hx1.
progress unfold rngl_acos.
destruct (rngl_le_dec ac_or x² 1) as [| H]; [ easy | ].
exfalso; apply H; clear H.
now apply (rngl_squ_le_1 Hon Hop Hiq Hor).
Qed.

Theorem rngl_sin_acos :
  ∀ x, (-1 ≤ x ≤ 1)%L → rngl_sin (rngl_acos x) = √(1 - x²)%L.
Proof.
destruct_ac.
intros * Hx1.
progress unfold rngl_acos.
destruct (rngl_le_dec ac_or x² 1) as [| H]; [ easy | ].
exfalso; apply H; clear H.
now apply (rngl_squ_le_1 Hon Hop Hiq Hor).
Qed.

Theorem angle_le_opp_r : ∀ θ1 θ2, θ1 ≠ 0%A → (θ1 ≤ - θ2)%A → (θ2 ≤ - θ1)%A.
Proof.
destruct_ac.
intros * H2z H2.
progress unfold angle_leb in H2.
progress unfold angle_leb.
cbn in H2 |-*.
rewrite (rngl_leb_0_opp Hop Hor) in H2.
rewrite (rngl_leb_opp_r Hop Hor).
rewrite (rngl_opp_0 Hop).
remember (0 ≤? rngl_sin θ1)%L as zs2 eqn:Hzs2.
remember (0 ≤? rngl_sin θ2)%L as zs eqn:Hzs.
remember (rngl_sin θ1 ≤? 0)%L as sz2 eqn:Hsz2.
remember (rngl_sin θ2 ≤? 0)%L as sz eqn:Hsz.
symmetry in Hzs2, Hzs, Hsz2, Hsz.
destruct zs. {
  destruct sz2; [ | easy ].
  destruct zs2; [ | now destruct sz ].
  apply rngl_leb_le in Hzs2, Hzs, Hsz2.
  apply rngl_leb_le.
  apply (rngl_le_antisymm Hor) in Hzs2; [ | easy ].
  apply eq_rngl_sin_0 in Hzs2.
  destruct Hzs2; [ easy | subst θ1 ].
  apply rngl_cos_bound.
}
destruct zs2. 2: {
  destruct sz; [ easy | ].
  apply (rngl_leb_gt Hor) in Hzs2, Hsz, Hzs.
  now apply (rngl_lt_asymm Hor) in Hzs.
}
apply rngl_leb_le in Hzs2.
apply (rngl_leb_gt Hor) in Hzs.
destruct sz. {
  destruct sz2; [ exfalso | easy ].
  apply rngl_leb_le in Hsz, H2, Hsz2.
  apply (rngl_le_antisymm Hor) in Hzs2; [ | easy ].
  apply eq_rngl_sin_0 in Hzs2.
  destruct Hzs2; [ easy | subst θ1 ].
  apply rngl_nlt_ge in H2.
  apply H2; clear H2.
  apply (rngl_le_neq Hor).
  split; [ apply rngl_cos_bound | ].
  cbn; intros Hcc.
  symmetry in Hcc.
  apply eq_rngl_cos_opp_1 in Hcc.
  subst θ2.
  now apply (rngl_lt_irrefl Hor) in Hzs.
}
clear H2.
destruct sz2. {
  exfalso.
  apply rngl_leb_le in Hsz2.
  apply (rngl_le_antisymm Hor) in Hzs2; [ | easy ].
  apply eq_rngl_sin_0 in Hzs2.
  destruct Hzs2; [ easy | subst θ1 ].
  apply (rngl_leb_gt Hor) in Hsz.
  now apply (rngl_lt_asymm Hor) in Hzs.
}
apply (rngl_leb_gt Hor) in Hsz.
now apply (rngl_lt_asymm Hor) in Hzs.
Qed.

Theorem angle_lt_opp_r :
  ∀ θ1 θ2,
  θ1 ≠ 0%A
  → (θ1 < - θ2)%A
  → (θ2 < - θ1)%A.
Proof.
destruct_ac.
intros * Hz1 H12.
progress unfold angle_ltb in H12.
progress unfold angle_ltb.
cbn in H12 |-*.
rewrite (rngl_leb_0_opp Hop Hor) in H12.
rewrite (rngl_leb_0_opp Hop Hor).
remember (0 ≤? rngl_sin θ1)%L as zs1 eqn:Hzs1.
remember (0 ≤? rngl_sin θ2)%L as zs2 eqn:Hzs2.
remember (rngl_sin θ1 ≤? 0)%L as s1z eqn:Hs1z.
remember (rngl_sin θ2 ≤? 0)%L as s2z eqn:Hs2z.
move zs2 before zs1; move s1z before zs2; move s2z before s1z.
symmetry in Hzs1, Hzs2, Hs1z, Hs2z.
destruct zs2. {
  destruct s1z; [ | easy ].
  destruct zs1; [ | now destruct s2z ].
  apply rngl_leb_le in Hzs1, Hs1z.
  apply (rngl_le_antisymm Hor) in Hzs1; [ clear Hs1z | easy ].
  apply eq_rngl_sin_0 in Hzs1.
  destruct Hzs1; [ easy | subst θ1 ].
  destruct s2z. {
    cbn in H12 |-*.
    apply rngl_leb_le in Hzs2, Hs2z.
    apply (rngl_le_antisymm Hor) in Hzs2; [ clear Hs2z | easy ].
    apply eq_rngl_sin_0 in Hzs2.
    destruct Hzs2; subst θ2. {
      apply rngl_ltb_lt in H12.
      apply rngl_nle_gt in H12.
      cbn in H12.
      exfalso; apply H12.
      apply (rngl_opp_1_le_1 Hon Hop Hiq Hor).
    }
    apply rngl_ltb_lt in H12.
    now apply (rngl_lt_irrefl Hor) in H12.
  }
  cbn.
  apply rngl_ltb_lt.
  apply (rngl_le_neq Hor).
  split; [ apply rngl_cos_bound | ].
  intros H; symmetry in H.
  apply eq_rngl_cos_opp_1 in H.
  subst θ2.
  cbn in Hs2z, Hzs2.
  now rewrite Hs2z in Hzs2.
}
destruct s1z. {
  exfalso.
  destruct zs1. {
    apply rngl_leb_le in Hzs1, Hs1z.
    apply (rngl_le_antisymm Hor) in Hzs1; [ clear Hs1z | easy ].
    apply eq_rngl_sin_0 in Hzs1.
    destruct Hzs1; [ easy | subst θ1 ].
    destruct s2z. {
      cbn in H12.
      apply Bool.not_false_iff_true in H12.
      apply H12.
      apply rngl_ltb_ge.
      apply rngl_cos_bound.
    }
    apply (rngl_leb_gt Hor) in Hs2z, Hzs2.
    now apply (rngl_lt_asymm Hor) in Hs2z.
  }
  destruct s2z; [ easy | ].
  apply (rngl_leb_gt Hor) in Hs2z, Hzs2.
  now apply (rngl_lt_asymm Hor) in Hs2z.
}
destruct zs1. {
  destruct s2z; [ easy | ].
  apply (rngl_leb_gt Hor) in Hs2z, Hzs2.
  now apply (rngl_lt_asymm Hor) in Hs2z.
}
destruct s2z; [ easy | ].
apply (rngl_leb_gt Hor) in Hs2z, Hzs2.
now apply (rngl_lt_asymm Hor) in Hs2z.
Qed.

Theorem angle_lt_le_incl :
  ∀ θ1 θ2, (θ1 < θ2 → θ1 ≤ θ2)%A.
Proof.
specialize ac_or as Hor.
intros * H12.
progress unfold angle_ltb in H12.
progress unfold angle_leb.
remember (0 ≤? rngl_sin θ1)%L as z1 eqn:Hz1.
remember (0 ≤? rngl_sin θ2)%L as z2 eqn:Hz2.
symmetry in Hz1, Hz2.
destruct z1. {
  destruct z2; [ | easy ].
  apply rngl_ltb_lt in H12.
  apply rngl_leb_le.
  now apply (rngl_lt_le_incl Hor).
} {
  destruct z2; [ easy | ].
  apply rngl_ltb_lt in H12.
  apply rngl_leb_le.
  now apply (rngl_lt_le_incl Hor).
}
Qed.

Theorem angle_lt_le_trans :
  ∀ θ1 θ2 θ3,
  (θ1 < θ2 → θ2 ≤ θ3 → θ1 < θ3)%A.
Proof.
destruct_ac.
intros * H12 H23.
progress unfold angle_ltb in H12.
progress unfold angle_leb in H23.
progress unfold angle_ltb.
remember (0 ≤? rngl_sin θ1)%L as z1 eqn:Hz1.
remember (0 ≤? rngl_sin θ2)%L as z2 eqn:Hz2.
remember (0 ≤? rngl_sin θ3)%L as z3 eqn:Hz3.
symmetry in Hz1, Hz2, Hz3.
destruct z1. {
  apply rngl_leb_le in Hz1.
  destruct z3; [ | easy ].
  apply rngl_ltb_lt.
  apply rngl_leb_le in Hz3.
  destruct z2; [ | easy ].
  apply rngl_leb_le in Hz2, H23.
  apply rngl_ltb_lt in H12.
  now apply (rngl_le_lt_trans Hor _ (rngl_cos θ2)).
} {
  destruct z2; [ easy | ].
  destruct z3; [ easy | ].
  apply rngl_ltb_lt in H12.
  apply rngl_leb_le in H23.
  apply rngl_ltb_lt.
  now apply (rngl_lt_le_trans Hor _ (rngl_cos θ2)).
}
Qed.

Theorem angle_le_lt_trans :
  ∀ θ1 θ2 θ3,
  (θ1 ≤ θ2 → θ2 < θ3 → θ1 < θ3)%A.
Proof.
intros * H12 H23.
apply angle_lt_iff.
split. {
  apply (angle_le_trans _ θ2); [ easy | ].
  now apply angle_lt_le_incl in H23.
}
intros H; subst θ3.
now apply angle_nle_gt in H23.
Qed.

Theorem angle_lt_trans : ∀ θ1 θ2 θ3, (θ1 < θ2 → θ2 < θ3 → θ1 < θ3)%A.
Proof.
intros * H12 H23.
apply (angle_le_lt_trans _ θ2); [ | easy ].
now apply angle_lt_le_incl in H12.
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
  apply (rngl_leb_gt Hor) in Hzs1, Hzs2.
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
  apply (rngl_leb_gt Hor) in Hzs2.
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
apply (rngl_leb_gt Hor) in Hs2z.
destruct zs2. 2: {
  apply (rngl_leb_gt Hor) in Hzs2.
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
specialize (rngl_int_dom_or_inv_1_quo Hiv Hon) as Hii.
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
specialize (rngl_int_dom_or_inv_1_quo Hiv Hon) as Hii.
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
specialize (rngl_int_dom_or_inv_1_quo Hiv Hon) as Hii.
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
  ∀ θ, rngl_cos (2 * θ) = ((rngl_cos θ)² - (rngl_sin θ)²)%L.
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
  → angle_straight ≠ 0%A.
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

End a.
