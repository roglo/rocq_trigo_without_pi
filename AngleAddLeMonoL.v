(* just a file for this theorem:
     (θ2 ≤ θ3)%A → (θ1 + θ2 ≤ θ1 + θ3)%A
 *)

Set Nested Proofs Allowed.
From Stdlib Require Import Utf8 Arith.

Require Import RingLike.Core.
Require Import AngleDef TrigoWithoutPiExt.
Require Import AngleAddOverflowLe.
Require Import Angle_order.
Require Import TacChangeAngle.
Require Import AngleAddLeMonoL_sin_lb_nonneg.
Require Import AngleAddLeMonoL_sin_lb_neg_sin_2_nonneg.
Require Import AngleAddLeMonoL_sin_lb_neg_sin_2_neg.
Require Export AngleAddLeMonoL_prop.

Section a.

Context {T : Type}.
Context {ro : ring_like_op T}.
Context {rp : ring_like_prop T}.
Context {ac : angle_ctx T}.

Theorem angle_add_le_mono_l :
  ∀ θ1 θ2 θ3,
  angle_add_overflow θ1 θ3 = false
  → (θ2 ≤ θ3)%A
  → (θ1 + θ2 ≤ θ1 + θ3)%A.
Proof.
destruct_ac.
intros * Haov13 H23.
destruct (rngl_le_dec Hor 0 (rngl_sin (θ1 + θ2))) as [Hzs12| Hzs12]. {
  now apply angle_add_le_mono_l_sin_lb_nonneg.
}
apply (rngl_nle_gt_iff Hor) in Hzs12.
destruct (rngl_le_dec Hor 0 (rngl_sin θ2)) as [Hzs2| Hzs2]. {
  now apply angle_add_le_mono_l_sin_lb_neg_sin_2_nonneg.
} {
  apply (rngl_nle_gt_iff Hor) in Hzs2.
  now apply angle_add_le_mono_l_sin_lb_neg_sin_2_neg.
}
Qed.

Theorem angle_mul_le_mono_l :
  ∀ θ1 θ2,
  (θ1 ≤ θ2)%A
  → ∀ n,
  angle_mul_nat_overflow n θ2 = false
  → (n * θ1 ≤ n * θ2)%A.
Proof.
destruct_ac.
intros * H12 * Hn2.
revert θ1 θ2 H12 Hn2.
induction n; intros; [ apply angle_le_refl | cbn ].
apply angle_mul_nat_overflow_succ_l_false in Hn2.
destruct Hn2 as (Hn2, H2n2).
generalize Hn2; intros Hn12.
apply (IHn θ1) in Hn12; [ | easy ].
apply (angle_le_trans _ (θ1 + n * θ2))%A. {
  apply angle_add_le_mono_l; [ | easy ].
  rewrite angle_add_overflow_comm.
  apply (angle_add_overflow_le _ θ2)%A; [ easy | ].
  now rewrite angle_add_overflow_comm.
} {
  rewrite (angle_add_comm θ1).
  rewrite (angle_add_comm θ2).
  apply angle_add_le_mono_l; [ | easy ].
  now rewrite angle_add_overflow_comm.
}
Qed.

Theorem angle_mul_le_mono_r :
  ∀ a b θ, angle_mul_nat_overflow b θ = false → a ≤ b → (a * θ ≤ b * θ)%A.
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
apply (angle_mul_nat_overflow_succ_l_false θ b) in Hb.
destruct Hb as (H1, H2).
specialize (IHb H1 _ Hab).
now apply angle_add_le_mono_l.
Qed.

Theorem angle_mul_nat_not_overflow_le_l :
  ∀ m n,
  m ≤ n
  → ∀ θ, angle_mul_nat_overflow n θ = false
  → angle_mul_nat_overflow m θ = false.
Proof.
destruct_ac.
intros * Hmn * Hn.
revert θ m Hmn Hn.
induction n; intros. {
  now apply Nat.le_0_r in Hmn; subst m.
}
apply angle_mul_nat_overflow_succ_l_false in Hn.
destruct m; [ easy | ].
apply Nat.succ_le_mono in Hmn.
apply angle_mul_nat_overflow_succ_l_false.
split; [ now apply IHn | ].
apply (angle_add_overflow_le _ (n * θ)); [ | easy ].
now apply angle_mul_le_mono_r.
Qed.

Theorem angle_mul_nat_overflow_le_l :
  ∀ n θ,
  angle_mul_nat_overflow n θ = true
  → ∀ m, n ≤ m → angle_mul_nat_overflow m θ = true.
Proof.
destruct_ac.
intros * Hn * Hnm.
apply Bool.not_false_iff_true in Hn.
apply Bool.not_false_iff_true.
intros H; apply Hn.
now apply (angle_mul_nat_not_overflow_le_l _ m).
Qed.

Theorem angle_mul_nat_overflow_distr_add_overflow :
  ∀ m n θ,
  angle_mul_nat_overflow (m + n) θ = false
  → angle_add_overflow (m * θ) (n * θ) = false.
Proof.
destruct_ac.
intros * Hmov.
revert n Hmov.
induction m; intros; [ apply angle_add_overflow_0_l | ].
rewrite Nat.add_succ_l in Hmov.
rewrite angle_mul_nat_overflow_succ_l in Hmov.
apply Bool.orb_false_iff in Hmov.
destruct Hmov as (Hmov, Hov).
specialize (IHm _ Hmov) as Hov'.
cbn.
rewrite angle_add_overflow_comm.
apply angle_add_not_overflow_move_add. 2: {
  rewrite <- angle_mul_add_distr_r.
  rewrite Nat.add_comm.
  now rewrite angle_add_overflow_comm.
}
now rewrite angle_add_overflow_comm.
Qed.

Theorem angle_mul_nat_overflow_true_assoc :
  ∀ m n θ,
  angle_mul_nat_overflow m (n * θ) = true
  → angle_mul_nat_overflow (m * n) θ = true.
Proof.
intros * Hmn.
revert n θ Hmn.
induction m; intros; [ easy | ].
rewrite angle_mul_nat_overflow_succ_l in Hmn.
apply Bool.orb_true_iff in Hmn.
destruct Hmn as [Hmn| Hmn]. {
  apply (angle_mul_nat_overflow_le_l (m * n)); [ now apply IHm | ].
  apply Nat.le_add_l.
}
destruct n. {
  cbn in Hmn.
  now rewrite angle_add_overflow_0_l in Hmn.
}
apply Bool.not_false_iff_true in Hmn.
apply Bool.not_false_iff_true.
intros H1; apply Hmn; clear Hmn.
rewrite angle_mul_nat_assoc.
now apply angle_mul_nat_overflow_distr_add_overflow.
Qed.

Theorem angle_mul_nat_overflow_le_r :
  ∀ θ1 θ2,
  (θ1 ≤ θ2)%A
  → ∀ n,
  angle_mul_nat_overflow n θ2 = false
  → angle_mul_nat_overflow n θ1 = false.
Proof.
destruct_ac.
intros * H12 * H2.
revert θ1 θ2 H12 H2.
induction n; intros; [ easy | ].
generalize H2; intros H.
apply angle_mul_nat_overflow_succ_l_false in H.
destruct H as (Hn2, H2n2).
cbn.
destruct n; [ easy | ].
apply Bool.orb_false_iff.
split; [ | now apply (IHn _ θ2) ].
remember (S n) as m eqn:Hm.
clear n Hm; rename m into n.
clear H2 IHn.
rewrite angle_add_overflow_comm.
eapply angle_add_overflow_le; [ apply H12 | ].
rewrite angle_add_overflow_comm.
eapply angle_add_overflow_le; [ | apply H2n2 ].
now apply angle_mul_le_mono_l.
Qed.

Theorem angle_add_lt_mono_l :
  ∀ θ1 θ2 θ3,
  angle_add_overflow θ1 θ3 = false
  → (θ2 < θ3)%A → (θ1 + θ2 < θ1 + θ3)%A.
Proof.
intros * H13 H23.
apply angle_lt_iff.
split. {
  apply angle_add_le_mono_l; [ easy | ].
  now apply angle_lt_le_incl in H23.
}
intros H.
apply (f_equal (λ θ, (θ - θ1)%A)) in H.
do 2 rewrite angle_add_comm, angle_add_sub in H.
subst θ3.
now apply angle_lt_irrefl in H23.
Qed.

(*
End a.

Record angle_cnt T {ro : ring_like_op T} := mk_angle_cnt
  { rngl_angle : angle T;
    rngl_count : nat }.

Arguments rngl_angle {T ro} a%_A.
Arguments rngl_count {T ro} a%_A.
Arguments mk_angle_cnt {T ro} a%_A : rename.

Section a.

Context {T : Type}.
Context {ro : ring_like_op T}.
Context {rp : ring_like_prop T}.
Context {ac : angle_ctx T}.

Definition angle_cnt_add (θ1 θ2 : angle_cnt T) :=
  mk_angle_cnt (rngl_angle θ1 + rngl_angle θ2)
    (rngl_count θ1 + rngl_count θ2 +
     Nat.b2n (angle_add_overflow (rngl_angle θ1) (rngl_angle θ2))).
*)

(*

Require Import AngleAddOverflowEquiv.

Definition angle_add_overflow1 θ1 θ2 :=
  if (θ1 =? 0)%A then false
  else if (θ2 =? 0)%A then false
  else if (0 <? rngl_sin θ1)%L then
    if (0 <? rngl_sin θ2)%L then false
    else (rngl_cos θ1 ≤? rngl_cos θ2)%L
  else
    if (0 <? rngl_sin θ2)%L then (rngl_cos θ2 ≤? rngl_cos θ1)%L
    else true.

Require Import Angle.

Theorem angle_add_overflow_equiv1 :
  ∀ θ1 θ2, angle_add_overflow1 θ1 θ2 = angle_add_overflow θ1 θ2.
Proof.
destruct_ac.
intros.
progress unfold angle_add_overflow.
progress unfold angle_add_overflow1.
remember (θ1 =? 0)%A as t1z eqn:Ht1z.
remember (θ2 =? 0)%A as t2z eqn:Ht2z.
symmetry in Ht1z, Ht2z.
destruct t1z; [ easy | cbn ].
apply angle_eqb_neq in Ht1z.
destruct t2z. {
  apply angle_eqb_eq in Ht2z; subst θ2.
  symmetry.
  apply angle_leb_gt.
  apply angle_lt_iff.
  split; [ apply angle_nonneg | ].
  intros H; apply Ht1z; clear Ht1z.
  symmetry in H.
  apply (f_equal angle_opp) in H.
  rewrite angle_opp_involutive in H.
  now rewrite angle_opp_0 in H.
}
apply angle_eqb_neq in Ht2z.
progress unfold angle_leb.
cbn.
rewrite (rngl_leb_opp_r Hop Hor).
rewrite (rngl_opp_0 Hop).
remember (0 <? rngl_sin θ1)%L as zs1 eqn:Hzs1.
remember (rngl_sin θ1 ≤? 0)%L as s1z eqn:Hs1z.
symmetry in Hzs1, Hs1z.
remember (0 <? rngl_sin θ2)%L as zs2 eqn:Hzs2.
remember (0 ≤? rngl_sin θ2)%L as zse2 eqn:Hzse2.
symmetry in Hzs2, Hzse2.
destruct zs1. {
  apply rngl_ltb_lt in Hzs1.
  destruct s1z. {
    apply rngl_leb_le in Hs1z.
    now apply rngl_nlt_ge in Hs1z.
  }
  clear Hs1z.
  destruct zs2. {
    apply rngl_ltb_lt in Hzs2.
    destruct zse2; [ easy | ].
    apply (rngl_leb_gt Hor) in Hzse2.
    now apply (rngl_lt_asymm Hor) in Hzs2.
  }
  apply (rngl_ltb_ge_iff Hor) in Hzs2.
  destruct zse2; [ | easy ].
  apply rngl_leb_le in Hzse2.
  apply (rngl_le_antisymm Hor) in Hzse2; [ clear Hzs2 | easy ].
  apply eq_rngl_sin_0 in Hzse2.
  destruct Hzse2; [ easy | subst; cbn ].
  apply (rngl_leb_gt Hor).
  apply (rngl_le_neq Hor).
  split; [ apply rngl_cos_bound | ].
  intros H; symmetry in H.
  apply eq_rngl_cos_opp_1 in H; subst.
  now apply (rngl_lt_irrefl Hor) in Hzs1.
}
apply rngl_ltb_nlt in Hzs1.
destruct s1z; [ | now apply (rngl_leb_gt Hor) in Hs1z ].
apply rngl_leb_le in Hs1z.
destruct zs2. {
  destruct zse2; [ easy | ].
  apply rngl_ltb_lt in Hzs2.
  apply (rngl_leb_gt Hor) in Hzse2.
  now apply (rngl_lt_asymm Hor) in Hzs2.
}
symmetry.
destruct zse2; [ | easy ].
apply (rngl_ltb_ge_iff Hor) in Hzs2.
apply rngl_leb_le in Hzse2.
apply (rngl_le_antisymm Hor) in Hzse2; [ | easy ].
apply eq_rngl_sin_0 in Hzse2.
destruct Hzse2; [ easy | subst; cbn ].
apply rngl_leb_le, rngl_cos_bound.
Qed.

Theorem angle_add_overflow_assoc' :
  ∀ θ1 θ2 θ3,
  angle_add_overflow θ1 θ2 = angle_add_overflow θ2 θ3
  → angle_add_overflow (θ1 + θ2) θ3 = angle_add_overflow θ1 (θ2 + θ3).
Proof.
(**)
destruct_ac.
intros * H12.
remember (angle_add_overflow θ2 θ3) as ov eqn:H23.
symmetry in H23.
destruct ov. 2: {
  remember (angle_add_overflow (θ1 + θ2) θ3) as ov eqn:Hov.
  symmetry in Hov |-*.
  destruct ov; [ now apply angle_add_overflow_move_add | ].
  rewrite angle_add_comm.
  now apply angle_add_not_overflow_move_add.
}
(**)
rewrite <- angle_add_overflow_equiv2 in H12, H23.
do 2 rewrite <- angle_add_overflow_equiv2.
progress unfold angle_add_overflow2 in H12.
progress unfold angle_add_overflow2 in H23.
progress unfold angle_add_overflow2.
rewrite angle_add_assoc.
remember (θ1 + θ2 + θ3 <? θ1)%A as l123 eqn:H123.
symmetry in H123.
destruct l123. {
  progress unfold angle_ltb in H12.
  progress unfold angle_ltb in H23.
  progress unfold angle_ltb in H123.
  progress unfold angle_ltb.
  remember (0 ≤? rngl_sin (θ1 + θ2 + θ3))%L as z123 eqn:Hz123.
  symmetry in Hz123.
  destruct z123. {
    apply rngl_leb_le in Hz123.
    remember (0 ≤? rngl_sin (θ1 + θ2))%L as z12 eqn:Hz12.
    symmetry in Hz12.
    destruct z12. {
      apply rngl_leb_le in Hz12.
      remember (0 ≤? rngl_sin θ1)%L as zs1 eqn:Hzs1.
      symmetry in Hzs1.
      destruct zs1. {
        apply rngl_leb_le in Hzs1.
        apply rngl_ltb_lt in H12.
        apply rngl_ltb_lt in H123.
        apply rngl_ltb_lt.
        apply (rngl_nle_gt_iff Hor).
        intros Hc123.
        apply rngl_nle_gt in H12.
        apply H12; clear H12.
        remember (0 ≤? rngl_sin (θ2 + θ3))%L as zs23 eqn:Hzs23.
        remember (0 ≤? rngl_sin θ2)%L as zs2 eqn:Hzs2.
        symmetry in Hzs23, Hzs2.
        destruct zs23. {
          apply rngl_leb_le in Hzs23.
          destruct zs2. {
            apply rngl_leb_le in Hzs2.
            apply rngl_ltb_lt in H23.
            destruct (rngl_le_dec Hor 0 (rngl_cos θ1)) as [Hzc1| Hzc1]. {
              destruct (rngl_le_dec Hor 0 (rngl_cos θ2)) as [Hzc2| Hzc2]. {
                now apply quadrant_1_rngl_cos_add_le_cos_l.
              }
              apply (rngl_nle_gt_iff Hor) in Hzc2.
              apply rngl_cos_add_le_cos; [ | easy | easy | easy ].
              now right; right; left.
            }
            apply (rngl_nle_gt_iff Hor) in Hzc1.
            generalize Hzc1; intros H.
            apply (rngl_lt_le_incl Hor) in H.
            apply angle_add_overflow_le_lemma_2;
              [ | easy | easy | easy | easy ].
            clear H; intros H.
            apply eq_rngl_cos_opp_1 in H; subst θ1.
            rewrite rngl_sin_add_straight_l in Hz12.
            apply (rngl_opp_nonneg_nonpos Hop Hor) in Hz12.
            apply (rngl_le_antisymm Hor) in Hzs2; [ | easy ].
            clear Hzc1 Hzs1 Hz12.
            apply eq_rngl_sin_0 in Hzs2.
            destruct Hzs2; subst θ2. {
              apply rngl_nle_gt in H23.
              apply H23, rngl_cos_bound.
            }
            rewrite rngl_sin_add_straight_l in Hzs23.
            apply (rngl_opp_nonneg_nonpos Hop Hor) in Hzs23.
            rewrite rngl_cos_add_straight_l in H23.
            cbn in H23.
            rewrite angle_straight_add_straight in Hz123.
            rewrite angle_add_0_l in Hz123.
            apply (rngl_le_antisymm Hor) in Hz123; [ | easy ].
            clear Hzs23.
            apply eq_rngl_sin_0 in Hz123.
            destruct Hz123; subst θ3. {
              now apply (rngl_lt_irrefl Hor) in H23.
            }
            rewrite angle_straight_add_straight in H123.
            rewrite angle_add_0_l in H123.
            now apply (rngl_lt_irrefl Hor) in H123.
          }
          clear H23.
          apply (rngl_leb_gt Hor) in Hzs2.
          change_angle_sub_r θ2 angle_straight.
          rewrite angle_add_assoc in Hz12, Hc123, H123, Hz123 |-*.
          rewrite angle_add_add_swap in Hc123, H123, Hz123.
          progress sin_cos_add_sub_straight_hyp T Hz12.
          progress sin_cos_add_sub_straight_hyp T Hzs2.
          progress sin_cos_add_sub_straight_hyp T Hzs23.
          progress sin_cos_add_sub_straight_hyp T Hc123.
          progress sin_cos_add_sub_straight_hyp T H123.
          progress sin_cos_add_sub_straight_hyp T Hz123.
          progress sin_cos_add_sub_straight_goal T.
...
rewrite <- angle_add_overflow_equiv1 in H12, H23.
do 2 rewrite <- angle_add_overflow_equiv1.
progress unfold angle_add_overflow1 in H12.
progress unfold angle_add_overflow1 in H23.
progress unfold angle_add_overflow1.
remember (θ1 =? 0)%A as t1z eqn:Ht1z.
remember (θ2 =? 0)%A as t2z eqn:Ht2z.
remember (θ3 =? 0)%A as t3z eqn:Ht3z.
symmetry in Ht1z, Ht2z, Ht3z.
destruct t1z; [ easy | ].
destruct t2z; [ easy | ].
destruct t3z; [ easy | ].
move Ht1z after Ht2z.
remember (0 <? rngl_sin θ1)%L as zs1 eqn:Hzs1.
remember (0 <? rngl_sin θ2)%L as zs2 eqn:Hzs2.
remember (0 <? rngl_sin θ3)%L as zs3 eqn:Hzs3.
symmetry in Hzs1, Hzs2, Hzs3.
destruct zs1. {
  destruct zs2; [ easy | ].
  move Hzs1 after Hzs2.
  destruct zs3. {
    remember (θ1 + θ2 =? 0)%A as t12z eqn:Ht12z.
    remember (θ2 + θ3 =? 0)%A as t23z eqn:Ht23z.
    remember (0 <? rngl_sin (θ1 + θ2))%L as zs12 eqn:Hzs12.
    remember (0 <? rngl_sin (θ2 + θ3))%L as zs23 eqn:Hzs23.
    symmetry in Ht12z, Ht23z, Hzs12, Hzs23.
    destruct t12z. {
      destruct t23z; [ easy | ].
      destruct zs23; [ easy | symmetry ].
      apply angle_eqb_eq in Ht12z.
      apply angle_eqb_neq in Ht23z.
      apply angle_add_move_0_r in Ht12z; subst θ1.
      cbn in Hzs1.
      rewrite (rngl_ltb_opp_r Hop Hor) in Hzs1.
      rewrite (rngl_opp_0 Hop) in Hzs1.
clear Ht1z Hzs2 H12.
clear zs12 Hzs12.
rewrite rngl_cos_opp.
apply rngl_ltb_lt in Hzs1, Hzs3.
apply rngl_leb_le in H23.
apply (rngl_ltb_ge_iff Hor) in Hzs23.
apply (rngl_leb_gt Hor).
(*
apply rngl_nlt_ge in Hzs23.
apply (rngl_nle_gt_iff Hor).
intros H223; apply Hzs23; clear Hzs23.
*)
apply angle_eqb_neq in Ht2z, Ht3z.
change_angle_sub_r θ2 angle_straight.
progress sin_cos_add_sub_straight_hyp T Hzs1.
progress sin_cos_add_sub_straight_hyp T H23.
progress sin_cos_add_sub_straight_hyp T Ht23z.
progress sin_cos_add_sub_straight_hyp T Hzs23.
progress sin_cos_add_sub_straight_goal T.
rewrite (rngl_add_opp_r Hop).
apply (rngl_lt_0_sub Hop Hor).
Search (rngl_cos _ < rngl_cos (_ + _))%L.
...
      apply rngl_ltb_lt in Hzs1, Hzs2.
        now apply (rngl_lt_asymm Hor) in Hzs1.
      }
      destruct zs12. {
        destruct t23z; [ easy | ].
        destruct zs23; [ easy | symmetry ].
        apply (rngl_leb_gt Hor).
        apply rngl_ltb_lt in Hzs1, Hzs2, Hzs3.
...
        eapply (rngl_lt_trans Hor). {
          apply (rngl_lt_sub_l Hop Hor).
          now apply (rngl_mul_pos_pos Hon Hop Hiq Hor).
        }
...
        apply (rngl_le_lt_trans Hor _ (rngl_cos θ3)). {
...
          rewrite <- (rngl_mul_1_l Hon (rngl_cos θ3)) at 2.
Search (_ * _ ≤ _ * _)%L.
...
          apply (rngl_mul_le_mono_nonneg_r Hon Hop Hiq Hor).

Search (_ * _ ≤ _)%L.
...
          apply <- (rngl_mul_lt_mono_pos_r Hon Hop Hiq Hor 1%L).
          apply rngl
Search (rngl_cos (_ + _) < rngl_cos _)%L.
...
intros * H12.
remember (angle_add_overflow θ2 θ3) as ov eqn:H23.
symmetry in H23.
destruct ov. 2: {
  remember (angle_add_overflow (θ1 + θ2) θ3) as ov eqn:Hov.
  symmetry in Hov |-*.
  destruct ov; [ now apply angle_add_overflow_move_add | ].
  rewrite angle_add_comm.
  now apply angle_add_not_overflow_move_add.
} {
  destruct (angle_lt_dec θ2 angle_straight) as [H2s| H2s]. {
(**)
    change_angle_sub_r θ1 angle_straight.
    change_angle_sub_r θ3 angle_straight.
    move θ1 after θ2.
    do 2 rewrite <- angle_add_overflow_equiv2.
    progress unfold angle_add_overflow2.
    progress sin_cos_add_sub_right_goal T.
    do 2 rewrite (angle_add_add_swap _ angle_straight).
    rewrite <- angle_add_assoc.
    rewrite angle_straight_add_straight.
    rewrite angle_add_0_r.
    progress unfold angle_ltb.
    remember (0 ≤? rngl_sin (θ1 + θ2 + θ3))%L as z123 eqn:Hz123.
    symmetry in Hz123.
    destruct z123. {
      progress sin_cos_add_sub_straight_goal T.
...
    generalize H12; intros H1s.
    rewrite angle_add_overflow_comm in H1s.
    apply angle_add_overflow_lt_straight_ge_straight in H1s; [ | easy ].
    generalize H23; intros H3s.
    apply angle_add_overflow_lt_straight_ge_straight in H3s; [ | easy ].
    remember (θ1 - angle_straight)%A as θ.
    apply angle_add_move_r in Heqθ.
    subst θ1; rename θ into θ1; move θ1 after θ2.
    remember (θ3 - angle_straight)%A as θ.
    apply angle_add_move_r in Heqθ.
    subst θ3; rename θ into θ3; move θ3 before θ2.
...
  H23 : angle_add_overflow θ2 (θ3 + angle_straight) = true
  H12 : angle_add_overflow (θ1 + angle_straight) θ2 = true
  H2s : (θ2 < angle_straight)%A
  H1s : (angle_straight ≤ θ1 + angle_straight)%A
  H3s : (angle_straight ≤ θ3 + angle_straight)%A
  ============================
  angle_add_overflow (θ1 + angle_straight + θ2) (θ3 + angle_straight) =
  angle_add_overflow (θ1 + angle_straight) (θ2 + (θ3 + angle_straight))
...
Search (angle_straight ≤ _)%A.
Search (_ < angle_straight)%A.
Search (_ ≤ _ + _)%A.
Theorem glop : ∀ θ, (angle_straight ≤ θ + angle_straight)%A → (θ < angle_straight)%A.
...
    apply glop in H1s, H3s.
...
Search (angle_add_overflow _ (_ + _)).
rewrite angle_add_comm in H12.
apply angle_add_overflow_move_add in H12.
rewrite (angle_add_comm θ3).
rewrite <- angle_add_overflow_assoc.
...
  rewrite <- angle_add_overflow_equiv2 in H23, H12.
  progress unfold angle_add_overflow2 in H23, H12.
  remember (angle_add_overflow (θ1 + θ2) θ3) as ov eqn:Hov.
  symmetry in Hov |-*.
  destruct ov. {
    rewrite <- angle_add_overflow_equiv2 in Hov |-*.
    progress unfold angle_add_overflow2 in Hov |-*.
    progress unfold angle_ltb.
    remember (0 ≤? rngl_sin (θ1 + (θ2 + θ3)))%L as zs1 eqn:Hzs1.
    symmetry in Hzs1.
    destruct zs1. {
      remember (0 ≤? rngl_sin θ1)%L as zs2 eqn:Hzs2.
      symmetry in Hzs2.
      destruct zs2; [ | easy ].
      apply rngl_leb_le in Hzs1.
      apply rngl_leb_le in Hzs2.
      apply rngl_ltb_lt.
Search (rngl_cos _ < rngl_cos (_ + _))%L.
...
Search (_ + _ < _ + _)%A.
Search (_ + _ < _)%A.
...
do 2 rewrite <- angle_add_overflow_equiv2.
rewrite <- angle_add_assoc.
rewrite angle_add_lt_mono_l.
...
  remember (angle_add_overflow (θ1 + θ2) θ3) as ov eqn:Hov.
  symmetry in Hov |-*.
  destruct ov. {
...
Qed.
...
*)

End a.
