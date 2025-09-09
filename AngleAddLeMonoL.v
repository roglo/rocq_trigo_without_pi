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
Require Import AngleAddOverflowEquiv.

Theorem angle_add_overflow_assoc' :
  ∀ θ1 θ2 θ3,
  angle_add_overflow θ1 θ2 = angle_add_overflow θ2 θ3
  → angle_add_overflow (θ1 + θ2) θ3 = angle_add_overflow θ1 (θ2 + θ3).
Proof.
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
