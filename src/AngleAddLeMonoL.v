(* just a file for this theorem:
     (α2 ≤ α3)%A → (α1 + α2 ≤ α1 + α3)%A
 *)

Set Nested Proofs Allowed.
Require Import Stdlib.Arith.Arith.
Require Import RingLike.Utf8.

Require Import RingLike.Core.
Require Import Angle AngleDef TrigoWithoutPiExt.
Require Import AngleAddOverflowLe.
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

(* to be completed
Theorem angle_sub_le_mono_l' :
  ∀ α1 α2 α3,
  (α1 ≤ α2 ≤ α3)%A
  → (α3 - α2 ≤ α3 - α1)%A.
Proof.
destruct_ac.
intros * (H12, H23).
progress unfold angle_leb.
remember (0 ≤? rngl_sin (α3 - α2))%L as s32 eqn:Hs32.
remember (0 ≤? rngl_sin (α3 - α1))%L as s31 eqn:Hs31.
symmetry in Hs32, Hs31.
destruct s32. {
  destruct s31; [ | easy ].
  apply rngl_leb_le in Hs32, Hs31.
  apply rngl_leb_le.
  progress unfold angle_leb in H12, H23.
  remember (0 ≤? rngl_sin α1)%L as zs1 eqn:Hzs1.
  remember (0 ≤? rngl_sin α2)%L as zs2 eqn:Hzs2.
  remember (0 ≤? rngl_sin α3)%L as zs3 eqn:Hzs3.
  symmetry in Hzs1, Hzs2, Hzs3.
  destruct zs1. {
    destruct zs2. {
      destruct zs3. {
        apply rngl_leb_le in Hzs1, Hzs2, H12, Hzs3, H23.
About rngl_sin_sub_nonneg_iff.
...
        apply rngl_sin_sub_nonneg_iff; [ | easy | ]. {
          (* lemma *)
          apply rngl_le_neq.
          split. {
            apply rngl_sin_sub_nonneg; [ easy | easy | ].
            now apply (rngl_le_trans Hor _ (rngl_cos α2)).
          }            
          intros H; symmetry in H.
          apply eq_rngl_sin_0 in H.
          destruct H as [H| H]. {
            apply -> angle_sub_move_0_r in H; subst α3.
            apply (rngl_le_antisymm Hor) in H12; [ | easy ].
            clear Hs31 H23 Hzs3.
... ...
        }
        rewrite angle_sub_sub_distr.
        rewrite angle_sub_sub_swap.
        rewrite angle_sub_diag, angle_sub_0_l.
        rewrite angle_add_opp_l.
        now apply rngl_sin_sub_nonneg.
...
Search (0 ≤ rngl_sin (_ - _))%L.
...
Search (rngl_cos _ ≤ rngl_cos (_ - _))%L.
Search (rngl_cos (_ - _) ≤ rngl_cos _)%L.
...
Search (rngl_cos (_ - _) ≤ rngl_cos (_ - _))%L.
...
*)

End a.
