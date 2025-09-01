Set Nested Proofs Allowed.
From Stdlib Require Import Utf8 Arith.

Require Import RingLike.Core.
Require Import RingLike.RealLike.
Require Import RingLike.Misc.
Require Import Angle TrigoWithoutPiExt.

Section a.

Context {T : Type}.
Context {ro : ring_like_op T}.
Context {rp : ring_like_prop T}.
Context {rl : real_like_prop T}.
Context {ac : angle_ctx T}.

Theorem rngl_cos_diff_le_eucl_dist :
  ∀ θ1 θ2, (rngl_cos θ1 - rngl_cos θ2 ≤ angle_eucl_dist θ1 θ2)%L.
Proof.
destruct_ac.
specialize (rngl_int_dom_or_inv_1_quo Hiv Hon) as Hii.
intros.
destruct (rngl_le_dec Hor (rngl_cos θ1) (rngl_cos θ2)) as [Hc12| Hc12]. {
  apply (rngl_le_trans Hor _ 0); [ now apply (rngl_le_sub_0 Hop Hor) | ].
  apply angle_eucl_dist_nonneg.
}
apply (rngl_nle_gt_iff Hor) in Hc12.
rewrite angle_eucl_dist_is_sqrt.
rewrite <- (rngl_abs_nonneg_eq  Hop Hor (_ - _)). 2: {
  apply (rngl_le_0_sub Hop Hor).
  now apply (rngl_lt_le_incl Hor) in Hc12.
}
rewrite <- (rl_sqrt_squ Hon Hop Hor).
apply (rl_sqrt_le_rl_sqrt Hon Hop Hor Hii). {
  apply (rngl_squ_nonneg Hon Hos Hiq Hor).
}
rewrite (rngl_squ_sub Hop Hic Hon).
rewrite (rngl_mul_sub_distr_l Hop).
rewrite (rngl_mul_1_r Hon).
rewrite rngl_cos_sub.
rewrite rngl_mul_add_distr_l.
rewrite (rngl_sub_add_distr Hos).
do 2 rewrite rngl_mul_assoc.
rewrite <- (rngl_add_sub_swap Hop).
rewrite (rngl_sub_sub_swap Hop).
rewrite (rngl_mul_mul_swap Hic).
apply (rngl_sub_le_mono_r Hop Hor).
specialize (cos2_sin2_1 θ1) as H1.
specialize (cos2_sin2_1 θ2) as H2.
apply (rngl_add_move_r Hop) in H1, H2.
rewrite H1, H2; clear H1 H2.
rewrite (rngl_add_sub_assoc Hop).
rewrite <- (rngl_add_sub_swap Hop).
rewrite <- (rngl_sub_add_distr Hos).
apply (rngl_sub_le_mono_l Hop Hor).
apply (rngl_le_0_sub Hop Hor).
rewrite (rngl_mul_mul_swap Hic).
rewrite (rngl_add_sub_swap Hop).
rewrite <- (rngl_squ_sub Hop Hic Hon).
apply (rngl_squ_nonneg Hon Hos Hiq Hor).
Qed.

Theorem rngl_sin_diff_le_eucl_dist :
  ∀ θ1 θ2, (rngl_sin θ1 - rngl_sin θ2 ≤ angle_eucl_dist θ1 θ2)%L.
Proof.
destruct_ac.
intros.
rewrite <- (rngl_cos_sub_right_l θ1).
rewrite <- (rngl_cos_sub_right_l θ2).
eapply (rngl_le_trans Hor); [ apply rngl_cos_diff_le_eucl_dist | ].
rewrite angle_eucl_dist_move_0_l.
rewrite angle_sub_sub_swap.
rewrite angle_sub_sub_distr.
rewrite angle_sub_diag.
rewrite angle_add_0_l.
rewrite <- angle_eucl_dist_move_0_r.
apply (rngl_le_refl Hor).
Qed.

Definition angle_eucl_distance :=
  {| d_dist := angle_eucl_dist; d_prop := angle_eucl_dist_is_dist |}.

Theorem rngl_is_Cauchy_angle_is_Cauchy_cos :
  ∀ θ,
  is_Cauchy_sequence angle_eucl_dist θ
  → is_Cauchy_sequence rngl_dist (λ i, rngl_cos (θ i)).
Proof.
destruct_ac.
intros * Hcs.
intros ε Hε.
specialize (Hcs ε Hε).
destruct Hcs as (N, HN).
exists N.
intros * Hp Hq.
cbn.
progress unfold rngl_dist.
destruct (rngl_le_dec Hor (rngl_cos (θ q)) (rngl_cos (θ p))) as [Hpq| Hpq]. {
  rewrite (rngl_abs_nonneg_eq Hop Hor). 2: {
    now apply (rngl_le_0_sub Hop Hor).
  }
  eapply (rngl_le_lt_trans Hor); [ | apply (HN p q Hp Hq) ].
  apply rngl_cos_diff_le_eucl_dist.
} {
  apply (rngl_nle_gt_iff Hor), (rngl_lt_le_incl Hor) in Hpq.
  rewrite (rngl_abs_sub_comm Hop Hor).
  rewrite (rngl_abs_nonneg_eq Hop Hor). 2: {
    now apply (rngl_le_0_sub Hop Hor).
  }
  eapply (rngl_le_lt_trans Hor); [ | apply (HN q p Hq Hp) ].
  apply rngl_cos_diff_le_eucl_dist.
}
Qed.

Theorem rngl_is_Cauchy_angle_is_Cauchy_sin :
  ∀ θ,
  is_Cauchy_sequence angle_eucl_dist θ
  → is_Cauchy_sequence rngl_dist (λ i, rngl_sin (θ i)).
Proof.
destruct_ac.
intros * Hcs.
intros ε Hε.
specialize (Hcs ε Hε).
destruct Hcs as (N, HN).
exists N.
intros * Hp Hq.
cbn.
progress unfold rngl_dist.
destruct (rngl_le_dec Hor (rngl_sin (θ q)) (rngl_sin (θ p))) as [Hpq| Hpq]. {
  rewrite (rngl_abs_nonneg_eq Hop Hor). 2: {
    now apply (rngl_le_0_sub Hop Hor).
  }
  eapply (rngl_le_lt_trans Hor); [ | apply (HN p q Hp Hq) ].
  apply rngl_sin_diff_le_eucl_dist.
} {
  apply (rngl_nle_gt_iff Hor), (rngl_lt_le_incl Hor) in Hpq.
  rewrite (rngl_abs_sub_comm Hop Hor).
  rewrite (rngl_abs_nonneg_eq Hop Hor). 2: {
    now apply (rngl_le_0_sub Hop Hor).
  }
  eapply (rngl_le_lt_trans Hor); [ | apply (HN q p Hq Hp) ].
  apply rngl_sin_diff_le_eucl_dist.
}
Qed.

(* to be moved somewhere else *)
Theorem rngl_dist_to_limit_bounded :
  rngl_has_1 T = true →
  rngl_has_opp T = true →
  rngl_is_ordered T = true →
  rngl_characteristic T ≠ 1 →
  ∀ u l,
  is_limit_when_seq_tends_to_inf rngl_dist u l
  → ∃ N, ∀ n, N ≤ n → (rngl_dist (u n) l < 1)%L.
Proof.
intros Hon Hop Hor Hc1.
specialize (rngl_has_opp_has_opp_or_subt Hop) as Hos.
intros * Hlim.
specialize (Hlim 1)%L.
specialize (rngl_0_lt_1 Hon Hos Hiq Hc1 Hor) as H.
now apply Hlim.
Qed.

Theorem rngl_converging_seq_bounded :
  rngl_has_1 T = true →
  rngl_has_opp T = true →
  rngl_is_ordered T = true →
  rngl_characteristic T ≠ 1 →
  ∀ u l,
  is_limit_when_seq_tends_to_inf rngl_dist u l
  → ∃ N, ∀ n, N ≤ n → (rngl_abs (u n) < rngl_abs l + 1)%L.
Proof.
intros Hon Hop Hor Hc1.
specialize (rngl_has_opp_has_opp_or_subt Hop) as Hos.
intros * Hlim.
apply (rngl_dist_to_limit_bounded Hon Hop Hor Hc1) in Hlim.
destruct Hlim as (N, HN).
exists N.
intros n Hn.
specialize (HN n Hn).
progress unfold rngl_dist in HN.
eapply (rngl_le_lt_trans Hor). 2: {
  apply (rngl_add_lt_mono_l Hos Hor), HN.
}
eapply (rngl_le_trans Hor); [ | apply (rngl_abs_triangle Hop Hor) ].
rewrite rngl_add_comm, (rngl_sub_add Hop).
apply (rngl_le_refl Hor).
Qed.

Theorem rngl_converging_seq_add_limit_bounded :
  rngl_has_1 T = true →
  rngl_has_opp T = true →
  rngl_is_ordered T = true →
  rngl_characteristic T ≠ 1 →
  ∀ u k,
  is_limit_when_seq_tends_to_inf rngl_dist u k
  → ∃ N, ∀ n, N ≤ n → (rngl_abs (u n + k) < 2 * rngl_abs k + 1)%L.
Proof.
intros Hon Hop Hor Hc1.
specialize (rngl_has_opp_has_opp_or_subt Hop) as Hos.
intros * Hlim.
apply (rngl_converging_seq_bounded Hon Hop Hor Hc1) in Hlim.
destruct Hlim as (N, HN).
exists N.
intros n Hn.
specialize (HN n Hn).
rewrite (rngl_mul_2_l Hon).
rewrite <- rngl_add_assoc.
eapply (rngl_le_lt_trans Hor). 2: {
  apply (rngl_add_lt_mono_l Hos Hor), HN.
}
rewrite rngl_add_comm.
apply (rngl_abs_triangle Hop Hor).
Qed.

Theorem rngl_limit_limit_squ :
  rngl_has_1 T = true →
  rngl_has_opp T = true →
  rngl_mul_is_comm T = true →
  rngl_has_inv T = true →
  rngl_is_ordered T = true →
  ∀ u l,
  is_limit_when_seq_tends_to_inf rngl_dist u l
  → is_limit_when_seq_tends_to_inf rngl_dist (λ i, (u i)²)%L l²%L.
Proof.
intros Hon Hop Hic Hiv Hor.
specialize (rngl_has_opp_has_opp_or_subt Hop) as Hos.
specialize (rngl_int_dom_or_inv_1_quo Hiv Hon) as Hii.
specialize (rngl_has_inv_and_1_has_inv_and_1_or_quot Hon Hiv) as Hi1.
destruct (Nat.eq_dec (rngl_characteristic T) 1) as [Hc1| Hc1]. {
  specialize (rngl_characteristic_1 Hon Hos Hc1) as H1.
  intros * Hu.
  intros ε Hε.
  rewrite (H1 ε) in Hε.
  now apply (rngl_lt_irrefl Hor) in Hε.
}
intros * Hu.
specialize (rngl_converging_seq_add_limit_bounded Hon Hop Hor Hc1) as H2.
specialize (H2 _ _ Hu).
intros ε Hε.
specialize (Hu (ε / (2 * rngl_abs l + 1)))%L.
assert (H : (0 < ε / (2 * rngl_abs l + 1))%L). {
  apply (rngl_lt_div_r Hon Hop Hiv Hor); [ | now rewrite (rngl_mul_0_l Hos) ].
  apply (rngl_lt_le_trans Hor _ 1). {
    apply (rngl_0_lt_1 Hon Hos Hiq Hc1 Hor).
  }
  apply (rngl_le_add_l Hos Hor).
  apply (rngl_mul_nonneg_nonneg Hon Hos Hiq Hor).
  apply (rngl_0_le_2 Hon Hos Hor).
  apply (rngl_abs_nonneg Hop Hor).
}
specialize (Hu H); clear H.
cbn in Hu.
progress unfold rngl_dist in Hu.
destruct Hu as (N1, HN1).
destruct H2 as (N2, HN2).
exists (max N1 N2).
intros n Hn.
assert (H : N1 ≤ n). {
  eapply Nat.le_trans; [ | apply Hn ].
  apply Nat.le_max_l.
}
specialize (HN1 _ H); clear H.
assert (H : N2 ≤ n). {
  eapply Nat.le_trans; [ | apply Hn ].
  apply Nat.le_max_r.
}
specialize (HN2 _ H); clear H.
cbn.
progress unfold rngl_dist.
rewrite (rngl_squ_sub_squ Hop).
rewrite (rngl_mul_comm Hic (u n)).
rewrite (rngl_add_sub Hos).
rewrite (rngl_abs_mul Hop Hi1 Hor).
eapply (rngl_le_lt_trans Hor). {
  apply (rngl_mul_le_mono_nonneg_l Hop Hor). {
    apply (rngl_abs_nonneg Hop Hor).
  }
  apply (rngl_lt_le_incl Hor) in HN1.
  apply HN1.
}
rewrite (rngl_mul_div_assoc Hiv).
apply (rngl_lt_div_l Hon Hop Hiv Hor). {
  apply (rngl_lt_le_trans Hor _ 1). {
    apply (rngl_0_lt_1 Hon Hos Hiq Hc1 Hor).
  }
  apply (rngl_le_add_l Hos Hor).
  apply (rngl_mul_nonneg_nonneg Hon Hos Hiq Hor).
  apply (rngl_0_le_2 Hon Hos Hor).
  apply (rngl_abs_nonneg Hop Hor).
}
rewrite (rngl_mul_comm Hic).
now apply (rngl_mul_lt_mono_pos_l Hop Hor Hii).
Qed.

Theorem is_limit_when_seq_tends_to_inf_eq_compat :
  ∀ A (da : A → A → T) a b f g z,
  (∀ i, f (i + a) = g (i + b))
  → is_limit_when_seq_tends_to_inf da f z
  → is_limit_when_seq_tends_to_inf da g z.
Proof.
intros * Hfg Hf.
intros ε Hε.
specialize (Hf ε Hε).
destruct Hf as (N, HN).
exists (N + max a b).
intros n Hn.
specialize (HN (n - b + a)).
assert (H : N ≤ n - b + a) by flia Hn.
specialize (HN H).
rewrite Hfg in HN.
rewrite Nat.sub_add in HN; [ easy | flia Hn ].
Qed.

Theorem limit_cos_cos_sin_sin :
  ∀ u θ,
  is_limit_when_seq_tends_to_inf rngl_dist
    (λ i, rngl_cos (u i)) (rngl_cos θ)
  → is_limit_when_seq_tends_to_inf rngl_dist
      (λ i, rngl_sin (u i)) (rngl_sin θ)
  → is_limit_when_seq_tends_to_inf angle_eucl_dist u θ.
Proof.
destruct_ac.
specialize (rngl_int_dom_or_inv_1_quo Hiv Hon) as Hii.
specialize (rngl_has_inv_and_1_has_inv_and_1_or_quot Hon Hiv) as Hi1.
destruct (Nat.eq_dec (rngl_characteristic T) 1) as [Hc1| Hc1]. {
  specialize (rngl_characteristic_1 Hon Hos Hc1) as H1.
  intros * Hc Hs ε Hε.
  rewrite H1 in Hε.
  now apply (rngl_lt_irrefl Hor) in Hε.
}
intros * Hc Hs.
intros ε Hε.
assert (H : (0 < √(ε² / 2))%L). {
  apply (rl_sqrt_pos Hon Hos Hor).
  apply (rngl_lt_div_r Hon Hop Hiv Hor).
  apply (rngl_0_lt_2 Hon Hos Hiq Hc1 Hor).
  rewrite (rngl_mul_0_l Hos).
  progress unfold rngl_squ.
  now apply (rngl_mul_pos_pos Hos Hor Hii).
}
specialize (Hc _ H).
specialize (Hs _ H).
clear H.
destruct Hc as (nc, Hnc).
destruct Hs as (ns, Hns).
move ns before nc.
exists (Nat.max nc ns).
intros n Hn.
cbn.
progress unfold angle_eucl_dist.
specialize (Hnc n).
assert (H : nc ≤ n). {
  apply (Nat.le_trans _ (Nat.max nc ns)); [ | easy ].
  apply Nat.le_max_l.
}
specialize (Hnc H); clear H.
specialize (Hns n).
assert (H : ns ≤ n). {
  apply (Nat.le_trans _ (Nat.max nc ns)); [ | easy ].
  apply Nat.le_max_r.
}
specialize (Hns H); clear H.
cbn in Hnc, Hns.
progress unfold rngl_dist in Hnc.
progress unfold rngl_dist in Hns.
assert (H : (0 ≤ ε² / 2)%L). {
  apply (rngl_div_nonneg Hon Hop Hiv Hor).
  apply (rngl_squ_nonneg Hon Hos Hiq Hor).
  apply (rngl_0_lt_2 Hon Hos Hiq Hc1 Hor).
}
rewrite <- (rngl_abs_sqrt Hop Hor) in Hnc; [ | easy ].
rewrite <- (rngl_abs_sqrt Hop Hor) in Hns; [ | easy ].
apply (rngl_abs_lt_squ_lt Hop Hor Hii) in Hnc, Hns; cycle 1. {
  apply (rngl_mul_comm Hic).
} {
  apply (rngl_mul_comm Hic).
}
rewrite (rngl_squ_sqrt Hon _ H) in Hnc, Hns.
clear H.
generalize Hε; intros H.
apply (rngl_lt_le_incl Hor) in H.
rewrite <- (rngl_abs_nonneg_eq Hop Hor ε H).
rewrite <- (rl_sqrt_squ Hon Hop Hor ε).
apply (rl_sqrt_lt_rl_sqrt Hon Hor). {
  apply (rngl_add_squ_nonneg Hos Hor).
}
rewrite <- (rngl_mul_div Hi1 ε² 2)%L.
rewrite (rngl_mul_2_r Hon ε²)%L. 2: {
  apply (rngl_2_neq_0 Hon Hos Hiq Hc1 Hor).
}
rewrite (rngl_div_add_distr_r Hiv).
rewrite (rngl_squ_sub_comm Hop (rngl_cos _))%L.
rewrite (rngl_squ_sub_comm Hop (rngl_sin _))%L.
now apply (rngl_add_lt_compat Hos Hor).
Qed.

Theorem limit_const :
  rngl_has_opp T = true →
  rngl_is_ordered T = true →
  ∀ c lim,
  is_limit_when_seq_tends_to_inf rngl_dist (λ _, c) lim
  → lim = c.
Proof.
intros Hop Hor * Hlim.
destruct (rngl_lt_dec Hor lim c) as [Hlc| Hcl]. {
  exfalso.
  specialize (Hlim (c - lim)%L).
  apply (rngl_lt_0_sub Hop Hor) in Hlc.
  specialize (Hlim Hlc).
  destruct Hlim as (N, HN).
  specialize (HN N (Nat.le_refl _)).
  cbn in HN.
  progress unfold rngl_dist in HN.
  apply (rngl_lt_le_incl Hor) in Hlc.
  rewrite (rngl_abs_nonneg_eq Hop Hor) in HN; [ | easy ].
  now apply (rngl_lt_irrefl Hor) in HN.
}
apply (rngl_nlt_ge_iff Hor) in Hcl.
destruct (rngl_lt_dec Hor c lim) as [Hlc| Hlc]. {
  exfalso.
  specialize (Hlim (lim - c)%L).
  generalize Hlc; intros H.
  apply (rngl_lt_0_sub Hop Hor) in H.
  specialize (Hlim H); clear H.
  destruct Hlim as (N, HN).
  specialize (HN N (Nat.le_refl _)).
  cbn in HN.
  progress unfold rngl_dist in HN.
  apply (rngl_le_sub_0 Hop Hor) in Hcl.
  rewrite (rngl_abs_nonpos_eq Hop Hor) in HN; [ | easy ].
  rewrite (rngl_opp_sub_distr Hop) in HN.
  now apply (rngl_lt_irrefl Hor) in HN.
}
apply (rngl_nlt_ge_iff Hor) in Hlc.
apply (rngl_le_antisymm Hor _ _ Hlc Hcl).
Qed.

Theorem rngl_is_complete_angle_is_complete :
  is_complete T rngl_dist
  → is_complete (angle T) angle_eucl_dist.
Proof.
destruct_ac.
specialize (rngl_int_dom_or_inv_1_quo Hiv Hon) as Hii.
specialize (rngl_has_inv_and_1_has_inv_and_1_or_quot Hon Hiv) as Hi1.
specialize (rngl_int_dom_or_inv_1_quo_and_eq_dec Hi1 Hed) as Hid.
destruct (Nat.eq_dec (rngl_characteristic T) 1) as [Hc1| Hc1]. {
  specialize (rngl_characteristic_1 Hon Hos Hc1) as H1.
  intros Hco u Hu.
  exists 0%A.
  intros ε Hε.
  rewrite (H1 ε) in Hε.
  now apply (rngl_lt_irrefl Hor) in Hε.
}
intros Hco.
progress unfold is_complete in Hco.
progress unfold is_complete.
intros u Hcs.
specialize (Hco (λ i, rngl_cos (u i))) as H1.
specialize (Hco (λ i, rngl_sin (u i))) as H2.
generalize Hcs; intros H.
apply rngl_is_Cauchy_angle_is_Cauchy_cos in H.
specialize (H1 H); clear H.
destruct H1 as (c, Hc).
generalize Hcs; intros H.
apply rngl_is_Cauchy_angle_is_Cauchy_sin in H.
specialize (H2 H); clear H.
destruct H2 as (s, Hs).
move s before c.
generalize Hc; intros Hci.
specialize (rngl_limit_interv Hon Hop Hiv Hor (rngl_dist_is_dist Hop Hor))
  as H1.
specialize (rngl_dist_left_mono Hop Hor) as H.
specialize (H1 H); clear H.
specialize (rngl_dist_right_mono Hop Hor) as H.
specialize (H1 H); clear H.
apply H1 with (a := (-1)%L) (b := 1%L) in Hci. 2: {
  intros; apply rngl_cos_bound.
}
generalize Hs; intros Hsi.
apply H1 with (a := (-1)%L) (b := 1%L) in Hsi. 2: {
  intros; apply rngl_sin_bound.
}
clear H1.
assert (Hcs1 : (c² + s² = 1)%L). {
  generalize Hc; intros H1.
  generalize Hs; intros H2.
  apply (rngl_limit_limit_squ Hon Hop Hic Hiv Hor) in H1.
  apply (rngl_limit_limit_squ Hon Hop Hic Hiv Hor) in H2.
  specialize (limit_add Hon Hop Hiv Hor (rngl_dist_is_dist Hop Hor)) as H.
  specialize (H (rngl_dist_add_add_le Hop Hor)).
  specialize (H _ _ _ _ H1 H2).
  cbn in H.
  eapply (is_limit_when_seq_tends_to_inf_eq_compat _ _ 0 0) in H. 2: {
    intros i.
    rewrite Nat.add_0_r.
    now rewrite cos2_sin2_1.
  }
  now apply (limit_const Hop Hor) in H.
}
rewrite <- (rngl_cos_acos c) in Hc; [ | easy ].
remember (rngl_acos c) as θ eqn:Hθ.
assert (Hts : s = rngl_sin θ ∨ s = (- rngl_sin θ)%L). {
  rewrite Hθ.
  rewrite rngl_sin_acos; [ | easy ].
  destruct (rngl_le_dec Hor 0 s) as [Hzs| Hzs]; [ left | right ]. {
    rewrite <- (rngl_abs_sqrt Hop Hor). 2: {
      apply (rngl_le_0_sub Hop Hor).
      now apply (rngl_squ_le_1 Hon Hop Hor).
    }
    rewrite <- (rngl_abs_nonneg_eq Hop Hor s Hzs).
    apply (eq_rngl_squ_rngl_abs Hop Hor Hii); [ apply (rngl_mul_comm Hic) | ].
    rewrite (rngl_squ_sqrt Hon). 2: {
      apply (rngl_le_0_sub Hop Hor).
      now apply (rngl_squ_le_1 Hon Hop Hor).
    }
    now apply (rngl_add_move_l Hop).
  } {
    apply (rngl_nle_gt_iff Hor) in Hzs.
    remember (- s)%L as s' eqn:H.
    apply (f_equal rngl_opp) in H.
    rewrite (rngl_opp_involutive Hop) in H.
    subst s; rename s' into s.
    rewrite (rngl_squ_opp Hop) in Hcs1.
    apply (rngl_opp_neg_pos Hop Hor) in Hzs.
    f_equal.
    rewrite <- (rngl_abs_sqrt Hop Hor). 2: {
      apply (rngl_le_0_sub Hop Hor).
      now apply (rngl_squ_le_1 Hon Hop Hor).
    }
    apply (rngl_lt_le_incl Hor) in Hzs.
    rewrite <- (rngl_abs_nonneg_eq Hop Hor s Hzs).
    apply (eq_rngl_squ_rngl_abs Hop Hor Hii); [ apply (rngl_mul_comm Hic) | ].
    rewrite (rngl_squ_sqrt Hon). 2: {
      apply (rngl_le_0_sub Hop Hor).
      now apply (rngl_squ_le_1 Hon Hop Hor).
    }
    now apply (rngl_add_move_l Hop).
  }
}
apply (f_equal rngl_cos) in Hθ.
rewrite (rngl_cos_acos _ Hci) in Hθ.
symmetry in Hθ; rename Hθ into Htc.
move Hts before Htc.
destruct Hts as [Hts| Hts]. {
  rewrite Hts in Hs.
  exists θ.
  now apply limit_cos_cos_sin_sin.
} {
  remember (- θ)%A as t eqn:Ht.
  apply (f_equal angle_opp) in Ht.
  rewrite angle_opp_involutive in Ht.
  subst θ; rename t into θ.
  rewrite rngl_cos_opp in Htc, Hc.
  rewrite rngl_sin_opp in Hts.
  rewrite Hts in Hs.
  rewrite (rngl_opp_involutive Hop) in Hts, Hs.
  exists θ.
  now apply limit_cos_cos_sin_sin.
}
Qed.

End a.
