(** * Angles Without π

    In this approach, an angle is not a real number but a pair of real
    numbers (x, y) such that x² + y² = 1. The cosine is then x, and the
    sine is y.

    The identity sin² + cos² = 1 holds by definition. We can define angle
    addition (see below), and the usual formulas for cos(x + y) and
    sin(x + y) follow naturally.

    There is no need for the number π here; the angle π is simply (-1, 0).
*)

Set Nested Proofs Allowed.
From Stdlib Require Import Utf8 Arith.

Import List.ListNotations.
Require Import RingLike.Core.
Require Import RingLike.RealLike.
Require Import RingLike.Misc.

Section a.

Context {T : Type}.
Context {ro : ring_like_op T}.
Context {rp : ring_like_prop T}.
Context {rl : real_like_prop T}.

Definition cos2_sin2_prop x y := (x² + y² =? 1)%L = true.

Record angle := mk_angle
  { rngl_cos : T;
    rngl_sin : T;
    rngl_cos2_sin2 : cos2_sin2_prop rngl_cos rngl_sin }.

Class angle_ctx :=
  { ac_ic : rngl_mul_is_comm T = true;
    ac_on : rngl_has_1 T = true;
    ac_op : rngl_has_opp T = true;
    ac_ed : rngl_has_eq_dec T = true;
    ac_iv : rngl_has_inv T = true;
    ac_c2 : rngl_characteristic T ≠ 2;
    ac_or : rngl_is_ordered T = true }.

End a.

Arguments angle T {ro}.
Arguments mk_angle {T ro} (rngl_cos rngl_sin)%_L.
Arguments angle_ctx T {ro rp}.
Arguments cos2_sin2_prop {T ro} (x y)%_L.

Ltac destruct_ac :=
  set (Hic := ac_ic);
  set (Hop := ac_op);
  set (Hiv := ac_iv);
  set (Hed := ac_ed);
  set (Hor := ac_or);
  specialize (rngl_has_opp_has_opp_or_psub Hop) as Hos;
  specialize (rngl_has_inv_has_inv_or_pdiv Hiv) as Hiq;
  specialize ac_on as Hon;
  specialize ac_c2 as Hc2.

Section a.

Context {T : Type}.
Context {ro : ring_like_op T}.
Context {rp : ring_like_prop T}.
Context {rl : real_like_prop T}.
Context {ac : angle_ctx T}.

Theorem eq_angle_eq : ∀ θ1 θ2,
  (rngl_cos θ1, rngl_sin θ1) = (rngl_cos θ2, rngl_sin θ2) ↔ θ1 = θ2.
Proof.
intros.
split; intros Hab; [ | now subst θ2 ].
injection Hab; clear Hab; intros Hs Hc.
destruct θ1 as (aco, asi, Hacs).
destruct θ2 as (bco, bsi, Hbcs).
cbn in Hs, Hc.
subst bsi bco.
f_equal.
apply (Eqdep_dec.UIP_dec Bool.bool_dec).
Qed.

Theorem neq_angle_neq : ∀ θ1 θ2,
  (rngl_cos θ1, rngl_sin θ1) ≠ (rngl_cos θ2, rngl_sin θ2) ↔ θ1 ≠ θ2.
Proof.
intros.
split; intros Hab H; [ now subst θ2 | ].
now apply eq_angle_eq in H.
Qed.

Theorem angle_zero_prop : cos2_sin2_prop 1 0.
Proof.
destruct_ac.
progress unfold cos2_sin2_prop.
progress unfold rngl_squ.
rewrite (rngl_mul_1_l Hon).
rewrite (rngl_mul_0_l Hos).
rewrite rngl_add_0_r.
apply (rngl_eqb_refl Hed).
Qed.

Theorem angle_right_prop : cos2_sin2_prop 0 1.
Proof.
destruct_ac.
progress unfold cos2_sin2_prop.
rewrite (rngl_squ_0 Hos).
rewrite (rngl_squ_1 Hon).
rewrite rngl_add_0_l.
apply (rngl_eqb_refl Hed).
Qed.

Theorem angle_straight_prop : cos2_sin2_prop (-1) 0.
Proof.
destruct_ac.
progress unfold cos2_sin2_prop.
rewrite (rngl_squ_opp Hop).
progress unfold rngl_squ.
rewrite (rngl_mul_1_l Hon).
rewrite (rngl_mul_0_l Hos).
rewrite rngl_add_0_r.
apply (rngl_eqb_refl Hed).
Qed.

Theorem angle_add_prop :
  ∀ a b,
  cos2_sin2_prop
    (rngl_cos a * rngl_cos b - rngl_sin a * rngl_sin b)
    (rngl_sin a * rngl_cos b + rngl_cos a * rngl_sin b).
Proof.
destruct_ac.
intros.
rewrite (rngl_add_comm (rngl_sin a * _)%L).
destruct a as (x, y, Hxy).
destruct b as (x', y', Hxy'); cbn.
move x' before y; move y' before x'.
progress unfold cos2_sin2_prop in Hxy, Hxy' |-*.
cbn in Hxy, Hxy' |-*.
rewrite (rngl_squ_add Hic Hon).
rewrite (rngl_squ_sub Hop Hic Hon).
rewrite rngl_add_add_swap.
do 2 rewrite rngl_add_assoc.
rewrite <- (rngl_add_sub_swap Hop).
do 4 rewrite rngl_mul_assoc.
rewrite (rngl_mul_mul_swap Hic (2 * x * y')%L).
rewrite (rngl_mul_mul_swap Hic (2 * x) y')%L.
rewrite (rngl_mul_mul_swap Hic (2 * x * x') y' y)%L.
rewrite (rngl_sub_add Hop).
do 4 rewrite (rngl_squ_mul Hic).
rewrite <- rngl_add_assoc.
do 2 rewrite <- rngl_mul_add_distr_l.
apply (rngl_eqb_eq Hed) in Hxy'.
rewrite Hxy'.
now do 2 rewrite (rngl_mul_1_r Hon).
Qed.

Theorem angle_opp_prop : ∀ a, cos2_sin2_prop (rngl_cos a) (- rngl_sin a).
Proof.
destruct_ac.
intros.
destruct a as (x, y, Hxy); cbn.
progress unfold cos2_sin2_prop in Hxy |-*.
now rewrite (rngl_squ_opp Hop).
Qed.

Definition angle_zero :=
  {| rngl_cos := 1; rngl_sin := 0; rngl_cos2_sin2 := angle_zero_prop |}%L.

Definition angle_right :=
  {| rngl_cos := 0; rngl_sin := 1;
     rngl_cos2_sin2 := angle_right_prop |}%L.

Definition angle_straight :=
  {| rngl_cos := -1; rngl_sin := 0;
     rngl_cos2_sin2 := angle_straight_prop |}%L.

Definition angle_add a b :=
  {| rngl_cos := (rngl_cos a * rngl_cos b - rngl_sin a * rngl_sin b)%L;
     rngl_sin := (rngl_sin a * rngl_cos b + rngl_cos a * rngl_sin b)%L;
     rngl_cos2_sin2 := angle_add_prop a b |}.

Definition angle_opp a :=
  {| rngl_cos := rngl_cos a; rngl_sin := (- rngl_sin a)%L;
     rngl_cos2_sin2 := angle_opp_prop a |}.

Definition angle_sub θ1 θ2 := angle_add θ1 (angle_opp θ2).

Fixpoint angle_mul_nat a n :=
  match n with
  | 0 => angle_zero
  | S n' => angle_add a (angle_mul_nat a n')
  end.

Theorem cos2_sin2_prop_add_squ : ∀ c s, cos2_sin2_prop c s → (c² + s² = 1)%L.
Proof.
destruct_ac.
intros * Hcs.
progress unfold cos2_sin2_prop in Hcs.
now apply (rngl_eqb_eq Hed) in Hcs.
Qed.

Theorem cos2_sin2_1 : ∀ θ, ((rngl_cos θ)² + (rngl_sin θ)² = 1)%L.
Proof.
destruct_ac.
intros.
destruct θ as (c, s, Hcs); cbn.
progress unfold cos2_sin2_prop in Hcs.
now apply (rngl_eqb_eq Hed) in Hcs.
Qed.

Theorem rngl_cos_proj_bound : ∀ c s, cos2_sin2_prop c s → (-1 ≤ c ≤ 1)%L.
Proof.
destruct_ac.
intros * Hcs.
apply cos2_sin2_prop_add_squ in Hcs.
assert (H : (c² ≤ 1)%L). {
  rewrite <- Hcs.
  apply (rngl_le_add_r Hos Hor).
  apply (rngl_squ_nonneg Hon Hos Hiq Hor).
}
replace 1%L with 1²%L in H. 2: {
  apply (rngl_mul_1_l Hon).
}
rewrite <- (rngl_squ_abs Hop c) in H.
rewrite <- (rngl_squ_abs Hop 1%L) in H.
apply (rngl_square_le_simpl_nonneg Hon Hop Hiq Hor) in H. 2: {
  rewrite (rngl_abs_1 Hon Hos Hiq Hor).
  apply (rngl_0_le_1 Hon Hos Hiq Hor).
}
rewrite (rngl_abs_1 Hon Hos Hiq Hor) in H.
now apply (rngl_abs_le Hop Hor) in H.
Qed.

Theorem rngl_sin_proj_bound : ∀ c s, cos2_sin2_prop c s → (-1 ≤ s ≤ 1)%L.
Proof.
destruct_ac.
intros * Hcs.
specialize (rngl_int_dom_or_inv_1_quo Hiv Hon) as Hii.
apply cos2_sin2_prop_add_squ in Hcs.
assert (H : (s² ≤ 1)%L). {
  rewrite <- Hcs.
  apply (rngl_le_add_l Hos Hor).
  apply (rngl_squ_nonneg Hon Hos Hiq Hor).
}
replace 1%L with 1²%L in H. 2: {
  apply (rngl_mul_1_l Hon).
}
rewrite <- (rngl_squ_abs Hop s) in H.
rewrite <- (rngl_squ_abs Hop 1%L) in H.
apply (rngl_square_le_simpl_nonneg Hon Hop Hiq Hor) in H. 2: {
  rewrite (rngl_abs_1 Hon Hos Hiq Hor).
  apply (rngl_0_le_1 Hon Hos Hiq Hor).
}
rewrite (rngl_abs_1 Hon Hos Hiq Hor) in H.
now apply (rngl_abs_le Hop Hor) in H.
Qed.

Theorem rngl_cos_bound : ∀ a, (-1 ≤ rngl_cos a ≤ 1)%L.
Proof.
destruct_ac.
intros.
destruct a as (ca, sa, Ha); cbn.
now apply (rngl_cos_proj_bound ca sa).
Qed.

Theorem rngl_sin_bound : ∀ a, (-1 ≤ rngl_sin a ≤ 1)%L.
Proof.
destruct_ac.
intros.
destruct a as (ca, sa, Ha); cbn.
now apply (rngl_sin_proj_bound ca sa).
Qed.

(* *)

Definition angle_eqb a b :=
  ((rngl_cos a =? rngl_cos b)%L && (rngl_sin a =? rngl_sin b)%L)%bool.

End a.

Declare Scope angle_scope.
Delimit Scope angle_scope with A.
Bind Scope angle_scope with angle.

Notation "0" := angle_zero : angle_scope.
Notation "θ1 + θ2" := (angle_add θ1 θ2) : angle_scope.
Notation "θ1 - θ2" := (angle_sub θ1 θ2) : angle_scope.
Notation "- θ" := (angle_opp θ) : angle_scope.
Notation "θ1 =? θ2" := (angle_eqb θ1 θ2) : angle_scope.
Notation "θ1 ≠? θ2" := (negb (angle_eqb θ1 θ2)) : angle_scope.
Notation "n * θ" := (angle_mul_nat θ n) : angle_scope.

Section a.

Context {T : Type}.
Context {ro : ring_like_op T}.
Context {rp : ring_like_prop T}.
Context {rl : real_like_prop T}.
Context {ac : angle_ctx T}.

Theorem rngl_cos_add :
  ∀ θ1 θ2,
  rngl_cos (θ1 + θ2) =
    (rngl_cos θ1 * rngl_cos θ2 - rngl_sin θ1 * rngl_sin θ2)%L.
Proof. easy. Qed.

Theorem rngl_sin_add :
  ∀ θ1 θ2,
  rngl_sin (θ1 + θ2) =
    (rngl_sin θ1 * rngl_cos θ2 + rngl_cos θ1 * rngl_sin θ2)%L.
Proof. easy. Qed.

Theorem rngl_cos_sub :
  ∀ θ1 θ2,
  (rngl_cos (θ1 - θ2) =
     rngl_cos θ1 * rngl_cos θ2 + rngl_sin θ1 * rngl_sin θ2)%L.
Proof.
destruct_ac.
intros; cbn.
rewrite (rngl_mul_opp_r Hop).
apply (rngl_sub_opp_r Hop).
Qed.

Theorem rngl_sin_sub :
  ∀ θ1 θ2,
  rngl_sin (θ1 - θ2) =
    (rngl_sin θ1 * rngl_cos θ2 - rngl_cos θ1 * rngl_sin θ2)%L.
Proof.
destruct_ac.
intros; cbn.
rewrite (rngl_mul_opp_r Hop).
apply (rngl_add_opp_r Hop).
Qed.

Theorem rngl_add_cos_nonneg_sqrt_mul_le :
  ∀ θ1 θ2,
  (0 ≤ rngl_cos θ1 + rngl_cos θ2)%L
  → (√((1 - rngl_cos θ1) * (1 - rngl_cos θ2)) ≤
      √((1 + rngl_cos θ1) * (1 + rngl_cos θ2)))%L.
Proof.
destruct_ac.
intros * H12.
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
destruct (Nat.eq_dec (rngl_characteristic T) 1) as [Hc1| Hc1]. {
  specialize (rngl_characteristic_1 Hon Hos Hc1) as H1.
  rewrite H1, (H1 (√_))%L.
  apply (rngl_le_refl Hor).
}
apply (rngl_square_le_simpl_nonneg Hon Hop Hiq Hor). {
  apply rl_sqrt_nonneg.
  now apply (rngl_mul_nonneg_nonneg Hon Hos Hiq Hor).
}
do 2 rewrite fold_rngl_squ.
rewrite (rngl_squ_sqrt Hon). 2: {
  now apply (rngl_mul_nonneg_nonneg Hon Hos Hiq Hor).
}
rewrite (rngl_squ_sqrt Hon). 2: {
  now apply (rngl_mul_nonneg_nonneg Hon Hos Hiq Hor).
}
rewrite (rngl_mul_sub_distr_l Hop).
rewrite (rngl_mul_1_r Hon).
rewrite (rngl_mul_sub_distr_r Hop).
rewrite (rngl_mul_1_l Hon).
rewrite (rngl_sub_sub_distr Hop).
rewrite rngl_mul_add_distr_l.
rewrite (rngl_mul_1_r Hon).
rewrite rngl_mul_add_distr_r.
rewrite (rngl_mul_1_l Hon).
rewrite rngl_add_assoc.
apply (rngl_add_le_mono_r Hos Hor).
rewrite <- (rngl_sub_add_distr Hos).
apply (rngl_le_sub_le_add_r Hop Hor).
do 2 rewrite <- rngl_add_assoc.
apply (rngl_le_add_r Hos Hor).
rewrite rngl_add_assoc.
rewrite rngl_add_add_swap.
rewrite rngl_add_assoc.
rewrite <- rngl_add_assoc.
rewrite <- (rngl_mul_2_l Hon).
rewrite <- (rngl_mul_2_l Hon (rngl_cos θ2)).
rewrite <- rngl_mul_add_distr_l.
apply (rngl_mul_nonneg_nonneg Hon Hos Hiq Hor); [ | easy ].
apply (rngl_lt_le_incl Hor).
apply (rngl_0_lt_2 Hon Hos Hiq Hc1 Hor).
Qed.

Theorem eq_rngl_sin_0 : ∀ θ, rngl_sin θ = 0%L → θ = 0%A ∨ θ = angle_straight.
Proof.
destruct_ac.
specialize (rngl_has_eq_dec_or_is_ordered_r Hor) as Heo.
intros * Hθ.
destruct θ as (c, s, Hcs).
cbn in Hθ |-*.
subst s; cbn.
specialize (cos2_sin2_prop_add_squ _ _ Hcs) as H1.
rewrite (rngl_squ_0 Hos) in H1.
rewrite rngl_add_0_r in H1.
rewrite <- (rngl_squ_1 Hon) in H1.
apply (rngl_squ_eq_cases Hon Hop Hiv Heo) in H1. 2: {
  rewrite (rngl_mul_1_l Hon).
  apply (rngl_mul_1_r Hon).
}
now destruct H1; subst c; [ left | right ]; apply eq_angle_eq.
Qed.

Theorem angle_add_comm : ∀ θ1 θ2, (θ1 + θ2 = θ2 + θ1)%A.
Proof.
destruct_ac.
intros.
apply eq_angle_eq; cbn.
rewrite (rngl_mul_comm Hic).
rewrite (rngl_mul_comm Hic (rngl_sin θ1)).
f_equal.
rewrite rngl_add_comm.
rewrite (rngl_mul_comm Hic).
rewrite (rngl_mul_comm Hic (rngl_cos θ2)).
easy.
Qed.

Theorem angle_add_assoc : ∀ θ1 θ2 θ3, (θ1 + (θ2 + θ3) = (θ1 + θ2) + θ3)%A.
Proof.
destruct_ac.
intros.
apply eq_angle_eq; cbn.
destruct θ1 as (c1, s1, Hcs1).
destruct θ2 as (c2, s2, Hcs2).
destruct θ3 as (c3, s3, Hcs3).
cbn.
f_equal. {
  rewrite (rngl_mul_sub_distr_l Hop).
  rewrite (rngl_mul_sub_distr_r Hop).
  rewrite rngl_mul_add_distr_l.
  rewrite rngl_mul_add_distr_r.
  do 4 rewrite rngl_mul_assoc.
  do 2 rewrite <- (rngl_sub_add_distr Hos).
  f_equal.
  rewrite rngl_add_comm; symmetry.
  apply rngl_add_assoc.
} {
  rewrite (rngl_mul_sub_distr_l Hop).
  rewrite (rngl_mul_sub_distr_r Hop).
  rewrite rngl_mul_add_distr_l.
  rewrite rngl_mul_add_distr_r.
  do 4 rewrite rngl_mul_assoc.
  rewrite (rngl_add_sub_assoc Hop).
  rewrite rngl_add_assoc.
  rewrite (rngl_add_sub_swap Hop).
  f_equal.
  symmetry.
  apply (rngl_add_sub_swap Hop).
}
Qed.

Theorem angle_add_opp_l : ∀ θ1 θ2, (- θ1 + θ2 = θ2 - θ1)%A.
Proof.
intros.
apply angle_add_comm.
Qed.

Theorem angle_add_opp_r : ∀ θ1 θ2, (θ1 + - θ2 = θ1 - θ2)%A.
Proof. easy. Qed.

Theorem angle_sub_diag : ∀ θ, (θ - θ = 0)%A.
Proof.
destruct_ac.
intros.
apply eq_angle_eq; cbn.
rewrite (rngl_mul_opp_r Hop).
rewrite (rngl_sub_opp_r Hop).
do 2 rewrite fold_rngl_squ.
rewrite cos2_sin2_1.
f_equal.
rewrite (rngl_mul_opp_r Hop).
rewrite (rngl_mul_comm Hic).
rewrite (rngl_add_opp_r Hop).
apply (rngl_sub_diag Hos).
Qed.

Theorem angle_add_0_l : ∀ θ, (0 + θ = θ)%A.
Proof.
destruct_ac.
intros.
apply eq_angle_eq; cbn.
do 2 rewrite (rngl_mul_1_l Hon).
do 2 rewrite (rngl_mul_0_l Hos).
rewrite (rngl_sub_0_r Hos).
now rewrite rngl_add_0_l.
Qed.

Theorem angle_add_0_r : ∀ θ, (θ + 0 = θ)%A.
Proof.
destruct_ac.
intros.
apply eq_angle_eq; cbn.
do 2 rewrite (rngl_mul_1_r Hon).
do 2 rewrite (rngl_mul_0_r Hos).
rewrite (rngl_sub_0_r Hos).
now rewrite rngl_add_0_r.
Qed.

Theorem angle_sub_0_l : ∀ θ, (0 - θ = - θ)%A.
Proof.
destruct_ac.
intros.
apply eq_angle_eq; cbn.
do 2 rewrite (rngl_mul_1_l Hon).
do 2 rewrite (rngl_mul_0_l Hos).
rewrite (rngl_sub_0_r Hos).
now rewrite rngl_add_0_l.
Qed.

Theorem angle_sub_0_r : ∀ θ, (θ - 0 = θ)%A.
Proof.
destruct_ac.
intros.
apply eq_angle_eq; cbn.
do 2 rewrite (rngl_mul_1_r Hon).
rewrite (rngl_opp_0 Hop).
do 2 rewrite (rngl_mul_0_r Hos).
rewrite (rngl_sub_0_r Hos).
now rewrite rngl_add_0_r.
Qed.

Theorem angle_add_opp_diag_l : ∀ θ, (- θ + θ = 0)%A.
Proof.
destruct_ac; intros.
apply eq_angle_eq; cbn.
do 2 rewrite (rngl_mul_opp_l Hop).
progress unfold rngl_sub.
rewrite Hop.
rewrite (rngl_opp_involutive Hop).
do 2 rewrite fold_rngl_squ.
rewrite cos2_sin2_1.
f_equal.
rewrite (rngl_add_opp_l Hop).
rewrite (rngl_mul_comm Hic).
apply (rngl_sub_diag Hos).
Qed.

Theorem angle_add_sub : ∀ θ1 θ2, (θ1 + θ2 - θ2)%A = θ1.
Proof.
destruct_ac; intros.
progress unfold angle_sub.
rewrite <- angle_add_assoc.
rewrite angle_add_opp_r.
rewrite angle_sub_diag.
apply (angle_add_0_r).
Qed.

Theorem angle_sub_add : ∀ θ1 θ2, (θ1 - θ2 + θ2)%A = θ1.
Proof.
destruct_ac; intros.
progress unfold angle_sub.
rewrite <- angle_add_assoc.
rewrite angle_add_opp_diag_l.
apply (angle_add_0_r).
Qed.

Theorem angle_opp_add_distr : ∀ θ1 θ2, (- (θ1 + θ2))%A = (- θ2 - θ1)%A.
Proof.
destruct_ac.
intros.
apply eq_angle_eq; cbn.
rewrite (rngl_mul_opp_r Hop).
rewrite (rngl_mul_opp_l Hop).
rewrite (rngl_sub_opp_r Hop).
rewrite (rngl_add_opp_r Hop).
do 2 rewrite (rngl_mul_comm Hic (rngl_cos θ1)).
do 2 rewrite (rngl_mul_comm Hic (rngl_sin θ1)).
f_equal.
rewrite (rngl_opp_add_distr Hop).
rewrite (rngl_opp_sub_swap Hop).
rewrite <- (rngl_mul_opp_l Hop).
rewrite (rngl_mul_opp_r Hop).
symmetry.
apply (rngl_add_opp_r Hop).
Qed.

Theorem angle_opp_sub_distr : ∀ θ1 θ2, (- (θ1 - θ2))%A = (θ2 - θ1)%A.
Proof.
destruct_ac.
intros.
apply eq_angle_eq; cbn.
do 3 rewrite (rngl_mul_opp_r Hop).
do 2 rewrite (rngl_sub_opp_r Hop).
rewrite (rngl_add_opp_r Hop).
rewrite (rngl_opp_sub_distr Hop).
do 2 rewrite (rngl_mul_comm Hic (rngl_cos θ1)).
do 2 rewrite (rngl_mul_comm Hic (rngl_sin θ1)).
f_equal.
rewrite (rngl_mul_opp_r Hop).
symmetry.
apply (rngl_add_opp_r Hop).
Qed.

Theorem angle_opp_involutive : ∀ θ, (- - θ)%A = θ.
Proof.
destruct_ac.
intros.
apply eq_angle_eq; cbn.
f_equal.
apply (rngl_opp_involutive Hop).
Qed.

Theorem angle_sub_sub_distr :
  ∀ θ1 θ2 θ3, (θ1 - (θ2 - θ3))%A = (θ1 - θ2 + θ3)%A.
Proof.
intros.
progress unfold angle_sub.
rewrite <- angle_add_assoc.
f_equal.
rewrite angle_opp_add_distr.
rewrite angle_opp_involutive.
apply angle_add_comm.
Qed.

Theorem angle_add_move_l : ∀ θ1 θ2 θ3, (θ1 + θ2)%A = θ3 ↔ θ2 = (θ3 - θ1)%A.
Proof.
destruct_ac.
intros.
split; intros H2. {
  subst θ3; symmetry.
  rewrite angle_add_comm.
  apply angle_add_sub.
} {
  subst θ2.
  rewrite angle_add_comm.
  apply angle_sub_add.
}
Qed.

Theorem angle_add_move_r : ∀ θ1 θ2 θ3, (θ1 + θ2)%A = θ3 ↔ θ1 = (θ3 - θ2)%A.
Proof.
destruct_ac; intros.
rewrite angle_add_comm.
apply angle_add_move_l.
Qed.

Theorem angle_sub_move_l : ∀ θ1 θ2 θ3, (θ1 - θ2)%A = θ3 ↔ θ2 = (θ1 - θ3)%A.
Proof.
destruct_ac.
intros.
split; intros Ha. {
  subst θ3; symmetry.
  rewrite angle_sub_sub_distr.
  rewrite angle_sub_diag.
  apply angle_add_0_l.
} {
  subst θ2.
  rewrite angle_sub_sub_distr.
  rewrite angle_sub_diag.
  apply angle_add_0_l.
}
Qed.

Theorem angle_sub_move_r : ∀ θ1 θ2 θ3, (θ1 - θ2)%A = θ3 ↔ θ1 = (θ3 + θ2)%A.
Proof.
destruct_ac.
intros.
split; intros Ha. {
  subst θ3; symmetry.
  apply angle_sub_add.
} {
  subst θ1.
  apply angle_add_sub.
}
Qed.

Theorem rngl_cos_add_straight_l :
  ∀ θ, rngl_cos (angle_straight + θ) = (- rngl_cos θ)%L.
Proof.
destruct_ac.
intros; cbn.
rewrite (rngl_mul_opp_l Hop).
rewrite (rngl_mul_1_l Hon).
rewrite (rngl_mul_0_l Hos).
apply (rngl_sub_0_r Hos).
Qed.

Theorem rngl_cos_add_straight_r :
  ∀ θ, rngl_cos (θ + angle_straight) = (- rngl_cos θ)%L.
Proof.
destruct_ac.
intros; cbn.
rewrite (rngl_mul_opp_r Hop).
rewrite (rngl_mul_1_r Hon).
rewrite (rngl_mul_0_r Hos).
apply (rngl_sub_0_r Hos).
Qed.

Theorem rngl_cos_add_right_l :
  ∀ θ, rngl_cos (angle_right + θ) = (- rngl_sin θ)%L.
Proof.
destruct_ac.
intros; cbn.
rewrite (rngl_mul_1_l Hon).
rewrite (rngl_mul_0_l Hos).
apply (rngl_sub_0_l Hop).
Qed.

Theorem rngl_cos_add_right_r :
  ∀ θ, rngl_cos (θ + angle_right) = (- rngl_sin θ)%L.
Proof.
destruct_ac.
intros; cbn.
rewrite (rngl_mul_1_r Hon).
rewrite (rngl_mul_0_r Hos).
apply (rngl_sub_0_l Hop).
Qed.

Theorem rngl_sin_add_right_l :
  ∀ θ, rngl_sin (angle_right + θ) = rngl_cos θ.
Proof.
destruct_ac.
intros; cbn.
rewrite (rngl_mul_1_l Hon).
rewrite (rngl_mul_0_l Hos).
apply rngl_add_0_r.
Qed.

Theorem rngl_sin_add_right_r :
  ∀ θ, rngl_sin (θ + angle_right) = rngl_cos θ.
Proof.
destruct_ac.
intros; cbn.
rewrite (rngl_mul_1_r Hon).
rewrite (rngl_mul_0_r Hos).
apply rngl_add_0_l.
Qed.

Theorem rngl_cos_sub_straight_l :
  ∀ θ, rngl_cos (angle_straight - θ) = (- rngl_cos θ)%L.
Proof.
destruct_ac.
intros; cbn.
rewrite (rngl_mul_opp_l Hop).
rewrite (rngl_mul_1_l Hon).
rewrite (rngl_mul_0_l Hos).
now rewrite (rngl_sub_0_r Hos).
Qed.

Theorem rngl_sin_sub_straight_l :
  ∀ θ, rngl_sin (angle_straight - θ) = rngl_sin θ.
Proof.
destruct_ac.
intros; cbn.
rewrite (rngl_mul_opp_l Hop).
rewrite (rngl_mul_1_l Hon).
rewrite (rngl_mul_0_l Hos).
rewrite rngl_add_0_l.
apply (rngl_opp_involutive Hop).
Qed.

Theorem rngl_cos_sub_straight_r :
  ∀ θ, rngl_cos (θ - angle_straight) = (- rngl_cos θ)%L.
Proof.
destruct_ac.
intros; cbn.
rewrite (rngl_mul_opp_r Hop).
rewrite (rngl_mul_1_r Hon).
rewrite (rngl_opp_0 Hop).
rewrite (rngl_mul_0_r Hos).
now rewrite (rngl_sub_0_r Hos).
Qed.

Theorem rngl_sin_sub_straight_r :
  ∀ θ, rngl_sin (θ - angle_straight) = (- rngl_sin θ)%L.
Proof.
destruct_ac.
intros; cbn.
rewrite (rngl_opp_0 Hop).
rewrite (rngl_mul_opp_r Hop).
rewrite (rngl_mul_0_r Hos).
rewrite rngl_add_0_r.
now rewrite (rngl_mul_1_r Hon).
Qed.

Theorem rngl_sin_nonneg_cos_le_sin_le :
  ∀ θ1 θ2,
  (0 ≤ rngl_sin θ1)%L
  → (0 ≤ rngl_sin θ2)%L
  → (rngl_cos θ1 ≤ rngl_cos θ2)%L
  → if (0 ≤? rngl_cos θ1)%L then (rngl_sin θ2 ≤ rngl_sin θ1)%L
    else if (0 ≤? rngl_cos θ2)%L then (0 ≤ rngl_sin (θ1 - θ2))%L
    else (rngl_sin θ1 ≤ rngl_sin θ2)%L.
Proof.
destruct_ac.
intros * Hzs1 Hzs2 Hc12.
specialize (rngl_int_dom_or_inv_1_quo Hiv Hon) as Hii.
remember (0 ≤? rngl_cos θ1)%L as zc1 eqn:Hzc1.
symmetry in Hzc1.
destruct zc1. {
  apply rngl_leb_le in Hzc1.
  rewrite <- (rngl_abs_nonneg_eq Hop Hor) in Hc12. 2: {
    eapply (rngl_le_trans Hor); [ apply Hzc1 | easy ].
  }
  rewrite <- (rngl_abs_nonneg_eq Hop Hor _ Hzc1) in Hc12.
  rewrite <- (rngl_abs_nonneg_eq Hop Hor); [ | easy ].
  rewrite <- (rngl_abs_nonneg_eq Hop Hor _ Hzs2).
  apply (rngl_abs_le_squ_le Hon Hop Hiq Hor) in Hc12.
  apply (rngl_squ_le_abs_le Hon Hop Hiq Hor).
  specialize (cos2_sin2_1 θ1) as Hcs1.
  specialize (cos2_sin2_1 θ2) as Hcs2.
  apply (rngl_add_sub_eq_r Hos) in Hcs1, Hcs2.
  rewrite <- Hcs1, <- Hcs2 in Hc12.
  now apply (rngl_sub_le_mono_l Hop Hor) in Hc12.
}
apply (rngl_leb_gt Hor) in Hzc1.
remember (0 ≤? rngl_cos θ2)%L as zc2 eqn:Hzc2.
symmetry in Hzc2.
destruct zc2. {
  apply rngl_leb_le in Hzc2; cbn.
  rewrite (rngl_mul_opp_r Hop).
  rewrite rngl_add_comm.
  rewrite (rngl_add_opp_l Hop).
  apply (rngl_le_0_sub Hop Hor).
  apply (rngl_le_trans Hor _ 0)%L. {
    apply (rngl_mul_nonpos_nonneg Hon Hop Hiq Hor); [ | easy ].
    now apply (rngl_lt_le_incl Hor).
  } {
    now apply (rngl_mul_nonneg_nonneg Hon Hos Hiq Hor).
  }
} {
  apply (rngl_leb_gt Hor) in Hzc2.
  apply (rngl_opp_le_compat Hop Hor) in Hc12.
  rewrite <- (rngl_abs_nonpos_eq Hop Hor) in Hc12. 2: {
    now apply (rngl_lt_le_incl Hor).
  }
  rewrite <- (rngl_abs_nonpos_eq Hop Hor) in Hc12. 2: {
    now apply (rngl_lt_le_incl Hor).
  }
  rewrite <- (rngl_abs_nonneg_eq Hop Hor); [ | easy ].
  rewrite <- (rngl_abs_nonneg_eq Hop Hor _ Hzs1).
  apply (rngl_abs_le_squ_le Hon Hop Hiq Hor) in Hc12.
  apply (rngl_squ_le_abs_le Hon Hop Hiq Hor).
  specialize (cos2_sin2_1 θ1) as Hcs1.
  specialize (cos2_sin2_1 θ2) as Hcs2.
  apply (rngl_add_sub_eq_r Hos) in Hcs1, Hcs2.
  rewrite <- Hcs1, <- Hcs2 in Hc12.
  now apply (rngl_sub_le_mono_l Hop Hor) in Hc12.
}
Qed.

Theorem rngl_cos_cos_sin_sin_nonneg_sin_le_cos_le_iff :
  ∀ θ1 θ2,
  (0 ≤ rngl_sin θ1)%L
  → (0 ≤ rngl_sin θ2)%L
  → (0 ≤ rngl_cos θ1)%L
  → (0 ≤ rngl_cos θ2)%L
  → (rngl_sin θ1 ≤ rngl_sin θ2)%L
  ↔ (rngl_cos θ2 ≤ rngl_cos θ1)%L.
Proof.
destruct_ac.
specialize (rngl_int_dom_or_inv_1_quo Hiv Hon) as Hii.
intros * Hzs1 Hzs2 Hzc1 Hzc2.
split. {
  intros Hss.
  apply rngl_nlt_ge in Hss.
  apply (rngl_nlt_ge_iff Hor).
  intros Hcc; apply Hss; clear Hss.
  apply (rngl_le_neq Hor).
  split. {
    apply (rngl_lt_le_incl Hor) in Hcc.
    specialize rngl_sin_nonneg_cos_le_sin_le as H1.
    specialize (H1 _ _ Hzs1 Hzs2 Hcc).
    apply rngl_leb_le in Hzc1.
    now rewrite Hzc1 in H1.
  }
  intros Hss.
  apply rngl_nle_gt in Hcc.
  apply Hcc; clear Hcc.
  rewrite <- (rngl_abs_nonneg_eq Hop Hor); [ | easy ].
  rewrite <- (rngl_abs_nonneg_eq Hop Hor (rngl_cos θ2)); [ | easy ].
  apply (rngl_squ_le_abs_le Hon Hop Hiq Hor).
  specialize (cos2_sin2_1 θ1) as H1.
  apply (rngl_add_move_r Hop) in H1.
  rewrite H1; clear H1.
  specialize (cos2_sin2_1 θ2) as H1.
  apply (rngl_add_move_r Hop) in H1.
  rewrite H1, Hss; clear H1.
  apply (rngl_le_refl Hor).
} {
  intros Hcc.
  specialize rngl_sin_nonneg_cos_le_sin_le as H1.
  specialize (H1 _ _ Hzs2 Hzs1 Hcc).
  apply rngl_leb_le in Hzc2.
  now rewrite Hzc2 in H1.
}
Qed.

Theorem rngl_cos_cos_sin_sin_nonneg_sin_lt_cos_lt_iff :
  ∀ θ1 θ2,
  (0 ≤ rngl_sin θ1)%L
  → (0 ≤ rngl_sin θ2)%L
  → (0 ≤ rngl_cos θ1)%L
  → (0 ≤ rngl_cos θ2)%L
  → (rngl_sin θ1 < rngl_sin θ2)%L
  ↔ (rngl_cos θ2 < rngl_cos θ1)%L.
Proof.
destruct_ac.
intros * Hzs1 Hzs2 Hzc1 Hzc2.
split. 2: {
  intros Hcc.
  apply rngl_nle_gt in Hcc.
  apply (rngl_nle_gt_iff Hor).
  intros Hss; apply Hcc; clear Hcc.
  now apply rngl_cos_cos_sin_sin_nonneg_sin_le_cos_le_iff.
} {
  intros Hss.
  apply rngl_nle_gt in Hss.
  apply (rngl_nle_gt_iff Hor).
  intros Hcc; apply Hss; clear Hss.
  now apply rngl_cos_cos_sin_sin_nonneg_sin_le_cos_le_iff.
}
Qed.

Theorem eq_rngl_cos_0 :
  ∀ θ, rngl_cos θ = 0%L ↔ (θ = angle_right ∨ θ = - angle_right)%A.
Proof.
destruct_ac.
specialize (rngl_has_eq_dec_or_is_ordered_r Hor) as Heo.
intros.
split; intros Hθ; [ | now destruct Hθ; subst θ ].
specialize (cos2_sin2_1 θ) as H1.
rewrite Hθ in H1.
rewrite (rngl_squ_0 Hos) in H1.
apply (rngl_add_move_l Hop) in H1.
rewrite (rngl_sub_0_r Hos) in H1.
rewrite <- (rngl_squ_1 Hon) in H1.
apply (rngl_squ_eq_cases Hon Hop Hiv Heo) in H1. 2: {
  rewrite (rngl_mul_1_l Hon).
  apply (rngl_mul_1_r Hon).
}
destruct H1. {
  left; apply eq_angle_eq.
  now rewrite Hθ, H.
} {
  right; apply eq_angle_eq.
  now rewrite Hθ, H.
}
Qed.

Theorem eq_rngl_cos_1 : ∀ θ, rngl_cos θ = 1%L ↔ θ = 0%A.
Proof.
destruct_ac.
specialize (rngl_has_eq_dec_or_is_ordered_r Hor) as Heo.
intros.
split; intros Hθ; [ | now subst θ ].
specialize (cos2_sin2_1 θ) as H1.
rewrite Hθ in H1.
rewrite (rngl_squ_1 Hon) in H1.
apply (rngl_add_move_l Hop) in H1.
rewrite (rngl_sub_diag Hos) in H1.
apply (eq_rngl_squ_0 Hos) in H1. 2: {
  apply Bool.orb_true_iff; right.
  rewrite Heo, Bool.andb_true_r.
  apply (rngl_has_inv_and_1_has_inv_and_1_or_pdiv Hon Hiv).
}
apply eq_angle_eq.
now rewrite Hθ, H1.
Qed.

Theorem eq_rngl_cos_opp_1 : ∀ θ, (rngl_cos θ = -1 → θ = angle_straight)%L.
Proof.
destruct_ac.
specialize (rngl_has_eq_dec_or_is_ordered_r Hor) as Heo.
intros * Hθ.
destruct θ as (c, s, Hcs).
cbn in Hθ |-*.
subst c.
apply eq_angle_eq; cbn.
f_equal.
apply (cos2_sin2_prop_add_squ) in Hcs.
rewrite (rngl_squ_opp Hop) in Hcs.
rewrite (rngl_squ_1 Hon) in Hcs.
apply (rngl_add_sub_eq_l Hos) in Hcs.
rewrite (rngl_sub_diag Hos) in Hcs.
symmetry in Hcs.
apply (eq_rngl_squ_0 Hos) in Hcs; [ easy | ].
apply Bool.orb_true_iff; right.
rewrite Heo, Bool.andb_true_r.
apply (rngl_has_inv_and_1_has_inv_and_1_or_pdiv Hon Hiv).
Qed.

Theorem eq_rngl_sin_1 : ∀ θ, rngl_sin θ = 1%L ↔ θ = angle_right.
Proof.
destruct_ac.
specialize (rngl_has_eq_dec_or_is_ordered_r Hor) as Heo.
intros.
split; intros Hθ; [ | now subst θ ].
specialize (cos2_sin2_1 θ) as H1.
rewrite Hθ in H1.
rewrite (rngl_squ_1 Hon) in H1.
apply (rngl_add_move_r Hop) in H1.
rewrite (rngl_sub_diag Hos) in H1.
apply (eq_rngl_squ_0 Hos) in H1. 2: {
  apply Bool.orb_true_iff; right.
  rewrite Heo, Bool.andb_true_r.
  apply (rngl_has_inv_and_1_has_inv_and_1_or_pdiv Hon Hiv).
}
apply eq_angle_eq.
now rewrite Hθ, H1.
Qed.

Theorem rngl_cos_eq :
  ∀ θ1 θ2, rngl_cos θ1 = rngl_cos θ2 → θ1 = θ2 ∨ θ1 = (- θ2)%A.
Proof.
destruct_ac.
specialize (rngl_has_eq_dec_or_is_ordered_r Hor) as Heo.
intros * Hcc.
destruct (rngl_eq_dec Heo (rngl_sin θ1) (rngl_sin θ2)) as [Hss| Hss]. {
  left.
  apply eq_angle_eq.
  now rewrite Hcc, Hss.
}
right.
apply eq_angle_eq.
rewrite Hcc; f_equal.
cbn.
specialize (cos2_sin2_1 θ1) as H1.
specialize (cos2_sin2_1 θ2) as H2.
apply (rngl_add_move_l Hop) in H1, H2.
rewrite Hcc in H1.
rewrite <- H2 in H1; clear H2.
apply (eq_rngl_squ_rngl_abs Hop Hor) in H1; cycle 1. {
  apply Bool.orb_true_iff; right.
  apply (rngl_has_inv_and_1_has_inv_and_1_or_pdiv Hon Hiv).
} {
  apply (rngl_mul_comm Hic).
}
progress unfold rngl_abs in H1.
remember (rngl_sin θ1 ≤? 0)%L as s1z eqn:Hs1z.
remember (rngl_sin θ2 ≤? 0)%L as s2z eqn:Hs2z.
symmetry in Hs1z, Hs2z.
destruct s1z; [ | now destruct s2z ].
destruct s2z; [ now apply (rngl_opp_inj Hop) in H1 | ].
rewrite <- H1; symmetry.
apply (rngl_opp_involutive Hop).
Qed.

Theorem rngl_sin_eq :
  ∀ θ1 θ2, rngl_sin θ1 = rngl_sin θ2 → θ1 = θ2 ∨ θ1 = (angle_straight - θ2)%A.
Proof.
destruct_ac.
specialize (rngl_has_eq_dec_or_is_ordered_r Hor) as Heo.
intros * Hss.
destruct (rngl_eq_dec Heo (rngl_cos θ1) (rngl_cos θ2)) as [Hcc| Hcc]. {
  left.
  apply eq_angle_eq.
  now rewrite Hcc, Hss.
}
right.
apply eq_angle_eq.
rewrite rngl_cos_sub_straight_l.
rewrite rngl_sin_sub_straight_l.
rewrite Hss; f_equal.
specialize (cos2_sin2_1 θ1) as H1.
specialize (cos2_sin2_1 θ2) as H2.
apply (rngl_add_move_r Hop) in H1, H2.
rewrite Hss in H1.
rewrite <- H2 in H1; clear H2.
apply (eq_rngl_squ_rngl_abs Hop Hor) in H1; cycle 1. {
  rewrite Bool.orb_true_iff; right.
  apply (rngl_has_inv_and_1_has_inv_and_1_or_pdiv Hon Hiv).
} {
  apply (rngl_mul_comm Hic).
}
progress unfold rngl_abs in H1.
remember (rngl_cos θ1 ≤? 0)%L as c1z eqn:Hc1z.
remember (rngl_cos θ2 ≤? 0)%L as c2z eqn:Hc2z.
symmetry in Hc1z, Hc2z.
destruct c1z; [ | now destruct c2z ].
destruct c2z; [ now apply (rngl_opp_inj Hop) in H1 | ].
rewrite <- H1; symmetry.
apply (rngl_opp_involutive Hop).
Qed.

Theorem rngl_cos_cos_sin_sin_neg_sin_le_cos_le_iff :
  ∀ θ1 θ2,
  (0 ≤ rngl_sin θ1)%L
  → (0 ≤ rngl_sin θ2)%L
  → (rngl_cos θ1 ≤ 0)%L
  → (rngl_cos θ2 ≤ 0)%L
  → (rngl_sin θ1 ≤ rngl_sin θ2)%L ↔ (rngl_cos θ1 ≤ rngl_cos θ2)%L.
Proof.
destruct_ac.
specialize (rngl_int_dom_or_inv_1_quo Hiv Hon) as Hii.
destruct (Nat.eq_dec (rngl_characteristic T) 1) as [Hc1| Hc1]. {
  specialize (rngl_characteristic_1 Hon Hos Hc1) as H1.
  intros * Hzs1 Hzs2 Hzc1 Hzc2.
  rewrite (H1 (rngl_sin θ1)), (H1 (rngl_sin θ2)).
  rewrite (H1 (rngl_cos θ1)), (H1 (rngl_cos θ2)).
  easy.
}
intros * Hzs1 Hzs2 Hzc1 Hzc2.
split. {
  intros Hss.
  apply rngl_nlt_ge in Hss.
  apply (rngl_nlt_ge_iff Hor).
  intros Hcc; apply Hss; clear Hss.
  apply (rngl_le_neq Hor).
  split. {
    apply (rngl_lt_le_incl Hor) in Hcc.
    specialize rngl_sin_nonneg_cos_le_sin_le as H1.
    specialize (H1 _ _ Hzs2 Hzs1 Hcc).
    destruct (rngl_le_dec Hor 0 (rngl_cos θ1)) as [H| H]. {
      apply (rngl_le_antisymm Hor) in H; [ | easy ].
      apply (eq_rngl_cos_0) in H.
      destruct H; subst θ1; [ apply rngl_sin_bound | ].
      exfalso.
      apply rngl_nlt_ge in Hzs1.
      apply Hzs1, (rngl_opp_1_lt_0 Hon Hop Hiq Hor Hc1).
    }
    apply (rngl_nle_gt_iff Hor) in H.
    move H before Hzc1; clear Hzc1; rename H into Hzc1.
    destruct (rngl_le_dec Hor 0 (rngl_cos θ2)) as [H| H]. {
      apply (rngl_le_antisymm Hor) in H; [ | easy ].
      apply (eq_rngl_cos_0) in H.
      destruct H; subst θ2. {
        apply (rngl_lt_le_incl Hor) in Hzc1.
        apply (rngl_le_antisymm Hor) in Hcc; [ | easy ].
        cbn in Hcc.
        apply (eq_rngl_cos_0) in Hcc.
        destruct Hcc; subst θ1; [ apply (rngl_le_refl Hor) | ].
        exfalso.
        apply rngl_nlt_ge in Hzs1.
        apply Hzs1; clear Hzs1; cbn.
        apply (rngl_opp_1_lt_0 Hon Hop Hiq Hor Hc1).
      }
      apply rngl_sin_bound.
    }
    apply (rngl_nle_gt_iff Hor) in H.
    move H before Hzc2; clear Hzc2; rename H into Hzc2.
    generalize Hzc2; intros H.
    apply (rngl_leb_gt Hor) in H.
    rewrite H in H1; clear H.
    generalize Hzc1; intros H.
    apply (rngl_leb_gt Hor) in H.
    now rewrite H in H1; clear H.
  }
  intros H.
  apply rngl_sin_eq in H.
  destruct H; subst θ2; [ now apply (rngl_lt_irrefl Hor) in Hcc | ].
  rewrite rngl_cos_sub_straight_l in Hcc, Hzc2.
  apply (rngl_opp_nonpos_nonneg Hop Hor) in Hzc2.
  apply (rngl_le_antisymm Hor) in Hzc2; [ | easy ].
  rewrite Hzc2 in Hcc.
  rewrite (rngl_opp_0 Hop) in Hcc.
  now apply (rngl_lt_irrefl Hor) in Hcc.
} {
  intros Hcc.
  destruct (rngl_le_dec Hor 0 (rngl_cos θ1)) as [H| H]. {
    apply (rngl_le_antisymm Hor) in H; [ | easy ].
    apply (eq_rngl_cos_0) in H.
    destruct H; subst θ1. {
      apply (rngl_le_antisymm Hor) in Hcc; [ | easy ].
      apply (eq_rngl_cos_0) in Hcc.
      destruct Hcc; subst θ2; [ apply (rngl_le_refl Hor) | ].
      exfalso.
      apply rngl_nlt_ge in Hzs2.
      apply Hzs2, (rngl_opp_1_lt_0 Hon Hop Hiq Hor Hc1).
    }
    apply rngl_sin_bound.
  }
  apply (rngl_nle_gt_iff Hor) in H.
  move H before Hzc1; clear Hzc1; rename H into Hzc1.
  destruct (rngl_le_dec Hor 0 (rngl_cos θ2)) as [H| H]. {
    apply (rngl_le_antisymm Hor) in H; [ | easy ].
    apply (eq_rngl_cos_0) in H.
    destruct H; subst θ2. {
      apply rngl_sin_bound.
    }
    exfalso.
    apply rngl_nlt_ge in Hzs2.
    apply Hzs2, (rngl_opp_1_lt_0 Hon Hop Hiq Hor Hc1).
  }
  apply (rngl_nle_gt_iff Hor) in H.
  move H before Hzc2; clear Hzc2; rename H into Hzc2.
  specialize rngl_sin_nonneg_cos_le_sin_le as H1.
  specialize (H1 _ _ Hzs1 Hzs2 Hcc).
  generalize Hzc1; intros H.
  apply (rngl_leb_gt Hor) in H.
  rewrite H in H1; clear H.
  generalize Hzc2; intros H.
  apply (rngl_leb_gt Hor) in H.
  now rewrite H in H1; clear H.
}
Qed.

Theorem rngl_add_cos_nonneg_when_sin_nonneg :
  ∀ θ1 θ2,
  (0 ≤ rngl_sin θ1)%L
  → (0 ≤ rngl_sin θ2)%L
  → (0 ≤ rngl_sin (θ1 + θ2))%L
  → (0 ≤ rngl_cos θ1)%L
  → (0 ≤ rngl_cos θ1 + rngl_cos θ2)%L.
Proof.
destruct_ac.
intros * Hzs1 Hzs2 Hzs3 Hzc1.
specialize (rngl_has_eq_dec_or_is_ordered_r Hor) as Heo.
specialize (rngl_int_dom_or_inv_1_quo Hiv Hon) as Hii.
destruct (Nat.eq_dec (rngl_characteristic T) 1) as [Hc1| Hc1]. {
  specialize (rngl_characteristic_1 Hon Hos Hc1) as H1.
  rewrite H1.
  apply (rngl_le_refl Hor).
}
remember (θ1 + θ2)%A as θ3 eqn:Hθ3.
destruct (rngl_le_dec Hor 0 (rngl_cos θ2)) as [Hzc2| Hzc2]. {
  now apply (rngl_le_0_add Hos Hor).
}
apply (rngl_nle_gt_iff Hor) in Hzc2.
(* here, for sin θ3 to be non negative, then the negativity
   of θ2 must not be greater than the positivity of θ1 *)
apply (rngl_le_sub_le_add_r Hop Hor).
rewrite (rngl_sub_0_l Hop).
apply (rngl_nlt_ge_iff Hor).
intros Hcc.
apply rngl_nlt_ge in Hzs3.
apply Hzs3; clear Hzs3.
subst θ3; cbn.
(* special case for sin θ2 = 0 *)
destruct (rngl_eq_dec Heo (rngl_sin θ2) 0) as [H2z| H2z]. {
  rewrite H2z, (rngl_mul_0_r Hos), rngl_add_0_r.
  destruct (rngl_eq_dec Heo (rngl_sin θ1) 0) as [H1z| H1z]. {
    apply (eq_rngl_sin_0) in H2z, H1z.
    destruct H2z; subst θ2. {
      apply (rngl_nle_gt_iff Hor) in Hzc2.
      exfalso; apply Hzc2; clear Hzc2; cbn.
      apply (rngl_0_le_1 Hon Hos Hiq Hor).
    }
    clear Hzs2 Hzc2.
    cbn in Hcc.
    exfalso.
    destruct H1z; subst θ1. {
      rewrite (rngl_opp_involutive Hop) in Hcc.
      cbn in Hcc.
      now apply (rngl_lt_irrefl Hor) in Hcc.
    }
    cbn in Hzc1.
    apply rngl_nlt_ge in Hzc1.
    apply Hzc1; clear Hzc1.
    apply (rngl_opp_neg_pos Hop Hor).
    apply (rngl_0_lt_1 Hon Hos Hiq Hc1 Hor).
  }
  apply (rngl_mul_pos_neg Hon Hop Hiq Hor); [ | easy ].
  apply (rngl_le_neq Hor).
  split; [ easy | ].
  now apply not_eq_sym.
}
assert (Hzls2 : (0 < rngl_sin θ2)%L). {
  apply (rngl_le_neq Hor).
  split; [ easy | ].
  now apply not_eq_sym.
}
clear H2z.
assert (Hs21 : (rngl_sin θ2 < rngl_sin θ1)%L). {
  apply (rngl_lt_opp_r Hop Hor) in Hcc.
  remember (angle_straight - θ2)%A as θ eqn:Hθ.
  symmetry in Hθ.
  apply angle_sub_move_l in Hθ.
  subst θ2; rename θ into θ2.
  move θ2 before θ1.
  rewrite rngl_cos_sub_straight_l in Hcc, Hzc2.
  rewrite rngl_sin_sub_straight_l in Hzs2 |-*.
  rewrite (rngl_add_opp_r Hop) in Hcc.
  apply -> (rngl_lt_sub_0 Hop Hor) in Hcc.
  apply (rngl_opp_neg_pos Hop Hor) in Hzc2.
  apply (rngl_lt_le_incl Hor) in Hzc2.
  now apply rngl_cos_cos_sin_sin_nonneg_sin_lt_cos_lt_iff.
}
rewrite rngl_add_comm.
apply
  (rngl_le_lt_trans Hor _
     ((- rngl_cos θ2) * rngl_sin θ2 +
        rngl_sin θ1 * rngl_cos θ2))%L. {
  apply (rngl_add_le_mono_r Hos Hor).
  apply (rngl_mul_le_mono_pos_r Hon Hop Hiq Hor); [ easy | ].
  now apply (rngl_lt_le_incl Hor).
}
rewrite rngl_add_comm.
rewrite (rngl_mul_comm Hic).
rewrite (rngl_mul_opp_l Hop).
rewrite (rngl_add_opp_r Hop).
rewrite <- (rngl_mul_sub_distr_l Hop).
rewrite (rngl_mul_comm Hic).
apply (rngl_mul_pos_neg Hon Hop Hiq Hor); [ | easy ].
now apply (rngl_lt_0_sub Hop Hor).
Qed.

Theorem rngl_sin_nonneg_sin_nonneg_add_1_cos_add_sub :
  ∀ θ1 θ2,
  (0 ≤? rngl_sin θ1)%L = (0 ≤? rngl_sin θ2)%L
  → ((1 + rngl_cos (θ1 + θ2)) * 2)%L =
      (√((1 + rngl_cos θ1) * (1 + rngl_cos θ2)) -
       √((1 - rngl_cos θ1) * (1 - rngl_cos θ2)))²%L.
Proof.
destruct_ac.
intros * Hzs12.
assert (Ha12 : ∀ θ1 θ2, (0 ≤ (1 + rngl_cos θ1) * (1 + rngl_cos θ2))%L). {
  intros.
  apply (rngl_mul_nonneg_nonneg Hon Hos Hiq Hor). {
    apply (rngl_le_sub_le_add_l Hop Hor).
    progress unfold rngl_sub.
    rewrite Hop, rngl_add_0_l.
    apply rngl_cos_bound.
  } {
    apply (rngl_le_sub_le_add_l Hop Hor).
    progress unfold rngl_sub.
    rewrite Hop, rngl_add_0_l.
    apply rngl_cos_bound.
  }
}
assert (Hs12 : ∀ θ1 θ2, (0 ≤ (1 - rngl_cos θ1) * (1 - rngl_cos θ2))%L). {
  intros.
  apply (rngl_mul_nonneg_nonneg Hon Hos Hiq Hor). {
    apply (rngl_le_add_le_sub_l Hop Hor).
    rewrite rngl_add_0_r.
    apply rngl_cos_bound.
  } {
    apply (rngl_le_add_le_sub_l Hop Hor).
    rewrite rngl_add_0_r.
    apply rngl_cos_bound.
  }
}
rewrite (rngl_squ_sub Hop Hic Hon).
rewrite (rngl_squ_sqrt Hon); [ | easy ].
rewrite (rngl_squ_sqrt Hon); [ | easy ].
rewrite <- (rngl_add_sub_swap Hop).
rewrite <- rngl_mul_assoc.
rewrite <- rl_sqrt_mul; [ | easy | easy ].
rewrite rngl_mul_assoc.
rewrite (rngl_mul_mul_swap Hic (1 + rngl_cos θ1))%L.
rewrite <- rngl_mul_assoc.
rewrite (rngl_squ_sub_squ' Hop).
rewrite (rngl_mul_1_r Hon), (rngl_mul_1_l Hon).
rewrite (rngl_add_sub Hos).
rewrite (rngl_squ_sub_squ' Hop).
rewrite (rngl_mul_1_r Hon), (rngl_mul_1_l Hon).
rewrite (rngl_add_sub Hos).
rewrite (rngl_squ_1 Hon).
replace (1 - (rngl_cos θ1)²)%L with (rngl_sin θ1)²%L. 2: {
  symmetry.
  apply (rngl_add_sub_eq_l Hos).
  apply (cos2_sin2_prop_add_squ).
  apply rngl_cos2_sin2.
}
replace (1 - (rngl_cos θ2)²)%L with (rngl_sin θ2)²%L. 2: {
  symmetry.
  apply (rngl_add_sub_eq_l Hos).
  apply (cos2_sin2_prop_add_squ).
  apply rngl_cos2_sin2.
}
rewrite rl_sqrt_mul; cycle 1. {
  apply (rngl_squ_nonneg Hon Hos Hiq Hor).
} {
  apply (rngl_squ_nonneg Hon Hos Hiq Hor).
}
do 2 rewrite (rl_sqrt_squ Hon Hop Hor).
rewrite (rngl_mul_add_distr_l (1 + rngl_cos θ1))%L.
rewrite (rngl_mul_1_r Hon).
rewrite (rngl_mul_add_distr_r 1 (rngl_cos θ1))%L.
rewrite (rngl_mul_1_l Hon).
rewrite (rngl_mul_sub_distr_l Hop (1 - rngl_cos θ1))%L.
rewrite (rngl_mul_1_r Hon).
rewrite (rngl_mul_sub_distr_r Hop 1 (rngl_cos θ1))%L.
rewrite (rngl_mul_1_l Hon).
rewrite rngl_add_assoc.
rewrite (rngl_add_sub_assoc Hop (1 + _ + _ + _ * _))%L.
rewrite (rngl_add_sub_assoc Hop _ 1 (rngl_cos θ1))%L.
rewrite (rngl_sub_sub_distr Hop _ (rngl_cos θ2)).
rewrite rngl_add_add_swap.
rewrite (rngl_add_add_swap _ (rngl_cos θ2) 1)%L.
rewrite (rngl_add_add_swap _ (rngl_cos θ1) 1)%L.
rewrite (rngl_add_sub_swap Hop _ _ (rngl_cos θ1)).
rewrite (rngl_add_sub_swap Hop _ _ (rngl_cos θ1)).
rewrite (rngl_add_sub Hos).
rewrite (rngl_add_sub_swap Hop _ _ (rngl_cos θ2)).
rewrite (rngl_add_sub Hos).
rewrite <- rngl_add_assoc.
rewrite <- (rngl_mul_2_l Hon (rngl_cos θ1 * _)%L).
rewrite (rngl_add_mul_r_diag_l Hon).
rewrite <- (rngl_mul_sub_distr_l Hop).
rewrite (rngl_mul_comm Hic).
f_equal.
rewrite <- (rngl_add_sub_assoc Hop).
f_equal; cbn.
f_equal.
remember (0 ≤? rngl_sin θ2)%L as zs2 eqn:Hzs2.
symmetry in Hzs2.
destruct zs2. {
  apply rngl_leb_le in Hzs2, Hzs12.
  rewrite (rngl_abs_nonneg_eq Hop Hor); [ | easy ].
  rewrite (rngl_abs_nonneg_eq Hop Hor); [ | easy ].
  easy.
} {
  apply (rngl_leb_gt Hor) in Hzs2, Hzs12.
  apply (rngl_lt_le_incl Hor) in Hzs2, Hzs12.
  rewrite (rngl_abs_nonpos_eq Hop Hor); [ | easy ].
  rewrite (rngl_abs_nonpos_eq Hop Hor); [ | easy ].
  rewrite (rngl_mul_opp_l Hop).
  rewrite (rngl_mul_opp_r Hop).
  symmetry.
  apply (rngl_opp_involutive Hop).
}
Qed.

Theorem angle_right_add_right :
  (angle_right + angle_right)%A = angle_straight.
Proof.
destruct_ac.
apply eq_angle_eq; cbn.
do 2 rewrite (rngl_mul_0_l Hos).
do 2 rewrite (rngl_mul_1_l Hon).
rewrite (rngl_sub_0_l Hop).
f_equal.
apply rngl_add_0_l.
Qed.

Theorem angle_straight_add_straight :
  (angle_straight + angle_straight = 0)%A.
Proof.
destruct_ac.
apply eq_angle_eq; cbn.
rewrite (rngl_mul_opp_opp Hop).
rewrite (rngl_mul_1_l Hon).
rewrite (rngl_mul_0_l Hos).
rewrite (rngl_sub_0_r Hos).
f_equal.
rewrite (rngl_mul_0_r Hos).
rewrite (rngl_mul_0_l Hos).
apply rngl_add_0_l.
Qed.

Theorem angle_straight_sub_right :
  (angle_straight - angle_right)%A = angle_right.
Proof.
destruct_ac.
apply eq_angle_eq; cbn.
do 2 rewrite (rngl_mul_0_r Hos).
rewrite (rngl_mul_0_l Hos).
rewrite (rngl_sub_diag Hos).
f_equal.
rewrite (rngl_squ_opp_1 Hon Hop).
apply rngl_add_0_l.
Qed.

Theorem rngl_sin_nonneg_sin_nonneg_sin_nonneg :
  ∀ θ1 θ2,
  θ1 ≠ angle_straight ∨ θ2 ≠ angle_straight
  → (0 ≤ rngl_sin θ1)%L
  → (0 ≤ rngl_sin θ2)%L
  → (0 ≤ rngl_sin (θ1 + θ2))%L
  → √((1 + rngl_cos (θ1 + θ2)) / 2)%L =
      (√((1 + rngl_cos θ1) / 2) * √((1 + rngl_cos θ2) / 2) -
       √((1 - rngl_cos θ1) / 2) * √((1 - rngl_cos θ2) / 2))%L.
Proof.
(* same goal but different hypotheses in the theorem
   rngl_sin_nonneg_sin_nonneg_add_cos_nonneg defined above;
   perhaps there is something to do? *)
(*
intros * Haov Hzs1 Hzs2 Hzs3.
apply rngl_sin_nonneg_sin_nonneg_add_cos_nonneg; try easy.
...
*)
destruct_ac.
specialize (rngl_has_eq_dec_or_is_ordered_r Hor) as Heo.
intros * H12ns Hzs1 Hzs2 Hzs3.
specialize (rngl_has_inv_and_1_has_inv_and_1_or_pdiv Hon Hiv) as Hi1.
specialize (rngl_int_dom_or_inv_1_quo Hiv Hon) as Hii.
specialize (rngl_int_dom_or_inv_1_quo_and_eq_dec Hi1 Hed) as Hid.
destruct (Nat.eq_dec (rngl_characteristic T) 1) as [Hc1| Hc1]. {
  specialize (rngl_characteristic_1 Hon Hos Hc1) as H1.
  rewrite H1.
  apply H1.
}
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
assert (Ha12 : ∀ θ1 θ2, (0 ≤ (1 + rngl_cos θ1) * (1 + rngl_cos θ2))%L). {
  intros.
  apply (rngl_mul_nonneg_nonneg Hon Hos Hiq Hor). {
    apply (rngl_le_sub_le_add_l Hop Hor).
    progress unfold rngl_sub.
    rewrite Hop, rngl_add_0_l.
    apply rngl_cos_bound.
  } {
    apply (rngl_le_sub_le_add_l Hop Hor).
    progress unfold rngl_sub.
    rewrite Hop, rngl_add_0_l.
    apply rngl_cos_bound.
  }
}
assert (Hs12 : ∀ θ1 θ2, (0 ≤ (1 - rngl_cos θ1) * (1 - rngl_cos θ2))%L). {
  intros.
  apply (rngl_mul_nonneg_nonneg Hon Hos Hiq Hor). {
    apply (rngl_le_add_le_sub_l Hop Hor).
    rewrite rngl_add_0_r.
    apply rngl_cos_bound.
  } {
    apply (rngl_le_add_le_sub_l Hop Hor).
    rewrite rngl_add_0_r.
    apply rngl_cos_bound.
  }
}
specialize (rngl_0_lt_2 Hon Hos Hiq Hc1 Hor) as Hz2.
specialize (rngl_2_neq_0 Hon Hos Hiq Hc1 Hor) as H20.
assert (Hze2 : (0 ≤ 2)%L) by now apply (rngl_lt_le_incl Hor).
assert (Hs2z : (√2 ≠ 0)%L). {
  intros H.
  apply (f_equal rngl_squ) in H.
  rewrite (rngl_squ_sqrt Hon) in H; [ | now apply (rngl_lt_le_incl Hor) ].
  now rewrite (rngl_squ_0 Hos) in H.
}
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
  apply rngl_add_cos_nonneg_sqrt_mul_le.
  destruct (rngl_le_dec Hor 0 (rngl_cos θ1)) as [Hzc1| Hzc1]. {
    now apply rngl_add_cos_nonneg_when_sin_nonneg.
  }
  destruct (rngl_le_dec Hor 0 (rngl_cos θ2)) as [Hzc2| Hzc2]. {
    rewrite angle_add_comm in Hzs3.
    rewrite rngl_add_comm.
    now apply rngl_add_cos_nonneg_when_sin_nonneg.
  }
  apply (rngl_nle_gt_iff Hor) in Hzc1, Hzc2.
  exfalso.
  apply rngl_nlt_ge in Hzs3.
  apply Hzs3; clear Hzs3.
  cbn.
  (* special case for sin θ2 = 0 *)
  destruct (rngl_eq_dec Heo (rngl_sin θ2) 0) as [H2z| H2z]. {
    rewrite H2z, (rngl_mul_0_r Hos), rngl_add_0_r.
    destruct (rngl_eq_dec Heo (rngl_sin θ1) 0) as [H1z| H1z]. {
      apply (eq_rngl_sin_0) in H2z, H1z.
      destruct H2z as [H2z| H2z]. {
        subst θ2.
        apply rngl_nle_gt in Hzc2.
        exfalso; apply Hzc2; clear Hzc2; cbn.
        apply (rngl_0_le_1 Hon Hos Hiq Hor).
      }
      destruct H12ns as [H12ns| H12ns]; [ | easy ].
      destruct H1z as [H1z| H1z]; [ | easy ].
      subst θ1 θ2.
      exfalso.
      apply rngl_nle_gt in Hzc1.
      apply Hzc1; clear Hzc1; cbn.
      apply (rngl_0_le_1 Hon Hos Hiq Hor).
    }
    apply (rngl_mul_pos_neg Hon Hop Hiq Hor); [ | easy ].
    apply (rngl_le_neq Hor).
    split; [ easy | ].
    now apply not_eq_sym.
  }
  rewrite rngl_add_comm.
  apply (rngl_add_neg_nonpos Hop Hor). {
    rewrite (rngl_mul_comm Hic).
    apply (rngl_mul_pos_neg Hon Hop Hiq Hor); [ | easy ].
    apply (rngl_le_neq Hor).
    split; [ easy | ].
    now apply not_eq_sym.
  }
  apply (rngl_mul_nonneg_nonpos Hon Hop Hiq Hor); [ easy | ].
  now apply (rngl_lt_le_incl Hor).
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
apply rngl_sin_nonneg_sin_nonneg_add_1_cos_add_sub.
apply rngl_leb_le in Hzs1, Hzs2.
congruence.
Qed.

Theorem rngl_sin_sub_anticomm :
  ∀ θ1 θ2, rngl_sin (θ1 - θ2) = (- rngl_sin (θ2 - θ1))%L.
Proof.
destruct_ac.
intros; cbn.
do 2 rewrite (rngl_mul_opp_r Hop).
do 2 rewrite (rngl_add_opp_r Hop).
rewrite (rngl_opp_sub_distr Hop).
rewrite (rngl_mul_comm Hic).
f_equal.
apply (rngl_mul_comm Hic).
Qed.

Theorem angle_sub_move_0_r : ∀ θ1 θ2, (θ1 - θ2)%A = 0%A ↔ θ1 = θ2.
Proof.
intros.
split; intros H12. {
  apply angle_sub_move_r in H12.
  now rewrite angle_add_0_l in H12.
} {
  apply angle_sub_move_r.
  now rewrite angle_add_0_l.
}
Qed.

Theorem rngl_sin_add_straight_l :
  ∀ θ, (rngl_sin (angle_straight + θ) = - rngl_sin θ)%L.
Proof.
destruct_ac.
intros; cbn.
rewrite (rngl_mul_0_l Hos).
rewrite rngl_add_0_l.
rewrite (rngl_mul_opp_l Hop).
f_equal.
apply (rngl_mul_1_l Hon).
Qed.

Theorem rngl_sin_sub_nonneg :
  ∀ θ1 θ2,
  (0 ≤ rngl_sin θ1)%L
  → (0 ≤ rngl_sin θ2)%L
  → (rngl_cos θ1 ≤ rngl_cos θ2)%L
  → (0 ≤ rngl_sin (θ1 - θ2))%L.
Proof.
destruct_ac.
intros * Hs1 Hs2 Hc12.
specialize rngl_sin_nonneg_cos_le_sin_le as H1.
specialize (H1 _ _ Hs1 Hs2 Hc12).
remember (0 ≤? rngl_cos θ1)%L as zc1 eqn:Hzc1.
symmetry in Hzc1.
destruct zc1. {
  apply rngl_leb_le in Hzc1; cbn.
  rewrite (rngl_mul_opp_r Hop).
  rewrite (rngl_add_opp_r Hop).
  apply (rngl_le_0_sub Hop Hor).
  rewrite (rngl_mul_comm Hic).
  now apply (rngl_mul_le_compat_nonneg Hon Hiq Hor).
} {
  apply (rngl_leb_gt Hor) in Hzc1.
  remember (0 ≤? rngl_cos θ2)%L as zc2 eqn:Hzc2.
  symmetry in Hzc2.
  destruct zc2; [ easy | ].
  apply (rngl_leb_gt Hor) in Hzc2; cbn.
  rewrite (rngl_mul_opp_r Hop).
  rewrite (rngl_add_opp_r Hop).
  apply (rngl_le_0_sub Hop Hor).
  rewrite (rngl_mul_comm Hic).
  apply (rngl_lt_le_incl Hor) in Hzc2.
  now apply (rngl_mul_le_compat_nonpos_nonneg Hon Hop Hiq Hor).
}
Qed.

Theorem rngl_sin_sub_nonneg_iff :
  ∀ θ1 θ2,
  (0 < rngl_sin θ1)%L
  → (0 ≤ rngl_sin θ2)%L
  → (rngl_cos θ1 ≤ rngl_cos θ2)%L
  ↔ (0 ≤ rngl_sin (θ1 - θ2))%L.
Proof.
destruct_ac.
destruct (Nat.eq_dec (rngl_characteristic T) 1) as [Hc1| Hc1]. {
  specialize (rngl_characteristic_1 Hon Hos Hc1) as H1.
  intros * Hs1 Hs2.
  do 2 rewrite (H1 (rngl_cos _)).
  now rewrite (H1 (rngl_sin _)).
}
intros * Hs1 Hs2.
split. {
  apply rngl_sin_sub_nonneg; try easy.
  now apply (rngl_lt_le_incl Hor).
}
intros Hs12.
apply (rngl_nlt_ge_iff Hor).
intros Hcc.
generalize Hcc; intros Hcc2.
apply (rngl_lt_le_incl Hor) in Hcc2.
specialize rngl_sin_nonneg_cos_le_sin_le as H1.
generalize Hs1; intros Hs1'.
apply (rngl_lt_le_incl Hor) in Hs1'.
specialize (H1 _ _ Hs2 Hs1' Hcc2).
remember (0 ≤? rngl_cos θ2)%L as zc2 eqn:Hzc2.
symmetry in Hzc2.
destruct zc2. {
  apply rngl_leb_le in Hzc2.
  rewrite rngl_sin_sub_anticomm in Hs12.
  apply (rngl_opp_nonneg_nonpos Hop Hor) in Hs12.
  apply rngl_nlt_ge in Hs12.
  apply Hs12; clear Hs12.
  apply (rngl_le_neq Hor).
  split; [ now apply rngl_sin_sub_nonneg | ].
  intros H; symmetry in H.
  apply eq_rngl_sin_0 in H.
  destruct H as [H| H]. {
    apply -> angle_sub_move_0_r in H.
    subst θ2.
    now apply (rngl_lt_irrefl Hor) in Hcc.
  }
  apply angle_sub_move_r in H.
  subst θ2.
  rewrite rngl_sin_add_straight_l in Hs2.
  apply (rngl_opp_nonneg_nonpos Hop Hor) in Hs2.
  now apply rngl_nle_gt in Hs1.
}
apply (rngl_leb_gt Hor) in Hzc2.
remember (0 ≤? rngl_cos θ1)%L as zc1 eqn:Hzc1.
symmetry in Hzc1.
destruct zc1. {
  apply rngl_leb_le in Hzc1.
  rewrite rngl_sin_sub_anticomm in Hs12.
  apply (rngl_opp_nonneg_nonpos Hop Hor) in Hs12.
  apply (rngl_le_antisymm Hor) in H1; [ | easy ].
  apply eq_rngl_sin_0 in H1.
  destruct H1. {
    apply -> angle_sub_move_0_r in H.
    subst θ2.
    now apply (rngl_lt_irrefl Hor) in Hcc.
  }
  apply angle_sub_move_r in H.
  subst θ2.
  rewrite rngl_sin_add_straight_l in Hs2.
  apply (rngl_opp_nonneg_nonpos Hop Hor) in Hs2.
  now apply rngl_nle_gt in Hs1.
}
apply (rngl_leb_gt Hor) in Hzc1.
rewrite rngl_sin_sub_anticomm in Hs12.
apply (rngl_opp_nonneg_nonpos Hop Hor) in Hs12.
apply rngl_nlt_ge in Hs12.
apply Hs12; clear Hs12.
apply (rngl_le_neq Hor).
split; [ now apply rngl_sin_sub_nonneg | ].
intros H; symmetry in H.
apply eq_rngl_sin_0 in H.
destruct H as [H| H]. {
  apply -> angle_sub_move_0_r in H.
  subst θ2.
  now apply (rngl_lt_irrefl Hor) in Hcc.
}
apply angle_sub_move_r in H.
subst θ2.
rewrite rngl_sin_add_straight_l in Hs2.
apply (rngl_opp_nonneg_nonpos Hop Hor) in Hs2.
now apply rngl_nle_gt in Hs1.
Qed.

Theorem angle_opp_inj : ∀ θ1 θ2, (- θ1)%A = (- θ2)%A → θ1 = θ2.
Proof.
destruct_ac.
intros * H12.
progress unfold angle_opp in H12.
injection H12; clear H12; intros H1 H2.
apply (rngl_opp_inj Hop) in H1.
apply eq_angle_eq.
now rewrite H1, H2.
Qed.

Theorem rngl_characteristic_1_angle_0 :
  rngl_characteristic T = 1 →
  ∀ θ, (θ = 0)%A.
Proof.
destruct_ac.
intros Hc1 *.
specialize (rngl_characteristic_1 Hon Hos Hc1) as H1.
apply eq_angle_eq.
do 2 rewrite (H1 (rngl_cos _)).
now do 2 rewrite (H1 (rngl_sin _)).
Qed.

Theorem rngl_add_cos_neg_when_sin_nonneg_neg :
  ∀ θ1 θ2,
  (0 ≤ rngl_sin θ1)%L
  → (0 ≤ rngl_sin θ2)%L
  → (rngl_sin (θ1 + θ2) < 0)%L
  → (0 ≤ rngl_cos θ1)%L
  → (rngl_cos θ1 + rngl_cos θ2 < 0)%L.
Proof.
destruct_ac.
intros * Hzs1 Hzs2 Hs3z Hzc1.
specialize (rngl_has_inv_and_1_has_inv_and_1_or_pdiv Hon Hiv) as Hi1.
specialize (rngl_int_dom_or_inv_1_quo Hiv Hon) as Hii.
specialize (rngl_int_dom_or_inv_1_quo_and_eq_dec Hi1 Hed) as Hid.
destruct (Nat.eq_dec (rngl_characteristic T) 1) as [Hc1| Hc1]. {
  specialize (rngl_characteristic_1 Hon Hos Hc1) as H1.
  rewrite (H1 (rngl_sin _)) in Hs3z.
  now apply (rngl_lt_irrefl Hor) in Hs3z.
}
remember (θ1 + θ2)%A as θ3 eqn:Hθ3.
destruct (rngl_le_dec Hor 0 (rngl_cos θ2)) as [Hzc2| Hzc2]. {
  apply rngl_nle_gt in Hs3z.
  exfalso; apply Hs3z; clear Hs3z.
  rewrite Hθ3; cbn.
  apply (rngl_le_0_add Hos Hor). {
    now apply (rngl_mul_nonneg_nonneg Hon Hos Hiq Hor).
  } {
    now apply (rngl_mul_nonneg_nonneg Hon Hos Hiq Hor).
  }
}
apply (rngl_nle_gt_iff Hor) in Hzc2.
apply (rngl_nle_gt_iff Hor).
intros Hcc.
assert (Hs21 : (rngl_sin θ1 ≤ rngl_sin θ2)%L). {
  remember (angle_straight - θ2)%A as θ eqn:Hθ.
  symmetry in Hθ.
  apply angle_sub_move_l in Hθ.
  subst θ2; rename θ into θ2.
  move θ2 before θ1.
  rewrite rngl_cos_sub_straight_l in Hcc, Hzc2.
  rewrite rngl_sin_sub_straight_l in Hzs2 |-*.
  rewrite (rngl_add_opp_r Hop) in Hcc.
  apply -> (rngl_le_0_sub Hop Hor) in Hcc.
  apply (rngl_opp_neg_pos Hop Hor) in Hzc2.
  move Hzc2 before Hzc1.
  apply (rngl_lt_le_incl Hor) in Hzc2.
  now apply rngl_cos_cos_sin_sin_nonneg_sin_le_cos_le_iff.
}
apply rngl_nle_gt in Hs3z.
apply Hs3z; clear Hs3z.
rewrite Hθ3; cbn.
rewrite rngl_add_comm.
replace (rngl_cos θ1) with (rngl_cos θ1 + rngl_cos θ2 - rngl_cos θ2)%L. 2: {
  apply (rngl_add_sub Hos).
}
rewrite (rngl_mul_sub_distr_r Hop).
rewrite <- (rngl_sub_sub_distr Hop).
rewrite (rngl_mul_comm Hic (rngl_cos θ2)).
rewrite <- (rngl_mul_sub_distr_r Hop).
progress unfold rngl_sub at 1.
rewrite Hop.
rewrite <- (rngl_mul_opp_r Hop).
(* ok, all terms are non negative *)
apply (rngl_le_0_add Hos Hor). {
  now apply (rngl_mul_nonneg_nonneg Hon Hos Hiq Hor).
}
apply (rngl_mul_nonneg_nonneg Hon Hos Hiq Hor). {
  now apply (rngl_le_0_sub Hop Hor).
} {
  apply (rngl_opp_nonneg_nonpos Hop Hor).
  now apply (rngl_lt_le_incl Hor).
}
Qed.

Theorem rngl_cos_opp : ∀ θ, rngl_cos (- θ) = rngl_cos θ.
Proof. easy. Qed.

Theorem rngl_sin_opp : ∀ θ, rngl_sin (- θ) = (- rngl_sin θ)%L.
Proof. easy. Qed.

Theorem rngl_add_cos_nonneg_when_sin_nonpos :
  ∀ θ1 θ2,
  (rngl_sin θ1 ≤ 0)%L
  → (rngl_sin θ2 ≤ 0)%L
  → (rngl_sin (θ1 + θ2) ≤ 0)%L
  → (0 ≤ rngl_cos θ1)%L
  → (0 ≤ rngl_cos θ1 + rngl_cos θ2)%L.
Proof.
destruct_ac.
intros * Hzs1 Hzs2 Hzs3 Hzc1.
rewrite <- rngl_cos_opp.
rewrite <- (rngl_cos_opp θ2).
apply rngl_add_cos_nonneg_when_sin_nonneg. {
  rewrite rngl_sin_opp.
  now apply (rngl_opp_nonneg_nonpos Hop Hor).
} {
  rewrite rngl_sin_opp.
  now apply (rngl_opp_nonneg_nonpos Hop Hor).
} {
  rewrite angle_add_opp_r.
  rewrite <- angle_opp_add_distr.
  rewrite rngl_sin_opp.
  apply (rngl_opp_nonneg_nonpos Hop Hor).
  now rewrite angle_add_comm.
} {
  now rewrite rngl_cos_opp.
}
Qed.

Theorem rngl_sin_add_straight_r :
  ∀ θ, (rngl_sin (θ + angle_straight) = - rngl_sin θ)%L.
Proof.
destruct_ac.
intros; cbn.
rewrite (rngl_mul_0_r Hos).
rewrite rngl_add_0_r.
rewrite (rngl_mul_opp_r Hop).
f_equal.
apply (rngl_mul_1_r Hon).
Qed.

Theorem rngl_sin_sub_nonneg_sin_le_sin :
  ∀ θ1 θ2,
  (0 ≤ rngl_sin θ1)%L
  → (0 ≤ rngl_cos θ1)%L
  → (0 ≤ rngl_sin (θ1 - θ2))%L
  → (rngl_sin θ2 ≤ rngl_sin θ1)%L.
Proof.
destruct_ac; intros * Hzs1 Hcs1 Hzs12.
cbn in Hzs12.
rewrite rngl_add_comm in Hzs12.
rewrite (rngl_mul_opp_r Hop) in Hzs12.
rewrite (rngl_add_opp_l Hop) in Hzs12.
apply -> (rngl_le_0_sub Hop Hor) in Hzs12.
apply (rngl_mul_le_mono_nonneg_l Hon Hop Hiq Hor (rngl_cos θ1)) in Hzs12;
  [ | easy ].
rewrite rngl_mul_assoc in Hzs12.
rewrite fold_rngl_squ in Hzs12.
specialize (cos2_sin2_1 θ1) as H1.
apply (rngl_add_move_r Hop) in H1.
rewrite H1 in Hzs12; clear H1.
rewrite (rngl_mul_sub_distr_r Hop) in Hzs12.
rewrite (rngl_mul_1_l Hon) in Hzs12.
apply (rngl_le_sub_le_add_r Hop Hor) in Hzs12.
rewrite (rngl_mul_comm Hic) in Hzs12.
progress unfold rngl_squ in Hzs12.
do 2 rewrite <- rngl_mul_assoc in Hzs12.
rewrite <- rngl_mul_add_distr_l in Hzs12.
rewrite (rngl_mul_comm Hic (rngl_cos θ2)) in Hzs12.
rewrite <- rngl_cos_sub in Hzs12.
eapply (rngl_le_trans Hor); [ apply Hzs12 | ].
apply (rngl_le_0_sub Hop Hor).
rewrite (rngl_sub_mul_r_diag_l Hon Hop).
apply (rngl_mul_nonneg_nonneg Hon Hos Hiq Hor); [ easy | ].
apply (rngl_le_0_sub Hop Hor).
apply rngl_cos_bound.
Qed.

Theorem rngl_sin_nonneg_sin_nonneg_add_1_cos_add_add :
  ∀ θ1 θ2,
  (0 ≤? rngl_sin θ1)%L = (0 ≤? rngl_sin θ2)%L
  → ((1 + rngl_cos (θ1 - θ2)) * 2)%L =
      (√((1 + rngl_cos θ1) * (1 + rngl_cos θ2)) +
       √((1 - rngl_cos θ1) * (1 - rngl_cos θ2)))²%L.
Proof.
intros * Hzs12.
(* proof borrowed from rngl_sin_nonneg_sin_nonneg_add_1_cos_add_sub
   and it works: perhaps there is a way to unify these two theorems *)
destruct_ac.
assert (Ha12 : ∀ θ1 θ2, (0 ≤ (1 + rngl_cos θ1) * (1 + rngl_cos θ2))%L). {
  intros.
  apply (rngl_mul_nonneg_nonneg Hon Hos Hiq Hor). {
    apply (rngl_le_sub_le_add_l Hop Hor).
    progress unfold rngl_sub.
    rewrite Hop, rngl_add_0_l.
    apply rngl_cos_bound.
  } {
    apply (rngl_le_sub_le_add_l Hop Hor).
    progress unfold rngl_sub.
    rewrite Hop, rngl_add_0_l.
    apply rngl_cos_bound.
  }
}
assert (Hs12 : ∀ θ1 θ2, (0 ≤ (1 - rngl_cos θ1) * (1 - rngl_cos θ2))%L). {
  intros.
  apply (rngl_mul_nonneg_nonneg Hon Hos Hiq Hor). {
    apply (rngl_le_add_le_sub_l Hop Hor).
    rewrite rngl_add_0_r.
    apply rngl_cos_bound.
  } {
    apply (rngl_le_add_le_sub_l Hop Hor).
    rewrite rngl_add_0_r.
    apply rngl_cos_bound.
  }
}
rewrite (rngl_squ_add Hic Hon).
rewrite (rngl_squ_sqrt Hon); [ | easy ].
rewrite (rngl_squ_sqrt Hon); [ | easy ].
rewrite rngl_add_add_swap.
rewrite <- rngl_mul_assoc.
rewrite <- rl_sqrt_mul; [ | easy | easy ].
rewrite rngl_mul_assoc.
rewrite (rngl_mul_mul_swap Hic (1 + rngl_cos θ1))%L.
rewrite <- rngl_mul_assoc.
do 2 rewrite (rngl_squ_sub_squ' Hop).
do 2 rewrite (rngl_mul_1_r Hon), (rngl_mul_1_l Hon).
do 2 rewrite (rngl_add_sub Hos).
rewrite (rngl_squ_1 Hon).
replace (1 - (rngl_cos θ1)²)%L with (rngl_sin θ1)²%L. 2: {
  symmetry.
  apply (rngl_add_sub_eq_l Hos).
  apply (cos2_sin2_prop_add_squ).
  apply rngl_cos2_sin2.
}
replace (1 - (rngl_cos θ2)²)%L with (rngl_sin θ2)²%L. 2: {
  symmetry.
  apply (rngl_add_sub_eq_l Hos).
  apply (cos2_sin2_prop_add_squ).
  apply rngl_cos2_sin2.
}
rewrite rl_sqrt_mul; cycle 1. {
  apply (rngl_squ_nonneg Hon Hos Hiq Hor).
} {
  apply (rngl_squ_nonneg Hon Hos Hiq Hor).
}
do 2 rewrite (rl_sqrt_squ Hon Hop Hor).
rewrite (rngl_mul_add_distr_l (1 + rngl_cos θ1))%L.
rewrite (rngl_mul_1_r Hon).
rewrite (rngl_mul_add_distr_r 1 (rngl_cos θ1))%L.
rewrite (rngl_mul_1_l Hon).
rewrite (rngl_mul_sub_distr_l Hop (1 - rngl_cos θ1))%L.
rewrite (rngl_mul_1_r Hon).
rewrite (rngl_mul_sub_distr_r Hop 1 (rngl_cos θ1))%L.
rewrite (rngl_mul_1_l Hon).
rewrite rngl_add_assoc.
rewrite (rngl_add_sub_assoc Hop (1 + _ + _ + _ * _))%L.
rewrite (rngl_add_sub_assoc Hop _ 1 (rngl_cos θ1))%L.
rewrite (rngl_sub_sub_distr Hop _ (rngl_cos θ2)).
rewrite (rngl_add_add_swap (1 + _ + _))%L.
rewrite (rngl_add_add_swap _ (rngl_cos θ2) 1)%L.
rewrite (rngl_add_add_swap _ (rngl_cos θ1) 1)%L.
rewrite (rngl_add_sub_swap Hop _ _ (rngl_cos θ1)).
rewrite (rngl_add_sub_swap Hop _ _ (rngl_cos θ1)).
rewrite (rngl_add_sub Hos).
rewrite (rngl_add_sub_swap Hop _ _ (rngl_cos θ2)).
rewrite (rngl_add_sub Hos).
rewrite <- (rngl_add_assoc 2)%L.
rewrite <- (rngl_mul_2_l Hon (rngl_cos θ1 * _)%L).
rewrite (rngl_add_mul_r_diag_l Hon).
rewrite <- rngl_mul_add_distr_l.
rewrite (rngl_mul_comm Hic).
f_equal.
rewrite <- rngl_add_assoc.
f_equal; cbn.
rewrite (rngl_mul_opp_r Hop).
rewrite (rngl_sub_opp_r Hop).
f_equal.
remember (0 ≤? rngl_sin θ2)%L as zs2 eqn:Hzs2.
symmetry in Hzs2.
destruct zs2. {
  apply rngl_leb_le in Hzs2, Hzs12.
  rewrite (rngl_abs_nonneg_eq Hop Hor); [ | easy ].
  rewrite (rngl_abs_nonneg_eq Hop Hor); [ | easy ].
  easy.
} {
  apply (rngl_leb_gt Hor) in Hzs2, Hzs12.
  apply (rngl_lt_le_incl Hor) in Hzs2, Hzs12.
  rewrite (rngl_abs_nonpos_eq Hop Hor); [ | easy ].
  rewrite (rngl_abs_nonpos_eq Hop Hor); [ | easy ].
  rewrite (rngl_mul_opp_l Hop).
  rewrite (rngl_mul_opp_r Hop).
  symmetry.
  apply (rngl_opp_involutive Hop).
}
Qed.

Theorem rngl_sin_nonneg_sin_neg_sin_add_neg :
  ∀ θ1 θ2,
  (0 ≤ rngl_sin θ1)%L
  → (rngl_sin θ2 ≤ 0)%L
  → √((1 + rngl_cos (θ1 + θ2)) / 2)%L =
     (√((1 - rngl_cos θ1) / 2) * √((1 - rngl_cos θ2) / 2) +
      √((1 + rngl_cos θ1) / 2) * √((1 + rngl_cos θ2) / 2))%L.
Proof.
intros * Hzs1 Hzs2.
destruct_ac.
specialize (rngl_has_inv_and_1_has_inv_and_1_or_pdiv Hon Hiv) as Hi1.
specialize (rngl_int_dom_or_inv_1_quo_and_eq_dec Hi1 Hed) as Hid.
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
assert (Ha12 : ∀ θ1 θ2, (0 ≤ (1 + rngl_cos θ1) * (1 + rngl_cos θ2))%L). {
  intros.
  apply (rngl_mul_nonneg_nonneg Hon Hos Hiq Hor). {
    apply (rngl_le_sub_le_add_l Hop Hor).
    progress unfold rngl_sub.
    rewrite Hop, rngl_add_0_l.
    apply rngl_cos_bound.
  } {
    apply (rngl_le_sub_le_add_l Hop Hor).
    progress unfold rngl_sub.
    rewrite Hop, rngl_add_0_l.
    apply rngl_cos_bound.
  }
}
assert (Hs12 : ∀ θ1 θ2, (0 ≤ (1 - rngl_cos θ1) * (1 - rngl_cos θ2))%L). {
  intros.
  apply (rngl_mul_nonneg_nonneg Hon Hos Hiq Hor). {
    apply (rngl_le_add_le_sub_l Hop Hor).
    rewrite rngl_add_0_r.
    apply rngl_cos_bound.
  } {
    apply (rngl_le_add_le_sub_l Hop Hor).
    rewrite rngl_add_0_r.
    apply rngl_cos_bound.
  }
}
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
rewrite <- (rngl_div_add_distr_r Hiv).
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
rewrite <- (rngl_abs_nonneg_eq Hop Hor). 2: {
  now apply (rngl_le_0_add Hos Hor); apply rl_sqrt_nonneg.
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
rewrite <- (rngl_squ_opp Hop).
rewrite (rngl_squ_opp Hop).
rewrite (rngl_add_comm (√_))%L.
remember (- θ2)%A as θ eqn:Hθ.
symmetry in Hθ.
rewrite <- angle_opp_involutive in Hθ.
apply angle_opp_inj in Hθ.
subst θ2; rename θ into θ2.
move θ2 before θ1.
rewrite rngl_sin_opp in Hzs2.
rewrite <- (rngl_opp_0 Hop) in Hzs2.
apply (rngl_opp_le_compat Hop Hor) in Hzs2.
rewrite angle_add_opp_r.
rewrite rngl_cos_opp.
apply rngl_sin_nonneg_sin_nonneg_add_1_cos_add_add.
apply rngl_leb_le in Hzs1, Hzs2.
congruence.
Qed.

Theorem angle_add_add_swap : ∀ θ1 θ2 θ3, (θ1 + θ2 + θ3)%A = (θ1 + θ3 + θ2)%A.
Proof.
intros.
do 2 rewrite <- angle_add_assoc.
f_equal.
apply angle_add_comm.
Qed.

Theorem angle_sub_sub_swap : ∀ θ1 θ2 θ3, (θ1 - θ2 - θ3 = θ1 - θ3 - θ2)%A.
Proof.
intros.
progress unfold angle_sub.
apply angle_add_add_swap.
Qed.

Theorem rngl_sin_nonneg_sin_nonneg_add_cos_nonneg :
  ∀ θ1 θ2,
  (0 ≤ rngl_sin θ1)%L
  → (0 ≤ rngl_sin θ2)%L
  → (0 ≤ rngl_cos θ1 + rngl_cos θ2)%L
  → √((1 + rngl_cos (θ1 + θ2)) / 2)%L =
    (√((1 + rngl_cos θ1) / 2) * √((1 + rngl_cos θ2) / 2) -
     √((1 - rngl_cos θ1) / 2) * √((1 - rngl_cos θ2) / 2))%L.
Proof.
intros * Hzs1 Hzs2 Hzc12.
destruct_ac.
specialize (rngl_has_inv_and_1_has_inv_and_1_or_pdiv Hon Hiv) as Hi1.
specialize (rngl_int_dom_or_inv_1_quo Hiv Hon) as Hii.
specialize (rngl_int_dom_or_inv_1_quo_and_eq_dec Hi1 Hed) as Hid.
destruct (Nat.eq_dec (rngl_characteristic T) 1) as [Hc1| Hc1]. {
  specialize (rngl_characteristic_1 Hon Hos Hc1) as H1.
  rewrite H1.
  apply H1.
}
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
assert (Ha12 : ∀ θ1 θ2, (0 ≤ (1 + rngl_cos θ1) * (1 + rngl_cos θ2))%L). {
  intros.
  apply (rngl_mul_nonneg_nonneg Hon Hos Hiq Hor). {
    apply (rngl_le_sub_le_add_l Hop Hor).
    progress unfold rngl_sub.
    rewrite Hop, rngl_add_0_l.
    apply rngl_cos_bound.
  } {
    apply (rngl_le_sub_le_add_l Hop Hor).
    progress unfold rngl_sub.
    rewrite Hop, rngl_add_0_l.
    apply rngl_cos_bound.
  }
}
assert (Hs12 : ∀ θ1 θ2, (0 ≤ (1 - rngl_cos θ1) * (1 - rngl_cos θ2))%L). {
  intros.
  apply (rngl_mul_nonneg_nonneg Hon Hos Hiq Hor). {
    apply (rngl_le_add_le_sub_l Hop Hor).
    rewrite rngl_add_0_r.
    apply rngl_cos_bound.
  } {
    apply (rngl_le_add_le_sub_l Hop Hor).
    rewrite rngl_add_0_r.
    apply rngl_cos_bound.
  }
}
specialize (rngl_0_lt_2 Hon Hos Hiq Hc1 Hor) as Hz2.
specialize (rngl_2_neq_0 Hon Hos Hiq Hc1 Hor) as H20.
assert (Hze2 : (0 ≤ 2)%L) by now apply (rngl_lt_le_incl Hor).
assert (Hs2z : (√2 ≠ 0)%L). {
  intros H.
  apply (f_equal rngl_squ) in H.
  rewrite (rngl_squ_sqrt Hon) in H; [ | now apply (rngl_lt_le_incl Hor) ].
  now rewrite (rngl_squ_0 Hos) in H.
}
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
rewrite <- (rngl_abs_nonneg_eq Hop Hor). 2: {
  apply (rngl_le_0_sub Hop Hor).
  now apply rngl_add_cos_nonneg_sqrt_mul_le.
}
apply (eq_rngl_squ_rngl_abs Hop Hor Hii). {
  apply (rngl_mul_comm Hic).
}
rewrite (rngl_squ_mul Hic).
rewrite (rngl_squ_div Hic Hon Hos Hiv); [ | easy ].
rewrite (rngl_squ_sqrt Hon); [ | easy ].
rewrite (rngl_squ_sqrt Hon); [ | easy ].
progress unfold rngl_squ at 1.
rewrite rngl_mul_assoc.
rewrite (rngl_div_mul Hon Hiv); [ | easy ].
rewrite <- (rngl_squ_opp Hop).
rewrite (rngl_squ_opp Hop).
rewrite (rngl_squ_sub Hop Hic Hon).
rewrite (rngl_squ_sqrt Hon); [ | easy ].
rewrite (rngl_squ_sqrt Hon); [ | easy ].
rewrite <- (rngl_add_sub_swap Hop).
rewrite <- rngl_mul_assoc.
rewrite <- rl_sqrt_mul; [ | easy | easy ].
rewrite rngl_mul_assoc.
rewrite (rngl_mul_mul_swap Hic (1 + rngl_cos θ1))%L.
rewrite <- rngl_mul_assoc.
do 2 rewrite (rngl_squ_sub_squ' Hop).
do 2 rewrite (rngl_mul_1_r Hon), (rngl_mul_1_l Hon).
do 2 rewrite (rngl_add_sub Hos).
rewrite (rngl_squ_1 Hon).
replace (1 - (rngl_cos θ1)²)%L with (rngl_sin θ1)²%L. 2: {
  symmetry.
  apply (rngl_add_sub_eq_l Hos).
  apply (cos2_sin2_prop_add_squ).
  apply rngl_cos2_sin2.
}
replace (1 - (rngl_cos θ2)²)%L with (rngl_sin θ2)²%L. 2: {
  symmetry.
  apply (rngl_add_sub_eq_l Hos).
  apply (cos2_sin2_prop_add_squ).
  apply rngl_cos2_sin2.
}
rewrite rl_sqrt_mul; cycle 1. {
  apply (rngl_squ_nonneg Hon Hos Hiq Hor).
} {
  apply (rngl_squ_nonneg Hon Hos Hiq Hor).
}
do 2 rewrite (rl_sqrt_squ Hon Hop Hor).
rewrite (rngl_mul_add_distr_l (1 + rngl_cos θ1))%L.
rewrite (rngl_mul_1_r Hon).
rewrite (rngl_mul_add_distr_r 1 (rngl_cos θ1))%L.
rewrite (rngl_mul_1_l Hon).
rewrite (rngl_mul_sub_distr_l Hop (1 - rngl_cos θ1))%L.
rewrite (rngl_mul_1_r Hon).
rewrite (rngl_mul_sub_distr_r Hop 1 (rngl_cos θ1))%L.
rewrite (rngl_mul_1_l Hon).
rewrite rngl_add_assoc.
rewrite (rngl_add_sub_assoc Hop (1 + _ + _ + _ * _))%L.
rewrite (rngl_add_sub_assoc Hop _ 1 (rngl_cos θ1))%L.
rewrite (rngl_sub_sub_distr Hop _ (rngl_cos θ2)).
rewrite (rngl_add_add_swap (1 + _ + _))%L.
rewrite (rngl_add_add_swap _ (rngl_cos θ2) 1)%L.
rewrite (rngl_add_add_swap _ (rngl_cos θ1) 1)%L.
rewrite (rngl_add_sub_swap Hop _ _ (rngl_cos θ1)).
rewrite (rngl_add_sub_swap Hop _ _ (rngl_cos θ1)).
rewrite (rngl_add_sub Hos).
rewrite (rngl_add_sub_swap Hop _ _ (rngl_cos θ2)).
rewrite (rngl_add_sub Hos).
rewrite <- (rngl_add_assoc 2)%L.
rewrite <- (rngl_mul_2_l Hon (rngl_cos θ1 * _)%L).
rewrite (rngl_add_mul_r_diag_l Hon).
rewrite <- (rngl_mul_sub_distr_l Hop).
rewrite (rngl_mul_comm Hic).
f_equal.
rewrite <- (rngl_add_sub_assoc Hop).
f_equal; cbn.
progress unfold rngl_sub.
rewrite Hop.
f_equal.
f_equal.
rewrite (rngl_abs_nonneg_eq Hop Hor); [ | easy ].
rewrite (rngl_abs_nonneg_eq Hop Hor); [ | easy ].
easy.
Qed.

Theorem rngl_sin_sub_right_l :
  ∀ θ, rngl_sin (angle_right - θ) = rngl_cos θ.
Proof.
destruct_ac.
intros; cbn.
rewrite (rngl_mul_0_l Hos).
rewrite rngl_add_0_r.
apply (rngl_mul_1_l Hon).
Qed.

Theorem rngl_sin_sub_right_r :
  ∀ θ, rngl_sin (θ - angle_right) = (- rngl_cos θ)%L.
Proof.
destruct_ac.
intros; cbn.
rewrite (rngl_mul_0_r Hos).
rewrite rngl_add_0_l.
rewrite (rngl_mul_opp_r Hop).
f_equal.
apply (rngl_mul_1_r Hon).
Qed.

Theorem rngl_cos_sub_right_r :
  ∀ θ, rngl_cos (θ - angle_right) = rngl_sin θ.
Proof.
destruct_ac.
intros; cbn.
rewrite (rngl_mul_0_r Hos).
rewrite (rngl_sub_0_l Hop).
rewrite (rngl_mul_opp_r Hop).
rewrite (rngl_opp_involutive Hop).
apply (rngl_mul_1_r Hon).
Qed.

Theorem rngl_cos_sub_right_l :
  ∀ θ, rngl_cos (angle_right - θ) = rngl_sin θ.
Proof.
destruct_ac.
intros; cbn.
rewrite (rngl_mul_0_l Hos).
rewrite (rngl_mul_1_l Hon).
rewrite (rngl_sub_opp_r Hop).
apply rngl_add_0_l.
Qed.

Theorem rngl_cos_sub_comm : ∀ θ1 θ2, rngl_cos (θ1 - θ2) = rngl_cos (θ2 - θ1).
Proof.
destruct_ac.
intros; cbn.
rewrite (rngl_mul_comm Hic).
f_equal.
do 2 rewrite (rngl_mul_opp_r Hop).
f_equal.
apply (rngl_mul_comm Hic).
Qed.

Theorem angle_sub_opp_r : ∀ θ1 θ2, (θ1 - - θ2)%A = (θ1 + θ2)%A.
Proof.
destruct_ac.
intros.
apply eq_angle_eq; cbn.
now rewrite (rngl_opp_involutive Hop).
Qed.

Theorem angle_add_sub_swap : ∀ θ1 θ2 θ3, (θ1 + θ2 - θ3 = θ1 - θ3 + θ2)%A.
Proof.
intros.
apply angle_add_add_swap.
Qed.

Theorem angle_add_sub_assoc : ∀ θ1 θ2 θ3, (θ1 + (θ2 - θ3) = θ1 + θ2 - θ3)%A.
Proof.
intros.
progress unfold angle_sub.
apply angle_add_assoc.
Qed.

Theorem rngl_cos_lt_cos_sub :
  ∀ θ1 θ2,
  (0 ≤ rngl_sin θ1)%L
  → (0 < rngl_sin θ2)%L
  → (rngl_cos θ1 ≤ rngl_cos θ2)%L
  → (rngl_cos θ1 < rngl_cos (θ2 - θ1))%L.
Proof.
destruct_ac.
specialize (rngl_has_eq_dec_or_is_ordered_r Hor) as Heo.
intros * Hzs1 Hzs2 Hc12z.
specialize (rngl_int_dom_or_inv_1_quo Hiv Hon) as Hii.
specialize (rngl_has_inv_and_1_has_inv_and_1_or_pdiv Hon Hiv) as Hi1.
specialize (rngl_int_dom_or_inv_1_quo_and_eq_dec Hi1 Hed) as Hid.
destruct (Nat.eq_dec (rngl_characteristic T) 1) as [Hc1| Hc1]. {
  specialize (rngl_characteristic_1 Hon Hos Hc1) as H1.
  rewrite H1 in Hzs2.
  now apply (rngl_lt_irrefl Hor) in Hzs2.
}
specialize (rngl_0_lt_2 Hon Hos Hiq Hc1 Hor) as Hz2.
assert (Hze2 : (0 ≤ 2)%L) by now apply (rngl_lt_le_incl Hor).
cbn.
rewrite (rngl_mul_opp_r Hop).
rewrite (rngl_sub_opp_r Hop).
rewrite (rngl_mul_comm Hic (rngl_cos θ2)).
rewrite (rngl_mul_comm Hic (rngl_sin θ2)).
apply (rngl_lt_sub_lt_add_l Hop Hor).
rewrite (rngl_sub_mul_r_diag_l Hon Hop).
rewrite <- (rngl_abs_nonneg_eq Hop Hor). 2: {
  apply (rngl_lt_le_incl Hor) in Hzs2.
  now apply (rngl_mul_nonneg_nonneg Hon Hos Hiq Hor).
}
destruct (rngl_lt_dec Hor (rngl_cos θ1) 0) as [Hc1z| Hzc1]. {
  destruct (rngl_eq_dec Heo (rngl_cos θ2) 1) as [Hc21| Hc21]. {
    apply eq_rngl_cos_1 in Hc21.
    subst θ2.
    now apply (rngl_lt_irrefl Hor) in Hzs2.
  }
  apply (rngl_lt_le_trans Hor _ 0). {
    rewrite (rngl_mul_comm Hic).
    apply (rngl_mul_pos_neg Hon Hop Hiq Hor); [ | easy ].
    apply (rngl_lt_0_sub Hop Hor).
    apply (rngl_le_neq Hor).
    split; [ apply rngl_cos_bound | easy ].
  }
  apply (rngl_abs_nonneg Hop Hor).
}
apply (rngl_nlt_ge_iff Hor) in Hzc1.
rewrite <- (rngl_abs_nonneg_eq Hop Hor (rngl_cos θ1 * _))%L. 2: {
  apply (rngl_mul_nonneg_nonneg Hon Hos Hiq Hor); [ easy | ].
  apply (rngl_le_0_sub Hop Hor).
  apply rngl_cos_bound.
}
apply (rngl_squ_lt_abs_lt Hon Hop Hiq Hor).
rewrite (rngl_squ_mul Hic (rngl_sin _)).
specialize (cos2_sin2_1 θ1) as H1.
apply (rngl_add_move_l Hop) in H1.
rewrite H1; clear H1.
specialize (cos2_sin2_1 θ2) as H1.
apply (rngl_add_move_l Hop) in H1.
rewrite H1; clear H1.
rewrite (rngl_mul_sub_distr_r Hop).
rewrite (rngl_mul_1_l Hon).
rewrite (rngl_squ_mul Hic).
apply (rngl_lt_add_lt_sub_l Hop Hor).
rewrite <- rngl_mul_add_distr_l.
rewrite (rngl_squ_sub Hop Hic Hon).
rewrite (rngl_squ_1 Hon).
rewrite (rngl_mul_1_r Hon).
rewrite rngl_add_assoc.
rewrite (rngl_add_sub_assoc Hop).
rewrite <- (rngl_add_sub_swap Hop 1)%L.
rewrite <- (rngl_add_sub_swap Hop).
rewrite (rngl_sub_add Hop).
rewrite (rngl_sub_mul_r_diag_l Hon Hop).
rewrite rngl_mul_assoc.
rewrite (rngl_mul_comm Hic _ 2)%L.
rewrite <- (rngl_squ_1 Hon) at 4.
rewrite (rngl_squ_sub_squ Hop).
rewrite (rngl_mul_1_r Hon), (rngl_mul_1_l Hon).
rewrite (rngl_add_sub Hos).
apply (rngl_mul_lt_mono_pos_r Hon Hop Hiq Hor). {
  apply (rngl_lt_0_sub Hop Hor).
  apply (rngl_le_neq Hor).
  split; [ now apply rngl_cos_bound | ].
  intros H.
  apply (eq_rngl_cos_1) in H.
  subst θ2.
  now apply (rngl_lt_irrefl Hor) in Hzs2.
}
apply (rngl_le_lt_trans Hor _ (2 * (rngl_cos θ2)²))%L. {
  apply (rngl_mul_le_mono_pos_l Hon Hop Hiq Hor); [ easy | ].
  apply (rngl_abs_le_squ_le Hon Hop Hiq Hor).
  rewrite (rngl_abs_nonneg_eq Hop Hor); [ | easy ].
  rewrite (rngl_abs_nonneg_eq Hop Hor). 2: {
    now apply (rngl_le_trans Hor _ (rngl_cos θ1)).
  }
  easy.
}
apply (rngl_le_lt_trans Hor _ (2 * rngl_cos θ2))%L. {
  apply (rngl_mul_le_mono_nonneg_l Hon Hop Hiq Hor); [ easy | ].
  rewrite <- (rngl_mul_1_l Hon (rngl_cos θ2)) at 2.
  progress unfold rngl_squ.
  apply (rngl_mul_le_mono_nonneg_r Hon Hop Hiq Hor). {
    now apply (rngl_le_trans Hor _ (rngl_cos θ1)).
  }
  now apply rngl_cos_bound.
}
rewrite (rngl_mul_2_l Hon).
apply (rngl_add_lt_mono_r Hos Hor).
apply (rngl_le_neq Hor).
split; [ now apply rngl_cos_bound | ].
intros H.
apply eq_rngl_cos_1 in H.
subst θ2.
now apply (rngl_lt_irrefl Hor) in Hzs2.
Qed.

Theorem rngl_cos_le_cos_sub :
  ∀ θ1 θ2,
  (0 ≤ rngl_sin θ1)%L
  → (0 ≤ rngl_sin θ2)%L
  → (rngl_cos θ1 ≤ rngl_cos θ2)%L
  → (rngl_cos θ1 ≤ rngl_cos (θ2 - θ1))%L.
Proof.
destruct_ac.
specialize (rngl_has_eq_dec_or_is_ordered_r Hor) as Heo.
intros * Hs1 Hs2 Hcc.
apply (rngl_lt_eq_cases Hor) in Hs2.
destruct Hs2 as [Hs2| Hs2]. {
  apply (rngl_lt_le_incl Hor).
  now apply rngl_cos_lt_cos_sub.
}
symmetry in Hs2.
apply eq_rngl_sin_0 in Hs2.
destruct Hs2; subst θ2. {
  rewrite angle_sub_0_l; cbn.
  apply (rngl_le_refl Hor).
}
rewrite rngl_cos_sub_straight_l.
cbn in Hcc.
apply (rngl_nlt_ge_iff Hor).
intros Hcc1.
apply (rngl_nlt_ge) in Hcc.
apply Hcc; clear Hcc.
apply (rngl_le_neq Hor).
split; [ apply rngl_cos_bound | ].
intros H; symmetry in H.
apply eq_rngl_cos_opp_1 in H; subst θ1.
apply rngl_nle_gt in Hcc1.
apply Hcc1; clear Hcc1; cbn.
rewrite (rngl_opp_involutive Hop).
apply (rngl_opp_1_le_1 Hon Hop Hiq Hor).
Qed.

Theorem angle_eqb_eq : ∀ θ1 θ2 : angle T, (θ1 =? θ2)%A = true ↔ θ1 = θ2.
Proof.
destruct_ac.
intros.
split; intros H12. {
  progress unfold angle_eqb in H12.
  apply Bool.andb_true_iff in H12.
  destruct H12 as (Hc12, Hs12).
  apply (rngl_eqb_eq Hed) in Hc12, Hs12.
  apply eq_angle_eq.
  now rewrite Hc12, Hs12.
} {
  subst θ2.
  progress unfold angle_eqb.
  now do 2 rewrite (rngl_eqb_refl Hed).
}
Qed.

Theorem angle_eqb_neq : ∀ θ1 θ2, (θ1 =? θ2)%A = false ↔ θ1 ≠ θ2.
Proof.
destruct_ac.
intros.
progress unfold angle_eqb.
split; intros H12. {
  intros H; subst θ2.
  now do 2 rewrite (rngl_eqb_refl Hed) in H12.
} {
  apply Bool.not_true_iff_false.
  intros H; apply H12; clear H12.
  apply eq_angle_eq; cbn.
  apply Bool.andb_true_iff in H.
  destruct H as (Hc, Hs).
  apply (rngl_eqb_eq Hed) in Hc, Hs.
  now rewrite Hc, Hs.
}
Qed.

Theorem angle_neqb_neq : ∀ θ1 θ2, (θ1 ≠? θ2)%A = true ↔ θ1 ≠ θ2.
Proof.
intros.
split; intros H12. {
  apply angle_eqb_neq.
  now apply Bool.negb_true_iff.
} {
  apply Bool.negb_true_iff.
  now apply angle_eqb_neq.
}
Qed.

Theorem angle_eq_dec : ∀ θ1 θ2 : angle T, {θ1 = θ2} + {θ1 ≠ θ2}.
Proof.
intros.
remember (θ1 =? θ2)%A as tt eqn:Htt.
symmetry in Htt.
destruct tt. {
  now left; apply angle_eqb_eq in Htt.
} {
  now right; apply angle_eqb_neq in Htt.
}
Qed.

Theorem angle_mul_add_distr_l :
  ∀ n θ1 θ2, (n * (θ1 + θ2) = n * θ1 + n * θ2)%A.
Proof.
intros.
induction n; cbn; [ symmetry; apply angle_add_0_l | ].
rewrite IHn.
do 2 rewrite angle_add_assoc.
f_equal.
do 2 rewrite <- angle_add_assoc.
f_equal.
apply angle_add_comm.
Qed.

Theorem angle_mul_add_distr_r :
  ∀ a b θ, ((a + b) * θ = a * θ + b * θ)%A.
Proof.
intros.
induction a; cbn; [ symmetry; apply angle_add_0_l | ].
rewrite IHa.
apply angle_add_assoc.
Qed.

Theorem angle_sub_add_distr :
  ∀ θ1 θ2 θ3, (θ1 - (θ2 + θ3))%A = (θ1 - θ2 - θ3)%A.
Proof.
intros.
progress unfold angle_sub.
rewrite angle_opp_add_distr.
progress unfold angle_sub.
rewrite angle_add_assoc.
apply angle_add_add_swap.
Qed.

Theorem angle_mul_sub_distr_l :
  ∀ n θ1 θ2, (n * (θ1 - θ2) = n * θ1 - n * θ2)%A.
Proof.
intros.
induction n; intros; cbn; [ symmetry; apply angle_sub_diag | ].
rewrite angle_sub_add_distr.
rewrite angle_add_sub_swap.
rewrite <- angle_add_sub_assoc.
f_equal.
apply IHn.
Qed.

Theorem angle_mul_sub_distr_r :
  ∀ a b θ, b ≤ a → ((a - b) * θ = a * θ - b * θ)%A.
Proof.
intros * Hba.
revert b Hba.
induction a; intros. {
  apply Nat.le_0_r in Hba; subst b; cbn.
  symmetry.
  apply angle_sub_diag.
}
destruct b; [ now rewrite angle_sub_0_r | ].
apply Nat.succ_le_mono in Hba.
rewrite Nat.sub_succ.
rewrite IHa; [ cbn | easy ].
rewrite angle_sub_add_distr.
rewrite angle_add_comm.
now rewrite angle_add_sub.
Qed.

Theorem fold_rl_sqrt : rl_nth_root 2 = rl_sqrt.
Proof. easy. Qed.

Theorem rngl_1_add_cos_div_2_nonneg : ∀ θ, (0 ≤ (1 + rngl_cos θ) / 2)%L.
Proof.
destruct_ac.
specialize (rngl_int_dom_or_inv_1_quo Hiv Hon) as Hii.
destruct (Nat.eq_dec (rngl_characteristic T) 1) as [Hc1| Hc1]. {
  specialize (rngl_characteristic_1 Hon Hos Hc1) as H1.
  intros.
  rewrite (H1 (_ / _))%L.
  apply (rngl_le_refl Hor).
}
intros.
apply (rngl_mul_le_mono_pos_r Hon Hop Hiq Hor) with (c := 2%L). {
  apply (rngl_0_lt_2 Hon Hos Hiq Hc1 Hor).
}
rewrite (rngl_mul_0_l Hos).
rewrite (rngl_div_mul Hon Hiv). 2: {
  apply (rngl_2_neq_0 Hon Hos Hiq Hc1 Hor).
}
apply (rngl_le_sub_le_add_l Hop Hor).
rewrite (rngl_sub_0_l Hop).
now apply rngl_cos_bound.
Qed.

Theorem rngl_1_sub_cos_div_2_nonneg : ∀ θ, (0 ≤ (1 - rngl_cos θ) / 2)%L.
Proof.
destruct_ac.
specialize (rngl_int_dom_or_inv_1_quo Hiv Hon) as Hii.
destruct (Nat.eq_dec (rngl_characteristic T) 1) as [Hc1| Hc1]. {
  specialize (rngl_characteristic_1 Hon Hos Hc1) as H1.
  intros.
  rewrite (H1 (_ / _))%L.
  apply (rngl_le_refl Hor).
}
intros.
apply (rngl_mul_le_mono_pos_r Hon Hop Hiq Hor) with (c := 2%L). {
  apply (rngl_0_lt_2 Hon Hos Hiq Hc1 Hor).
}
rewrite (rngl_mul_0_l Hos).
rewrite (rngl_div_mul Hon Hiv). 2: {
  apply (rngl_2_neq_0 Hon Hos Hiq Hc1 Hor).
}
apply (rngl_le_0_sub Hop Hor).
now apply rngl_cos_bound.
Qed.

Theorem angle_add_move_0_r : ∀ θ1 θ2, (θ1 + θ2 = 0 ↔ θ1 = (- θ2))%A.
Proof.
destruct_ac.
intros.
split; intros H12. {
  rewrite <- angle_sub_0_l.
  rewrite <- H12; symmetry.
  apply angle_add_sub.
} {
  subst θ1.
  rewrite angle_add_opp_l.
  apply angle_sub_diag.
}
Qed.

Theorem angle_opp_0 : (- 0)%A = 0%A.
Proof.
destruct_ac.
apply eq_angle_eq.
cbn; f_equal.
apply (rngl_opp_0 Hop).
Qed.

Theorem angle_opp_straight : (- angle_straight)%A = angle_straight.
Proof.
destruct_ac.
apply eq_angle_eq; cbn.
f_equal.
apply (rngl_opp_0 Hop).
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

Theorem rngl_acos_prop :
  ∀ x, (x² ≤ 1)%L → cos2_sin2_prop x √(1 - x²)%L.
Proof.
destruct_ac.
intros * Hx1.
progress unfold cos2_sin2_prop.
apply (rngl_eqb_eq Hed).
rewrite (rngl_squ_sqrt Hon). 2: {
  apply (rngl_le_add_le_sub_r Hop Hor).
  now rewrite rngl_add_0_l.
}
rewrite rngl_add_comm.
apply (rngl_sub_add Hop).
Qed.

Definition rngl_acos (x : T) :=
  match (rngl_le_dec ac_or x² 1)%L with
  | left Hx1 =>
      {| rngl_cos := x; rngl_sin := √(1 - x²)%L;
         rngl_cos2_sin2 := rngl_acos_prop x Hx1 |}
  | _ =>
      angle_zero
  end.

Arguments rngl_acos x%_L.

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

End a.

Arguments rngl_acos {T ro rp rl ac} x%_L.
