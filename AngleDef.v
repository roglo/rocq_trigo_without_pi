Set Nested Proofs Allowed.
From Stdlib Require Import Utf8 Arith.

Require Import RingLike.Core.
Require Import RingLike.RealLike.

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
Arguments angle_ctx T {ro rp}.
Arguments cos2_sin2_prop {T ro} (x y)%_L.
Arguments mk_angle {T ro} (rngl_cos rngl_sin)%_L.

Notation "rngl_cos² a" := ((rngl_cos a)²) (at level 10).
Notation "rngl_sin² a" := ((rngl_sin a)²) (at level 10).

Ltac destruct_ac :=
  set (Hic := ac_ic);
  set (Hon := ac_on);
  set (Hop := ac_op);
  set (Hiv := ac_iv);
  set (Hed := ac_ed);
  set (Hor := ac_or);
  specialize (rngl_has_opp_has_opp_or_psub Hop) as Hos;
  specialize (rngl_has_inv_has_inv_or_pdiv Hiv) as Hiq;
  specialize (rngl_int_dom_or_inv_1_quo Hiv Hon) as Hii;
  specialize (rngl_has_eq_dec_or_is_ordered_l Hed) as Heo;
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
apply (rngl_eqb_refl Heo).
Qed.

Theorem angle_right_prop : cos2_sin2_prop 0 1.
Proof.
destruct_ac.
progress unfold cos2_sin2_prop.
rewrite (rngl_squ_0 Hos).
rewrite (rngl_squ_1 Hon).
rewrite rngl_add_0_l.
apply (rngl_eqb_refl Heo).
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
apply (rngl_eqb_refl Heo).
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
apply (rngl_eqb_eq Heo) in Hxy'.
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
now apply (rngl_eqb_eq Heo) in Hcs.
Qed.

Theorem cos2_sin2_1 : ∀ θ, (rngl_cos² θ + rngl_sin² θ = 1)%L.
Proof.
destruct_ac.
intros.
destruct θ as (c, s, Hcs); cbn.
progress unfold cos2_sin2_prop in Hcs.
now apply (rngl_eqb_eq Heo) in Hcs.
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

Notation "'π'" := (angle_straight) (at level 0).
Notation "'π/₂'" := angle_right.

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

Theorem angle_add_opp_l : ∀ θ1 θ2, (- θ1 + θ2 = θ2 - θ1)%A.
Proof.
intros.
apply angle_add_comm.
Qed.

Theorem angle_add_opp_r : ∀ θ1 θ2, (θ1 + - θ2 = θ1 - θ2)%A.
Proof. easy. Qed.

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

Theorem angle_add_sub : ∀ θ1 θ2, (θ1 + θ2 - θ2)%A = θ1.
Proof.
destruct_ac; intros.
progress unfold angle_sub.
rewrite <- angle_add_assoc.
rewrite angle_add_opp_r.
rewrite angle_sub_diag.
apply angle_add_0_r.
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

Theorem angle_sub_add : ∀ θ1 θ2, (θ1 - θ2 + θ2)%A = θ1.
Proof.
destruct_ac; intros.
progress unfold angle_sub.
rewrite <- angle_add_assoc.
rewrite angle_add_opp_diag_l.
apply (angle_add_0_r).
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

Theorem angle_right_add_right : (π/₂ + π/₂)%A = π.
Proof.
destruct_ac.
apply eq_angle_eq; cbn.
do 2 rewrite (rngl_mul_0_l Hos).
do 2 rewrite (rngl_mul_1_l Hon).
rewrite (rngl_sub_0_l Hop).
f_equal.
apply rngl_add_0_l.
Qed.

Theorem angle_straight_add_straight : (π + π = 0)%A.
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
  (π - π/₂)%A = π/₂.
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

Theorem angle_sub_opp_r : ∀ θ1 θ2, (θ1 - - θ2)%A = (θ1 + θ2)%A.
Proof.
destruct_ac.
intros.
apply eq_angle_eq; cbn.
now rewrite (rngl_opp_involutive Hop).
Qed.

Theorem angle_add_add_swap : ∀ θ1 θ2 θ3, (θ1 + θ2 + θ3)%A = (θ1 + θ3 + θ2)%A.
Proof.
intros.
do 2 rewrite <- angle_add_assoc.
f_equal.
apply angle_add_comm.
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

Theorem angle_sub_sub_swap : ∀ θ1 θ2 θ3, (θ1 - θ2 - θ3 = θ1 - θ3 - θ2)%A.
Proof.
intros.
progress unfold angle_sub.
apply angle_add_add_swap.
Qed.

Theorem angle_eqb_eq : ∀ θ1 θ2 : angle T, (θ1 =? θ2)%A = true ↔ θ1 = θ2.
Proof.
destruct_ac.
intros.
split; intros H12. {
  progress unfold angle_eqb in H12.
  apply Bool.andb_true_iff in H12.
  destruct H12 as (Hc12, Hs12).
  apply (rngl_eqb_eq Heo) in Hc12, Hs12.
  apply eq_angle_eq.
  now rewrite Hc12, Hs12.
} {
  subst θ2.
  progress unfold angle_eqb.
  now do 2 rewrite (rngl_eqb_refl Heo).
}
Qed.

Theorem angle_eqb_neq : ∀ θ1 θ2, (θ1 =? θ2)%A = false ↔ θ1 ≠ θ2.
Proof.
destruct_ac.
intros.
progress unfold angle_eqb.
split; intros H12. {
  intros H; subst θ2.
  now do 2 rewrite (rngl_eqb_refl Heo) in H12.
} {
  apply Bool.not_true_iff_false.
  intros H; apply H12; clear H12.
  apply eq_angle_eq; cbn.
  apply Bool.andb_true_iff in H.
  destruct H as (Hc, Hs).
  apply (rngl_eqb_eq Heo) in Hc, Hs.
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

Theorem angle_opp_straight : (- π)%A = π.
Proof.
destruct_ac.
apply eq_angle_eq; cbn.
f_equal.
apply (rngl_opp_0 Hop).
Qed.

Theorem angle_eqb_refl : ∀ θ : angle T, ((θ =? θ)%A = true).
Proof. now intros; apply angle_eqb_eq. Qed.

End a.
