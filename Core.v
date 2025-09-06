From Stdlib Require Import Utf8 Arith.

Require Import RingLike.Core.
Require Import RingLike.RealLike.

Section a.

Context {T : Type}.
Context {ro : ring_like_op T}.
Context {rp : ring_like_prop T}.

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

Declare Scope angle_scope.
Delimit Scope angle_scope with A.
Bind Scope angle_scope with angle.

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

Definition angle_zero :=
  {| rngl_cos := 1; rngl_sin := 0; rngl_cos2_sin2 := angle_zero_prop |}%L.

Definition angle_right :=
  {| rngl_cos := 0; rngl_sin := 1;
     rngl_cos2_sin2 := angle_right_prop |}%L.

Definition angle_straight :=
  {| rngl_cos := -1; rngl_sin := 0;
     rngl_cos2_sin2 := angle_straight_prop |}%L.

Definition rngl_acos (x : T) :=
  match (rngl_le_dec ac_or x² 1)%L with
  | left Hx1 =>
      {| rngl_cos := x; rngl_sin := √(1 - x²)%L;
         rngl_cos2_sin2 := rngl_acos_prop x Hx1 |}
  | _ =>
      angle_zero
  end.

(* *)

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

Definition angle_add a b :=
  {| rngl_cos := (rngl_cos a * rngl_cos b - rngl_sin a * rngl_sin b)%L;
     rngl_sin := (rngl_sin a * rngl_cos b + rngl_cos a * rngl_sin b)%L;
     rngl_cos2_sin2 := angle_add_prop a b |}.

Definition angle_opp a :=
  {| rngl_cos := rngl_cos a; rngl_sin := (- rngl_sin a)%L;
     rngl_cos2_sin2 := angle_opp_prop a |}.

Definition angle_sub θ1 θ2 := angle_add θ1 (angle_opp θ2).

Definition angle_ltb θ1 θ2 :=
  if (0 ≤? rngl_sin θ1)%L then
    if (0 ≤? rngl_sin θ2)%L then (rngl_cos θ2 <? rngl_cos θ1)%L
    else true
  else
    if (0 ≤? rngl_sin θ2)%L then false
    else (rngl_cos θ1 <? rngl_cos θ2)%L.

End a.

Notation "θ1 < θ2" := (angle_ltb θ1 θ2 = true) : angle_scope.

Section a.

Context {T : Type}.
Context {ro : ring_like_op T}.
Context {rp : ring_like_prop T}.
Context {rl : real_like_prop T}.
Context {ac : angle_ctx T}.

Theorem rngl_lt_0_cos :
  ∀ θ, (θ < angle_right)%A → (0 < rngl_cos θ)%L.
Proof.
destruct_ac.
intros * Htr.
progress unfold angle_ltb in Htr.
cbn in Htr.
specialize (rngl_0_le_1 Hon Hos Hiq Hor) as H1.
apply rngl_leb_le in H1.
rewrite H1 in Htr.
remember (0 ≤? rngl_sin θ)%L as zst eqn:Hzst.
symmetry in Hzst.
destruct zst; [ | easy ].
now apply rngl_ltb_lt in Htr.
Qed.

(* *)

Theorem cos2_sin2_prop_add_squ :
  ∀ c s, cos2_sin2_prop c s → (c² + s² = 1)%L.
Proof.
destruct_ac.
intros * Hcs.
progress unfold cos2_sin2_prop in Hcs.
now apply (rngl_eqb_eq Hed) in Hcs.
Qed.

Theorem rngl_cos_proj_bound :
  ∀ c s, cos2_sin2_prop c s → (-1 ≤ c ≤ 1)%L.
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

Theorem rngl_cos_bound :
  ∀ a, (-1 ≤ rngl_cos a ≤ 1)%L.
Proof.
destruct_ac.
intros.
destruct a as (ca, sa, Ha); cbn.
now apply (rngl_cos_proj_bound ca sa).
Qed.

Theorem angle_div_2_prop :
  ∀ a (ε := (if (0 ≤? rngl_sin a)%L then 1%L else (-1)%L)),
  cos2_sin2_prop
    (ε * √((1 + rngl_cos a) / 2))%L
    (√((1 - rngl_cos a) / 2)%L).
Proof.
destruct_ac.
intros.
progress unfold cos2_sin2_prop.
assert (Hε : (ε² = 1)%L). {
  progress unfold ε.
  destruct (0 ≤? _)%L. {
    apply (rngl_mul_1_l Hon).
  } {
    apply (rngl_squ_opp_1 Hon Hop).
  }
}
rewrite (rngl_squ_mul Hic).
rewrite Hε, (rngl_mul_1_l Hon).
apply (rngl_eqb_eq Hed).
destruct (Nat.eq_dec (rngl_characteristic T) 1) as [Hc1| Hc1]. {
  specialize (rngl_characteristic_1 Hon Hos Hc1) as H1.
  now rewrite (H1 (_ + _)%L), (H1 1%L).
}
rewrite (rngl_squ_sqrt Hon). 2: {
  apply (rngl_le_div_r Hon Hop Hiv Hor). {
    apply (rngl_0_lt_2 Hon Hos Hiq Hc1 Hor).
  }
  rewrite (rngl_mul_0_l Hos).
  apply (rngl_le_sub_le_add_l Hop Hor).
  rewrite (rngl_sub_0_l Hop).
  apply rngl_cos_bound.
}
rewrite (rngl_squ_sqrt Hon). 2: {
  apply (rngl_le_div_r Hon Hop Hiv Hor). {
    apply (rngl_0_lt_2 Hon Hos Hiq Hc1 Hor).
  }
  rewrite (rngl_mul_0_l Hos).
  apply (rngl_le_add_le_sub_r Hop Hor).
  rewrite rngl_add_0_l.
  apply rngl_cos_bound.
}
rewrite <- (rngl_div_add_distr_r Hiv).
rewrite (rngl_add_sub_assoc Hop).
rewrite rngl_add_comm.
rewrite rngl_add_assoc.
rewrite (rngl_add_sub Hos).
apply (rngl_div_diag Hon Hiq).
apply (rngl_2_neq_0 Hon Hos Hiq Hc1 Hor).
Qed.

Definition angle_div_2 a :=
  let ε := if (0 ≤? rngl_sin a)%L then 1%L else (-1)%L in
  {| rngl_cos := ε * √((1 + rngl_cos a) / 2)%L;
     rngl_sin := √((1 - rngl_cos a)%L / 2%L);
     rngl_cos2_sin2 := angle_div_2_prop a |}.

End a.

Arguments rngl_acos {T ro rp rl ac} x%_L.

Notation "0" := angle_zero : angle_scope.
Notation "θ1 - θ2" := (angle_sub θ1 θ2) : angle_scope.
Notation "- θ" := (angle_opp θ) : angle_scope.
Notation "θ /₂" := (angle_div_2 θ) (at level 40) : angle_scope.


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

Theorem angle_opp_sub_distr :
  ∀ θ1 θ2, (- (θ1 - θ2))%A = (θ2 - θ1)%A.
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

Theorem angle_straight_div_2 : (angle_straight /₂ = angle_right)%A.
Proof.
destruct_ac.
specialize (rngl_has_inv_and_1_has_inv_and_1_or_pdiv Hon Hiv) as Hi1.
specialize (rngl_int_dom_or_inv_1_quo_and_eq_dec Hi1 Hed) as Hid.
destruct (Nat.eq_dec (rngl_characteristic T) 1) as [Hc1| Hc1]. {
  intros.
  specialize (rngl_characteristic_1_angle_0 Hc1) as H1.
  rewrite (H1 angle_right).
  apply H1.
}
apply eq_angle_eq; cbn.
rewrite (rngl_leb_refl Hor).
rewrite (rngl_mul_1_l Hon).
rewrite (rngl_add_opp_r Hop).
rewrite (rngl_sub_opp_r Hop).
rewrite (rngl_sub_diag Hos).
rewrite (rngl_div_0_l Hos Hi1). 2: {
  apply (rngl_2_neq_0 Hon Hos Hiq Hc1 Hor).
}
rewrite (rl_sqrt_0 Hon Hop Hor). 2: {
  rewrite Bool.orb_true_iff; right.
  apply (rngl_has_inv_and_1_has_inv_and_1_or_pdiv Hon Hiv).
}
f_equal.
rewrite (rngl_div_diag Hon Hiq). 2: {
  apply (rngl_2_neq_0 Hon Hos Hiq Hc1 Hor).
}
apply (rl_sqrt_1 Hon Hop Hiq Hor).
Qed.

End a.
