Set Nested Proofs Allowed.
Require Import Stdlib.Arith.Arith.
Require Import RingLike.Utf8.

Require Import RingLike.Core.
Require Import RingLike.RealLike.
(*
From TrigoWithoutPi Require Import AngleDef Angle.
From TrigoWithoutPi Require Import Core.
*)

Notation "a ≤? b <? c" := ((a ≤? b)%L && (b <? c)%L)%bool
  (at level 70, b at next level) : ring_like_scope.

Section a.

Context {T : Type}.
Context {ro : ring_like_op T}.
Context {rp : ring_like_prop T}.
Context {rl : real_like_prop T}.

(* Angles as (s, up, right), where s is the absolute sine (0 ≤ s < 1),
   and up/right indicate the quadrant. *)

Definition angle2_prop s := (0 ≤? s <? 1)%L = true.

Record angle2 := mk_angle2
  { a_s : T;
    a_up : bool;
    a_right : bool;
    a_prop : angle2_prop a_s }.

Class angle2_ctx :=
  { ac_ic : rngl_mul_is_comm T = true;
    ac_op : rngl_has_opp T = true;
    ac_iv : rngl_has_inv T = true;
    ac_to : rngl_is_totally_ordered T = true;
    ac_c1 : rngl_characteristic T ≠ 1 }.

Definition sin α :=
  if a_up α then
    if a_right α then √(a_s α)
    else √(1 - a_s α)%L
  else
    if a_right α then (- √(1 - a_s α))%L
    else (- √(a_s α))%L.
Definition cos α :=
  if a_up α then
    if a_right α then √(1 - a_s α)
    else (- √(a_s α))%L
  else
    if a_right α then √(a_s α)%L
    else (- √(1 - a_s α))%L.

End a.

Arguments angle2 T {ro}.
Arguments angle2_ctx T {ro rp}.
Arguments angle2_prop {T ro} s%_L.
Arguments mk_angle2 {T ro} a_s%_L (a_up a_right)%_bool a_prop.

Notation "cos² a" := ((cos a)²) (at level 10).
Notation "sin² a" := ((sin a)²) (at level 10).

Ltac destruct_ac2 :=
  set (Hic := ac_ic);
  set (Hop := ac_op);
  set (Hiv := ac_iv);
  set (Hto := ac_to);
  set (Hc1 := ac_c1);
  set (Hos := rngl_has_opp_has_opp_or_psub Hop);
  set (Hiq := rngl_has_inv_has_inv_or_pdiv Hiv);
  set (Hor := rngl_is_totally_ordered_is_ordered Hto);
  set (Heo := rngl_has_eq_dec_or_is_ordered_r Hor).

Section a.

Context {T : Type}.
Context {ro : ring_like_op T}.
Context {rp : ring_like_prop T}.
Context {rl : real_like_prop T}.
Context {ac : angle2_ctx T}.

Theorem eq_angle2_eq : ∀ α1 α2,
  (a_s α1, a_up α1, a_right α1) = (a_s α2, a_up α2, a_right α2) ↔ α1 = α2.
Proof.
intros.
split; intros Hab; [ | now subst α2 ].
injection Hab; clear Hab; intros Hr Hu Hs.
destruct α1 as (s1, u1, r1, H1).
destruct α2 as (s2, u2, r2, H2).
cbn in Hs, Hu, Hr.
subst s2 u2 r2.
f_equal.
apply (Eqdep_dec.UIP_dec Bool.bool_dec).
Qed.

Theorem angle2_zero_prop : angle2_prop 0%L.
Proof.
destruct_ac2.
progress unfold angle2_prop.
apply Bool.andb_true_iff.
rewrite (rngl_leb_refl Hor).
split; [ easy | ].
apply (rngl_ltb_lt Heo).
apply (rngl_0_lt_1 Hos Hc1 Hto).
Qed.

Definition angle2_zero :=
  {| a_s := 0%L; a_up := true; a_right := true; a_prop := angle2_zero_prop |}.

Definition angle2_right :=
  {| a_s := 0; a_up := true; a_right := false; a_prop := angle2_zero_prop |}.

Theorem a_s_bound : ∀ α, (0 ≤ a_s α < 1)%L.
Proof.
destruct_ac2.
intros.
specialize (a_prop α) as H1.
apply Bool.andb_true_iff in H1.
destruct H1 as (H1, H2).
apply rngl_leb_le in H1.
now apply (rngl_ltb_lt Heo) in H2.
Qed.

Theorem cos2_sin2_1 : ∀ α, (cos² α + sin² α = 1)%L.
Proof.
destruct_ac2.
intros.
progress unfold cos.
progress unfold sin.
destruct (a_up α), (a_right α). {
  rewrite rngl_squ_sqrt. {
    rewrite rngl_squ_sqrt; [ apply (rngl_sub_add Hop) | ].
    apply a_s_bound.
  }
  apply (rngl_le_0_sub Hop Hor).
  apply a_s_bound.
} {
  rewrite rngl_squ_sqrt. {
    rewrite (rngl_squ_opp Hop), rngl_add_comm.
    rewrite rngl_squ_sqrt; [ apply (rngl_sub_add Hop) | ].
    apply a_s_bound.
  }
  apply (rngl_le_0_sub Hop Hor).
  apply a_s_bound.
} {
  rewrite rngl_squ_sqrt. {
    rewrite (rngl_squ_opp Hop), rngl_add_comm.
    rewrite rngl_squ_sqrt; [ apply (rngl_sub_add Hop) | ].
    apply (rngl_le_0_sub Hop Hor).
    apply a_s_bound.
  }
  apply a_s_bound.
} {
  do 2 rewrite (rngl_squ_opp Hop).
  rewrite rngl_squ_sqrt. {
    rewrite rngl_squ_sqrt; [ apply (rngl_sub_add Hop) | ].
    apply a_s_bound.
  }
  apply (rngl_le_0_sub Hop Hor).
  apply a_s_bound.
}
Qed.

Theorem cos_sin_add_prop :
  ∀ a b,
  ((cos a * cos b - sin a * sin b)² + (sin a * cos b + cos a * sin b)² = 1)%L.
Proof.
destruct_ac2.
intros.
remember (cos a) as x eqn:Hx.
remember (sin a) as y eqn:Hy.
remember (cos b) as x' eqn:Hx'.
remember (sin b) as y' eqn:Hy'.
rewrite (rngl_add_comm (y * _)%L).
rewrite (rngl_squ_add Hic).
rewrite (rngl_squ_sub Hop Hic).
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
subst.
rewrite cos2_sin2_1.
do 2 rewrite rngl_mul_1_r.
apply cos2_sin2_1.
Qed.

Theorem cos_add_le_1 : ∀ a b, (cos a * cos b - sin a * sin b ≤ 1)%L.
Proof.
destruct_ac2.
intros.
specialize (cos_sin_add_prop a b) as H1.
apply (rngl_squ_le_1_iff Hop Hiq Hto).
rewrite <- H1.
apply (rngl_le_add_r Hos Hor).
apply (rngl_squ_nonneg Hos Hto).
Qed.

Theorem sin_add_le_1 : ∀ a b, (sin a * cos b + cos a * sin b ≤ 1)%L.
Proof.
destruct_ac2.
intros.
specialize (cos_sin_add_prop a b) as H1.
apply (rngl_squ_le_1_iff Hop Hiq Hto).
rewrite <- H1.
apply (rngl_le_add_l Hos Hor).
apply (rngl_squ_nonneg Hos Hto).
Qed.

Theorem angle2_add_prop_1 a b :
  let cab := (cos a * cos b - sin a * sin b)%L in
  ∀ (Hzc : (0 <? cab)%L = true), angle2_prop (1 - cab²).
Proof.
destruct_ac2.
specialize (rngl_integral_or_inv_pdiv_eq_dec_order Hiv Hor) as Hio.
intros.
progress unfold angle2_prop.
apply Bool.andb_true_iff.
apply (rngl_ltb_lt Heo) in Hzc.
split. {
  apply rngl_leb_le.
  apply (rngl_le_0_sub Hop Hor).
  apply (rngl_squ_le_1_iff Hop Hiq Hto).
  split. {
    apply (rngl_le_trans Hor _ 0); [ | now apply rngl_lt_le_incl ].
    apply (rngl_opp_1_le_0 Hop Hto).
  }
  subst cab.
  apply cos_add_le_1.
}
apply (rngl_ltb_lt Heo).
apply (rngl_lt_sub_l Hop Hor).
apply rngl_le_neq.
split; [ apply (rngl_squ_nonneg Hos Hto) | ].
intros H; symmetry in H.
apply (eq_rngl_squ_0 Hos Hio) in H.
rewrite H in Hzc.
now apply rngl_lt_irrefl in Hzc.
Qed.

Definition angle2_add a b :=
  let cab := (cos a * cos b - sin a * sin b)%L in
  match Bool.bool_dec (a_up a) true with
  | left Hua =>
      match Bool.bool_dec (a_right a) true with
      | left Hra =>
         match Bool.bool_dec (a_up b) true with
         | left Hub =>
             match Bool.bool_dec (a_right b) true with
             | left Hrb =>
                 match rngl_ltb_dec 0 cab with
                 | left Hzc =>
                     {| a_s := 1 - cab²; a_up := true; a_right := true;
                        a_prop := angle2_add_prop_1 a b Hzc |}
                 | right Hsz =>
                     angle2_zero
                 end
             | right Hlb => angle2_zero
             end
        | right Hdb => angle2_zero
         end
      | right Hla => angle2_zero
    end
  | right Hda => angle2_zero
  end.

...

End a.
