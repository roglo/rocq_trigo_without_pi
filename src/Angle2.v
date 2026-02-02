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
  if a_up α then a_s α else (- a_s α)%L.
Definition cos α :=
  if a_right α then √ (1 - (a_s α)²) else (- √ (1 - (a_s α)²))%L.

End a.

Arguments angle2 T {ro}.
Arguments angle2_ctx T {ro rp}.
Arguments angle2_prop {T ro} s%_L.

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

Theorem cos2_sin2_1 : ∀ α, (cos² α + sin² α = 1)%L.
Proof.
destruct_ac2.
intros.
progress unfold cos.
progress unfold sin.
...

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
...
apply (rngl_eqb_eq Heo) in Hxy'.
rewrite Hxy'.
now do 2 rewrite rngl_mul_1_r.
...

Theorem sin_add_le_1 : ∀ a b, (sin a * cos b + cos a * sin b ≤ 1)%L.
Proof.
destruct_ac2.
intros.
enough ((cos a)² + (sin a)² = 1)%L.
enough ((cos b)² + (sin b)² = 1)%L.
enough (-1 ≤ cos a ≤ 1)%L.
enough (-1 ≤ sin a ≤ 1)%L.
enough (-1 ≤ cos b ≤ 1)%L.
enough (-1 ≤ sin b ≤ 1)%L.
...
destruct a as (sa, ua, ra, Hpa).
destruct b as (sb, ub, rb, Hpb).
move Hpa before Hpb.
progress unfold sin, cos.
cbn.
progress unfold angle2_prop in Hpa, Hpb.
apply Bool.andb_true_iff in Hpa, Hpb.
destruct Hpa as (Ha1, Ha2).
destruct Hpb as (Hb1, Hb2).
apply rngl_leb_le in Ha1, Hb1.
apply (rngl_ltb_lt Heo) in Ha2, Hb2.
destruct ua, ub, ra, rb. {
...

Theorem angle2_add_prop_1 a b :
  let s := (sin a * cos b + cos a * sin b)%L in
  ∀ (Hzs : (0 ≤? s)%L = true) (Hs1 : (s =? 1)%L = false), angle2_prop s.
Proof.
destruct_ac2.
intros.
apply (rngl_eqb_neq Heo) in Hs1.
progress unfold angle2_prop.
rewrite Hzs; cbn.
subst s.
apply (rngl_ltb_lt Heo).
apply rngl_le_neq.
split; [ | easy ].
...
progress unfold sin.
progress unfold cos.
destruct (a_up a). {
  destruct (a_right a). {
    destruct (a_up b). {
      destruct (a_right b). {
...
Qed.

Definition angle2_add a b :=
  match Bool.bool_dec (a_up a) true with
  | left Hua =>
      match Bool.bool_dec (a_right a) true with
      | left Hra =>
         match Bool.bool_dec (a_up b) true with
         | left Hub =>
             match Bool.bool_dec (a_right b) true with
             | left Hrb =>
                 let s := (sin a * cos b + cos a * sin b)%L in
                 match rngl_leb_dec 0 s with
                 | left Hzs =>
                     match rngl_ltb_dec s 1 with
                     | left Hs1 =>
                         {| a_s := s; a_up := true; a_right := true;
                            a_prop := angle2_add_prop_1 a b Hzs Hs1 |}
                     | right Hs1 => angle2_zero
                     end
                 | right Hsz => angle2_zero
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
