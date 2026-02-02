Set Nested Proofs Allowed.
Require Import Stdlib.Arith.Arith.
Require Import RingLike.Utf8.

Require Import RingLike.Core.
Require Import RingLike.RealLike.

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
  { s : T;
    a_up : bool;
    a_right : bool;
    a_prop : angle2_prop s }.

Class angle2_ctx :=
  { ac_op : rngl_has_opp T = true;
    ac_to : rngl_is_totally_ordered T = true;
    ac_c1 : rngl_characteristic T ≠ 1 }.

Definition sin α :=
  if a_up α then s α else (- s α)%L.
Definition cos α :=
  if a_right α then √ (1 - (s α)²) else (- √ (1 - (s α)²))%L.

End a.

Arguments angle2 T {ro}.
Arguments angle2_ctx T {ro rp}.

Ltac destruct_ac2 :=
  set (Hop := ac_op);
  set (Hto := ac_to);
  set (Hc1 := ac_c1);
  set (Hos := rngl_has_opp_has_opp_or_psub Hop);
  set (Hor := rngl_is_totally_ordered_is_ordered Hto);
  set (Heo := rngl_has_eq_dec_or_is_ordered_r Hor).

Section a.

Context {T : Type}.
Context {ro : ring_like_op T}.
Context {rp : ring_like_prop T}.
Context {rl : real_like_prop T}.
Context {ac : angle2_ctx T}.

Theorem eq_angle2_eq : ∀ α1 α2,
  (s α1, a_up α1, a_right α1) = (s α2, a_up α2, a_right α2) ↔ α1 = α2.
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
  {| s := 0%L; a_up := true; a_right := true; a_prop := angle2_zero_prop |}.

(*
Lemma exemple (b : bool) (P Q : Prop) :
  b = true -> P -> Q -> (if b then P else Q).
...
*)

Theorem a_prop_up_right a b :
  a_up a = true
  → let s := (s a * √(1 - (s b)²) + √(1 - (s a)²) * s b)%L in
    ∀ s, angle2_prop s.
Admitted.

Definition angle2_add1 a b (a_up_true : a_up a = true) :=
  if a_right a then
    if a_up b then
      if a_right b then
        let s := (s a * √ (1 - (s b)²) + √ (1 - (s a)²) * s b)%L in
        if (0 ≤? s)%L then
          {| s := s; a_up := true; a_right := true;
             a_prop := a_prop_up_right a b a_up_true s |}
        else angle2_zero
      else angle2_zero
    else angle2_zero
  else angle2_zero.

Definition angle2_add (a b : angle2 T) : angle2 T.
remember (a_up a) as ua eqn:Hua.
symmetry in Hua.
destruct ua. {
  apply (angle2_add1 a b Hua).
}
apply angle2_zero.
Show Proof.
(* ah ouai, ça va être des types dépendants de merde *)
...

Definition angle2_add a b :=
  if a_up a then
    if a_right a then
      if a_up b then
        if a_right b then
          let s := (s a * √ (1 - (s b)²) + √ (1 - (s a)²) * s b)%L in
          if (0 ≤? s)%L then
            {| s := s; a_up := true; a_right := true;
               a_prop := a_prop_up_right a b (a_up a) s |}
          else angle2_zero
        else angle2_zero
      else angle2_zero
    else angle2_zero
  else angle2_zero.

...

End a.
