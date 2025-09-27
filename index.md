---
title: "Trigonometry Without π – A Constructive Library in Rocq (Coq)"
css: style.css
---

This site documents a formalization of trigonometry that avoids the use of
real numbers for angles and, in particular, avoids using π.

Instead of treating angles as real scalars, this approach models them as
pairs (x, y) such that x² + y² = 1 — i.e., points on the unit circle.
Trigonometric functions are defined geometrically, and angle operations
(addition, bisection, division by n) are constructed using only elementary
tools such as square roots.

All results are proven in Rocq (a proof assistant previously named
Coq), following a constructive philosophy: no infinite series, no
transcendental constants, and no non-constructive principles.

## Highlights

- A geometric and algebraic definition of angles and trigonometric functions
- Constructive proofs of key results, including division of angles
- Formal verification in Rocq, fully documented module by module

This library may be of interest to:

- Formal methods researchers
- Constructive mathematicians
- Educators exploring alternative approaches to trigonometry

👉 [Zenodo article](https://zenodo.org/records/15347540)

👉 [GitHub source code](https://github.com/roglo/rocq_trigo_without_pi)

## Available Modules

Definition of angle, cos, sin, addition of angles:

- [Angle_Def](TrigoWithoutPi.Angle_Def.html)

Division of an angle by 2:

- [Angle_Div2](TrigoWithoutPi.Angle_Div2.html)

Proof that the sequence converging to division by a natural is of Cauchy:

- [Seq_Angle_Is_Cauchy](TrigoWithoutPi.Seq_Angle_Is_Cauchy.html)

Proof that the angle type is complete:

- [Angle_Type_Is_Complete](TrigoWithoutPi.Angle_Type_Is_Complete.html)

Division of an angle by a natural number:

- [Angle_Div_Nat](TrigoWithoutPi.Angle_Div_Nat.html)

Other modules:

- [Angle_Add_Le_MonoL_prop](TrigoWithoutPi.Angle_Add_Le_Mono_L_prop.html)
- [Angle_Add_Le_Mono_L_1](TrigoWithoutPi.Angle_Add_Le_Mono_L_1.html)
- [Angle_Add_Le_Mono_L_2](TrigoWithoutPi.Angle_Add_Le_Mono_L_2.html)
- [Angle_Add_Le_Mono_L_3](TrigoWithoutPi.Angle_Add_Le_Mono_L_3.html)
- [Angle_Add_Le_Mono_L](TrigoWithoutPi.Angle_Add_Le_Mono_L.html)
- [Angle_Add_Overflow_Le](TrigoWithoutPi.Angle_Add_Overflow_Le.html)
- [Angle_Div2_Add](TrigoWithoutPi.Angle_Div2_Add.html)
- [Order](TrigoWithoutPi.Order.html)
- [Tac_Change_Angle](TrigoWithoutPi.Tac_Change_Angle.html)
- [Trigo_Without_Pi_Ext](TrigoWithoutPi.Trigo_Without_Pi_Ext.html)

## Table of Contents

- [toc](toc.html)

---
