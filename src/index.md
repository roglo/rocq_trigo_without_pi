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

- [Angle](TrigoWithoutPi.Angle.html)

Division of an angle by 2:

- [AngleDiv2](TrigoWithoutPi.AngleDiv2.html)

Proof that the sequence converging to division by a natural is of Cauchy:

- [SeqAngleIsCauchy](TrigoWithoutPi.SeqAngleIsCauchy.html)

Proof that the angle type is complete:

- [AngleTypeIsComplete](TrigoWithoutPi.AngleTypeIsComplete.html)

Division of an angle by a natural number:

- [AngleDivNat](TrigoWithoutPi.AngleDivNat.html)

Other modules:

- [AngleAddLeMonoL_prop](TrigoWithoutPi.AngleAddLeMonoL_prop.html)
- [AngleAddLeMonoL_sin_lb_neg_sin_2_neg](TrigoWithoutPi.AngleAddLeMonoL_sin_lb_neg_sin_2_neg.html)
- [AngleAddLeMonoL_sin_lb_neg_sin_2_nonneg](TrigoWithoutPi.AngleAddLeMonoL_sin_lb_neg_sin_2_nonneg.html)
- [AngleAddLeMonoL_sin_lb_nonneg](TrigoWithoutPi.AngleAddLeMonoL_sin_lb_nonneg.html)
- [AngleAddLeMonoL](TrigoWithoutPi.AngleAddLeMonoL.html)
- [AngleAddOverflowLe](TrigoWithoutPi.AngleAddOverflowLe.html)
- [AngleDiv2Add](TrigoWithoutPi.AngleDiv2Add.html)
- [Order](TrigoWithoutPi.Order.html)
- [TacChangeAngle](TrigoWithoutPi.TacChangeAngle.html)
- [TrigoWithoutPiExt](TrigoWithoutPi.TrigoWithoutPiExt.html)

## Table of Contents

- [toc](toc.html)

---
