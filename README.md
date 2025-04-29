# rocq_trigo_without_pi

A Rocq/Coq library for **trigonometry without π**.

This library defines a form of trigonometry where **angles are not
real numbers**, but instead are represented as **pairs of real numbers
(x, y)** constrained by the unit circle equation x²+y²=1.

This approach is purely geometric and avoids relying on π as a
fundamental constant, aligning with constructive and algebraic
perspectives.

## 🔧 Installation

To install this project via `opam`, use:

```bash
opam pin add rocq-ring-like https://github.com/roglo/rocq_ring_like.git
opam pin add rocq-trigo-without-pi https://github.com/roglo/rocq_trigo_without_pi.git
