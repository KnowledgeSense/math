# 312-avoiding alternating-sign rectangles

This project proves the full three-variable enumeration formula for every
`r k d : ℕ` with `d ≤ r` and `d ≤ k`. The main theorem is
`ASR312.full_enumeration`:

```lean
(S r k d : ℤ) = F r k d
```

`S` counts actual `r × k` alternating-sign rectangles with exactly `d`
nonempty rows that admit an extension, below and to the right, to a
312-avoiding square alternating-sign matrix. The existential square witness
is part of the definition; internal avoidance alone is not substituted for
extendability. `F` is the four-term formula of Conjecture 4.5 in
[arXiv:2610.07442v1](https://arxiv.org/abs/2610.07442v1), with generalized
integer-upper binomial coefficients and zero for negative lower indices.
Zero dimensions and all boundary faces are included.

The proof constructs literal matrix bijections for the square Schröder
count and all rectangle recurrences, including the balanced-width face.
It then derives the count's formal generating series and evaluates the
four-term expression by a proved formal coefficient-change identity.
The Catalan substitution and the negative-exponent boundary cases are
proved within the project. No enumeration recurrence, characterizing
bijection, or coefficient-extraction theorem is assumed as an axiom.

## Build

Lean 4.34.1 and Mathlib v4.34.1 are pinned at the repository root.
On Windows, use a short checkout path, such as `C:/math`.

From the repository root:

```sh
lake exe cache get
lake --wfail build ASR312
lake script run certificates ASR312
lake script run audit ASR312
lake env leanchecker --fresh ASR312
```

`tests/Certificates.lean` checks the stated results and boundary cases.
`tests/Axioms.lean` lists the logical axioms used by the project.
