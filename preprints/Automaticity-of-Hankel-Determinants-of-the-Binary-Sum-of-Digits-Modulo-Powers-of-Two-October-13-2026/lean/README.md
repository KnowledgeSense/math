# Binary digit-sum Hankel determinants

Let `s(j)` be the number of ones in the binary expansion of `j`, and let
`D(N) = det[s(i+j)]` for `0 ≤ i,j < N`.

`HankelAutomaticity.binary_digit_sum_hankel_automaticity` proves that, for every
`K ≥ 1`, the sequence `n ↦ D(n+1) mod 2^K` is 2-automatic. The supplied finite
machine reads ordinary binary digits most significant first, accepts the empty
representation of zero, and ignores arbitrarily many leading zeroes.
`hankel_automaton_correct_with_leading_zeroes` gives its exact output for every
index and every number of leading zeroes.

The definition of `s` uses `Nat.digits`; `digitSum_eq_count_bits` identifies it
with the literal number of true binary digits. All determinant bridges are
proved. The proof obtains the lower reflection and upper weight-halving
recurrences by determinant-preserving matrix operations. It normalizes the
actual determinant together with its rank-one perturbation coefficient, giving
integral recurrences without reducing rational denominators modulo powers of
two. A finite suffix-answer function yields an LSB machine, and finite
transformation composition proves the conversion to the stated MSB machine.

The target is the all-powers-of-two automaticity question for binary digit-sum
Hankel determinants. The weighted determinant reductions follow the ideas of
B. Sobolewski and M. Ulas, *Hankel determinants of weighted binary sums of digits*,
arXiv:2607.09376, Sections 3–4. Their determinant identities are proved here,
not assumed as external axioms. The finite-state construction is direct.

## Build

Lean 4.34.1 and Mathlib v4.34.1 are pinned at the repository root.
On Windows, use a short checkout path, such as `C:/math`.

From the repository root:

```sh
lake exe cache get
lake --wfail build HankelAutomaticity
lake script run certificates HankelAutomaticity
lake script run audit HankelAutomaticity
lake env leanchecker --fresh HankelAutomaticity
```

`tests/Certificates.lean` checks the stated results and boundary cases.
`tests/Axioms.lean` lists the logical axioms used by the project.
