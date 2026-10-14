# Oscillatory scalar recurrence

Lean 4.34.1 / mathlib v4.34.1 formalization of the four recurrence formulas in Conjecture 3.9 of [arXiv:2607.19797](https://arxiv.org/html/2607.19797v1), for the bilinear weight `x exp(i m π x)` on `[-1,1]`, every nonzero integer `m`, and every degree in the stated ranges.

## Main results

- `original_orthogonal_family`: the actual monic polynomials obtained from the integral moment matrices, with exact degrees and integral orthogonality. `orthogonalPolynomial_unique` proves uniqueness.
- `original_initial_recurrence` and `original_three_term_recurrence`: the source's recurrence, with real coefficients `alpha` and `beta` and the original degree indexing.
- `alpha_even`, `alpha_odd`: both diagonal formulas for every `k ≥ 2`.
- `beta_even`, `beta_odd`: both lower-coefficient formulas for every `k ≥ 1`.
- `uniform_monic_family`: one frequency-independent rational polynomial family, monic of degree `j`, with `G₀ = 1` and `G₁ = X − 2`.
- `realFamily_even_denominator_ne_zero` and `realFamily_odd_denominator_ne_zero`: every denominator in those formulas is nonzero.
- `recurrenceFamily_appendix_2` through the listed indices `3,4,5,6,8,9,11,12,15,16`: exact agreement with all polynomials printed in Appendix C(4).

The family is defined from the actual Hankel determinant and divided bordered numerator. The proof establishes the integral-to-polynomial normalization, determinant nonvanishing at every allowed frequency, both parity leading coefficients of the Hankel and bordered determinants, and the common family indexing. Unused family indices are filled by monomials. Finite Appendix identities use rational triangular-factorization certificates and exact polynomial interpolation; the displayed data are checked by Lean's kernel, not accepted as inputs.

`TranscendencePi.lean` and `TranscendencePiAux.lean` adapt the cited Apache-2.0 proof of π's transcendence. See `THIRD_PARTY_NOTICES.md` and `LICENSE-APACHE-2.0.md`. No additional axioms or numerical-oracle assumptions are used.

## Build

Lean 4.34.1 and Mathlib v4.34.1 are pinned at the repository root.
On Windows, use a short checkout path, such as `C:/math`.

From the repository root:

```sh
lake exe cache get
lake --wfail build OscillatoryRecurrence
lake script run certificates OscillatoryRecurrence
lake script run audit OscillatoryRecurrence
lake env leanchecker --fresh OscillatoryRecurrence
```

`tests/Certificates.lean` checks the stated results and boundary cases.
`tests/Axioms.lean` lists the logical axioms used by the project.
