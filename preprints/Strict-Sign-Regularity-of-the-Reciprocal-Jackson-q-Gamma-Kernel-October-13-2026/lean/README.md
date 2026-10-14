# Strict sign regularity of the reciprocal q-gamma kernel

Lean 4.34.1 / mathlib v4.34.1.

For every 0 < q < 1, every finite order r ≥ 1, and arbitrary strictly
increasing positive real lists x₁,…,xᵣ and y₁,…,yᵣ, the project proves

    (−1)^(r(r−1)/2) det[1 / Γ_q(xᵢ + yⱼ)] > 0.

`qGamma` uses the standard infinite-product definition

    Γ_q(z) = (1−q)^(1−z) (q;q)∞ / (q^z;q)∞.

All products and normalizing factors are shown to converge and be strictly
positive on the stated domain. Node lists are unrestricted real lists;
no integer spacing, bounded order, or fixed truncation replaces the result.

## Proof modules

- `Products`: convergence, positivity, and finite-product bounds
- `GeneralizedVandermonde`: strict positivity for arbitrary increasing
  nonnegative integer exponents, using Descartes' rule and a continuous path
- `CauchyBinet`, `OrderedMinors`, `Bidiagonal`: local finite determinant
  identities and all-minor nonnegativity
- `NestedCoefficients`, `NestedMinors`, `QProductMinors`: exact bidiagonal
  coefficient factorization and every selected nested-product minor
- `QBinomial`: the genuine convergent infinite q-binomial identity, proved
  from the coefficient recurrence, its functional equation, and limits
- `FiniteKernel`, `InfiniteKernel`: positive finite expansions and a fixed
  positive contribution surviving the infinite limit
- `Reversal`, `Main`: the original node ordering, reversal signature, and
  positive row/column normalization to the actual reciprocal q-gamma kernel

The formalization proves the two inputs used in the manuscript: the
q-binomial theorem and total nonnegativity of the Newton coefficient
matrix. The coefficient-matrix result follows from exact bidiagonal
factorization in `NestedCoefficients`, `NestedMinors` and `QProductMinors`.
Strict positivity in the limit follows from an explicit fixed positive minor.

## Build

Lean 4.34.1 and Mathlib v4.34.1 are pinned at the repository root.
On Windows, use a short checkout path, such as `C:/math`.

From the repository root:

```sh
lake exe cache get
lake --wfail build ReciprocalQGamma
lake script run certificates ReciprocalQGamma
lake script run audit ReciprocalQGamma
lake env leanchecker --fresh ReciprocalQGamma
```

`tests/Certificates.lean` checks the stated results and boundary cases.
`tests/Axioms.lean` lists the logical axioms used by the project.
