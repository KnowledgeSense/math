# Generic value semigroups with prescribed coordinate orders

Lean formalization accompanying the [manuscript](../article.pdf).

## Results

- `release_generic_value_theorem`: a nonzero integer-coefficient condition on exactly the higher coefficients below conductor plus minimum order determines the full formal and convergent analytic value semigroups.
- `release_algebraically_independent_values`: algebraic independence over the rationals suffices.
- `greedy_numerical_semigroup`: the prescribed greedy set is a cofinite additive submonoid.
- `genus_conductor_formula`: exact signed maximum formulas, conductor, and the uniform two-coordinate cutoff. `genus_and_minimal_generators` supplies the multiplicity and generator bounds.
- `greedy_genus_asymptotic`, `arithmetic_progression_genus_bounds`, and `even_arithmetic_progression_genus_bigO`: the general genus estimates and arithmetic-progression corollary.

`NormalizedGerms` uses the original series expression and proves independence from every higher tail. Its analytic theorem uses actual analytic functions, derivatives, and analytic order. The formal-to-analytic equality is proved. The nonvanishing minors are established through explicit exponential witnesses and finite Pascal-matrix factorization.

## Build

From the repository root, run:

```sh
lake exe cache get
lake --wfail build GenericValueSemigroups
lake script run audit GenericValueSemigroups
lake env leanchecker --fresh GenericValueSemigroups
```

The shared toolchain and dependency revisions are pinned at the repository root.
