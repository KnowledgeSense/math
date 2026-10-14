# Honest embedding dimension in multiplicity five

Lean formalization accompanying the [manuscript](../article.pdf).

## Results

- `theorem_one_four`: the complete first-collision criterion for four minimal generators, including its three explicit residue alternatives.
- `theorem_one_five`: the complete residue and strict-inequality criterion for five minimal generators.
- `theorem_two`: the exhaustive classification into honest embedding dimensions 2, 3, 4 and 5, with every clause of Theorem 1.2.

`NumericalSemigroup.honestEmbeddingDimension` is the least ambient dimension of an actual complex analytic realization. Numerical semigroups are cofinite additive submonoids of the naturals; generators are intrinsic minimal generators. The analytic value set ranges over all analytic outer germs. Its Taylor/formal-substitution bridge, normalization, residue obstructions, and every required convergent realization are proved. The multiplicity-five maximal-dimension result is proved here as well.

The package covers the two main theorems and their supporting mathematics. The paper's finite computational census is not part of these proofs.

## Build

From the repository root, run:

```sh
lake exe cache get
lake --wfail build HonestEmbeddingDimension
lake script run audit HonestEmbeddingDimension
lake env leanchecker --fresh HonestEmbeddingDimension
```

The shared toolchain and dependency revisions are pinned at the repository root.
