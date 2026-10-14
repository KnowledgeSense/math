# Product inequality for Wishart block determinants

Proves the product inequality for nonnegative powers of determinants of blocks in a partition, under the Bartlett construction of the Wishart law, for real shape alpha > p - 1 and positive definite covariance.

Entry points:

- `MainTheorems/WishartBlocks/MainProductInequality.lean`

## Build

Lean 4.34.1 and Mathlib v4.34.1 are pinned at the repository root.
On Windows, use a short checkout path, such as `C:/math`.

From the repository root:

```sh
lake exe cache get
lake --wfail build WishartBlocks
lake script run audit WishartBlocks
lake env leanchecker --fresh WishartBlocks
```

`Audit.lean` lists the axioms used by the main results and selected supporting theorems.
