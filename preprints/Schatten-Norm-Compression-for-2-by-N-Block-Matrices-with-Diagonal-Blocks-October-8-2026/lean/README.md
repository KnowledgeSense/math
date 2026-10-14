# Schatten norm compression

Proves the lower compression inequality for 1 <= p <= 2 and the upper inequality for p >= 2, including the operator norm, for complex 2-by-N matrices with diagonal blocks.

Entry points:

- `MainTheorems/DiagonalSchatten/Main.lean`

## Build

Lean 4.34.1 and Mathlib v4.34.1 are pinned at the repository root.
On Windows, use a short checkout path, such as `C:/math`.

From the repository root:

```sh
lake exe cache get
lake --wfail build DiagonalSchatten
lake script run audit DiagonalSchatten
lake env leanchecker --fresh DiagonalSchatten
```

`Audit.lean` lists the axioms used by the main results and selected supporting theorems.
