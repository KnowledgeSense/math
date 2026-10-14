# Local permutation polynomials of maximum degree

Constructs local permutation polynomials with coefficients in the prime field, coordinate degree at most q - 2 and total degree n(q - 2), for every finite field of size q > 3 and every n >= 1.

Entry points:

- `MainTheorems/LocalPermutation/Classification.lean`

## Build

Lean 4.34.1 and Mathlib v4.34.1 are pinned at the repository root.
On Windows, use a short checkout path, such as `C:/math`.

From the repository root:

```sh
lake exe cache get
lake --wfail build LocalPermutation
lake script run audit LocalPermutation
lake env leanchecker --fresh LocalPermutation
```

`Audit.lean` lists the axioms used by the main results and selected supporting theorems.
