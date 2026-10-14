# Real-rooted domination polynomials

Classifies finite graphs with real-rooted domination polynomials through leaf presentations and gives the polynomial factorization.

Entry points:

- `MainTheorems/DominationRoots/FactorForm.lean`

## Build

Lean 4.34.1 and Mathlib v4.34.1 are pinned at the repository root.
On Windows, use a short checkout path, such as `C:/math`.

From the repository root:

```sh
lake exe cache get
lake --wfail build DominationRoots
lake script run audit DominationRoots
lake env leanchecker --fresh DominationRoots
```

`Audit.lean` lists the axioms used by the main results and selected supporting theorems.
