# Optimal Ando-Hiai-Okubo constants

Classifies optimal constants for normalized two-matrix trace words: the constant is 1 in dimensions one and two; in higher dimensions it is 1 or infinite according to the feasibility criterion.

Entry points:

- `MainTheorems/AHOConstants/Classification.lean`

## Build

Lean 4.34.1 and Mathlib v4.34.1 are pinned at the repository root.
On Windows, use a short checkout path, such as `C:/math`.

From the repository root:

```sh
lake exe cache get
lake --wfail build AHOConstants
lake script run audit AHOConstants
lake env leanchecker --fresh AHOConstants
```

`Audit.lean` lists the axioms used by the main results and selected supporting theorems.
