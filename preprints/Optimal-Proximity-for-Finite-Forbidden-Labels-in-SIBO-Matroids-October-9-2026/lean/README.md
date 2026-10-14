# SIBO proximity

Proves the sharp proximity bound for SIBO matroids with arbitrary finite forbidden label sets in abelian groups, together with uniform-matroid examples attaining it.

Entry points:

- `MainTheorems/SIBOSharpness.lean`

## Build

Lean 4.34.1 and Mathlib v4.34.1 are pinned at the repository root.
On Windows, use a short checkout path, such as `C:/math`.

From the repository root:

```sh
lake exe cache get
lake --wfail build SIBO
lake script run audit SIBO
lake env leanchecker --fresh SIBO
```

`Audit.lean` lists the axioms used by the main results and selected supporting theorems.
