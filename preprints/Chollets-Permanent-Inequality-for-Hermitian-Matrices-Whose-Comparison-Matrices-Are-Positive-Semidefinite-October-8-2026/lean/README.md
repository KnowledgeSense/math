# Chollet permanent inequality

Proves the permanent inequality for finite complex Hermitian matrices with positive semidefinite comparison matrices.

Entry points:

- `MainTheorems/Chollet/Classification.lean`

## Build

Lean 4.34.1 and Mathlib v4.34.1 are pinned at the repository root.
On Windows, use a short checkout path, such as `C:/math`.

From the repository root:

```sh
lake exe cache get
lake --wfail build Chollet
lake script run audit Chollet
lake env leanchecker --fresh Chollet
```

`Audit.lean` lists the axioms used by the main results and selected supporting theorems.
