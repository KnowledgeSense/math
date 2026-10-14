# Eulerian pencil root classification

Classifies the real-root regions of the Eulerian polynomial pencil A_n(x) + k x A_(n-2)(x), for all n >= 3 and real k.

Entry points:

- `MainTheorems/EulerianPencil/Classification.lean`

## Build

Lean 4.34.1 and Mathlib v4.34.1 are pinned at the repository root.
On Windows, use a short checkout path, such as `C:/math`.

From the repository root:

```sh
lake exe cache get
lake --wfail build EulerianPencil
lake script run audit EulerianPencil
lake env leanchecker --fresh EulerianPencil
```

`Audit.lean` lists the axioms used by the main results and selected supporting theorems.
