# Cyclic orderings of laminar matroids

Constructs cyclic basis orderings of finite laminar matroids that preserve a prescribed sequence of disjoint basis blocks.

Entry points:

- `MainTheorems/Laminar/CyclicOrdering.lean`

## Build

Lean 4.34.1 and Mathlib v4.34.1 are pinned at the repository root.
On Windows, use a short checkout path, such as `C:/math`.

From the repository root:

```sh
lake exe cache get
lake --wfail build Laminar
lake script run audit Laminar
lake env leanchecker --fresh Laminar
```

`Audit.lean` lists the axioms used by the main results and selected supporting theorems.
