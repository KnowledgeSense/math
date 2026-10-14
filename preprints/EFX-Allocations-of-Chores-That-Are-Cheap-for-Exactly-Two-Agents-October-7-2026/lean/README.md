# EFX allocations of chores

Proves existence of a complete EFX allocation for any finite set of chores and at least two agents in the two-cheap-recipient model, with costs 1 and r > 2.

Entry points:

- `MainTheorems/Chores/Classification.lean`

## Build

Lean 4.34.1 and Mathlib v4.34.1 are pinned at the repository root.
On Windows, use a short checkout path, such as `C:/math`.

From the repository root:

```sh
lake exe cache get
lake --wfail build Chores
lake script run audit Chores
lake env leanchecker --fresh Chores
```

`Audit.lean` lists the axioms used by the main results and selected supporting theorems.
