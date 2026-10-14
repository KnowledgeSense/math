# Tuza conjecture for path and cycle powers

Proves Tuza's inequality for all powers of paths and cycles and their finite disjoint unions.

Entry points:

- `MainTheorems/PathCycleTuza/Classification.lean`

## Build

Lean 4.34.1 and Mathlib v4.34.1 are pinned at the repository root.
On Windows, use a short checkout path, such as `C:/math`.

From the repository root:

```sh
lake exe cache get
lake --wfail build PathCycleTuza
lake script run audit PathCycleTuza
lake env leanchecker --fresh PathCycleTuza
```

`Audit.lean` lists the axioms used by the main results and selected supporting theorems.
