# Domination sequences of path and cycle powers

Proves ultra log-concavity of the domination sequences of all powers of paths and cycles.

Entry points:

- `MainTheorems/Domination/Classification.lean`

## Build

Lean 4.34.1 and Mathlib v4.34.1 are pinned at the repository root.
On Windows, use a short checkout path, such as `C:/math`.

From the repository root:

```sh
lake exe cache get
lake --wfail build Domination
lake script run audit Domination
lake env leanchecker --fresh Domination
```

`Audit.lean` lists the axioms used by the main results and selected supporting theorems.
