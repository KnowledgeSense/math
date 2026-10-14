# Pure O-sequence classification

Classifies the codimension and type pairs for which every pure O-sequence is log-concave, with counterexamples for all remaining feasible pairs.

Entry points:

- `MainTheorems/PureOSequences/Classification.lean`

## Build

Lean 4.34.1 and Mathlib v4.34.1 are pinned at the repository root.
On Windows, use a short checkout path, such as `C:/math`.

From the repository root:

```sh
lake exe cache get
lake --wfail build PureOSequences
lake script run audit PureOSequences
lake env leanchecker --fresh PureOSequences
```

`Audit.lean` lists the axioms used by the main results and selected supporting theorems.
