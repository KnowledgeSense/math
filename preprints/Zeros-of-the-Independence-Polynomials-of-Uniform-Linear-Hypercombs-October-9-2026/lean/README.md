# Strong independence polynomials of uniform hypercombs

Proves the root sector bound, log-concavity and unimodality for strong independence polynomials of uniform linear hypercombs.

Entry points:

- `MainTheorems/Hypercomb/Classification.lean`

## Build

Lean 4.34.1 and Mathlib v4.34.1 are pinned at the repository root.
On Windows, use a short checkout path, such as `C:/math`.

From the repository root:

```sh
lake exe cache get
lake --wfail build Hypercomb
lake script run audit Hypercomb
lake env leanchecker --fresh Hypercomb
```

`Audit.lean` lists the axioms used by the main results and selected supporting theorems.
