# Tuza conjecture for co-chain graphs

Proves the triangle-cover versus triangle-packing inequality for arbitrary finite co-chain graphs.

Entry points:

- `MainTheorems/Tuza/Classification.lean`

## Build

Lean 4.34.1 and Mathlib v4.34.1 are pinned at the repository root.
On Windows, use a short checkout path, such as `C:/math`.

From the repository root:

```sh
lake exe cache get
lake --wfail build Tuza
lake script run audit Tuza
lake env leanchecker --fresh Tuza
```

`Audit.lean` lists the axioms used by the main results and selected supporting theorems.
