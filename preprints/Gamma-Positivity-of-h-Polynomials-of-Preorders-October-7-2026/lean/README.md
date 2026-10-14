# Gamma-positivity for preorders

Proves the gamma expansion of the support polynomial of an arbitrary finite preorder. It also relates that polynomial to the Ehrhart h-star polynomial of its augmented root polytope.

Entry points:

- `MainTheorems/PreorderGamma/FullMain.lean`

## Build

Lean 4.34.1 and Mathlib v4.34.1 are pinned at the repository root.
On Windows, use a short checkout path, such as `C:/math`.

From the repository root:

```sh
lake exe cache get
lake --wfail build PreorderGamma
lake script run audit PreorderGamma
lake env leanchecker --fresh PreorderGamma
```

`Audit.lean` lists the axioms used by the main results and selected supporting theorems.
