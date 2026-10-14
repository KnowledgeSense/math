# Bose–Burton inverse-Z polynomials

This project proves the ordinary inverse-Z theorem for every finite field K and every nonzero proper subspace W of a finite-dimensional vector space V. The matroid is the literal restriction of projective geometry to points outside W. Its inverse-Z polynomial has degree dim V, positive symmetric coefficients, and strict log-concavity at every internal index. The theorem includes affine geometries, one-point deletions, and every rank-two boundary.

Main declaration: `BoseBurton.bose_burton_inverseZ_main`.
The exact source finite-kernel identity is `boseBurtonY_eq_originalKernel`; `boseBurtonY_coefficient_formula` covers every coefficient, with `boseBurtonY_coeff_above` proving vanishing above rank.

The proof constructs the represented matroid, identifies its actual flats and ranked intervals, derives projective KL and Möbius invariants, counts genuine subspaces and flags, and evaluates the inverse-Z incidence convolution. A proved finite reindexing identifies the original signed kernel. Its positive expansion and discrete concavity then give the strict inequalities. The small vendored incidence modules retain their original namespaces and proofs.

## Build

Lean 4.34.1 and Mathlib v4.34.1 are pinned at the repository root.
On Windows, use a short checkout path, such as `C:/math`.

From the repository root:

```sh
lake exe cache get
lake --wfail build BoseBurton
lake script run certificates BoseBurton
lake script run audit BoseBurton
lake env leanchecker --fresh BoseBurton
```

`tests/Certificates.lean` checks the stated results and boundary cases.
`tests/Axioms.lean` lists the logical axioms used by the project.
