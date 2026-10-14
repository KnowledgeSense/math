# Inverse-Z log-concavity for fan matroids

`Fan.fan_inverseZ_main` proves the ordinary inverse-Z theorem for every fan
formed by joining an apex to all vertices of a path on n vertices, n ≥ 1.
Its polynomial has degree n, positive supported coefficients, symmetry,
and strict log-concavity at every internal index. The rank-one boundary is
`Fan.inverseZ_one`: Y₁ = 1 + t. There is no size cutoff.

`Fan.inverseZ` is defined on the actual ranked lattice of graphic flats.
Flats use connectivity closure, and rank is the vertex count minus the
number of connected components. The proof identifies these flats with
explicit spoke/rim configurations and proves their ranks. The KL and
inverse-KL recursions satisfy the standard incidence characterization.

The generating-function identity is derived from actual intervals and
finite flat enumeration. Boolean, separated-product and pendant intervals,
upper Möbius recurrences, and a unique trailing hub-run decomposition give
an exact renewal equation. Its strict-half-degree and reciprocal solution
is unique. Formal substitution and coefficient extraction identify that
solution with a finite weighted Delannoy sum. Real-rooted auxiliary kernels,
coefficientwise Turán inequalities and finite weighted summation prove the
strict coefficient inequalities. No family coefficient formula is assumed.
Coefficients above rank are separately proved to vanish.

The fan convention and motivating generating
function are those of Gao–Li–Li, *Inverse Kazhdan–Lusztig polynomials of fan
matroids*, arXiv:2603.25254v2, Theorem 3.1, equation (37). That identity's
actual-invariant content is proved locally here. The `ThagomizerTuran`
modules reuse the generic incidence-invariant foundations; the project is
self-contained apart from the pinned public mathlib dependency.

## Build

Lean 4.34.1 and Mathlib v4.34.1 are pinned at the repository root.
On Windows, use a short checkout path, such as `C:/math`.

From the repository root:

```sh
lake exe cache get
lake --wfail build Fan
lake script run certificates Fan
lake script run audit Fan
lake env leanchecker --fresh Fan
```

`tests/Certificates.lean` checks the stated results and boundary cases.
`tests/Axioms.lean` lists the logical axioms used by the project.
