# Retained-joint Dowling inverse-Z polynomials

This project proves the ordinary inverse-Z theorem for every finite group G, every n ≥ 1, and every subset X of retained joints. The matroid has all G-labelled links and precisely the joints in X. Its inverse-Z polynomial has degree equal to its actual rank, positive symmetric coefficients, and strict log-concavity at every internal coefficient.

Main declaration: `Dowling.retained_dowling_inverseZ`. The conclusion `StrictInverseZRow` states these four properties explicitly. `retained_dowling_strict_log_concave` and `retained_dowling_coeff_above` expose the strict inequalities and vanishing above rank directly for the genuine matroid invariant.

The theorem includes nonabelian groups, arbitrary retained subsets, the trivial-group clique-plus-partial-apex family, and both small-rank exceptions. For n ≥ 2 the rank is n whenever |G| ≥ 2 or X is nonempty. The trivial-group jointless case has rank n−1. At n=1 the empty ground has polynomial 1 and the retained joint has polynomial 1+t. `retained_constant_product` gives the source endpoint formula.

The proof constructs the actual frame matroid and proves its all-subset balanced-component rank formula using genuine gain walks and simple circles. Its flats and ranked intervals yield the full Dowling generating functions and coefficient formulas. A proved finite-matroid deletion theorem then evaluates every retained-joint correction. The resulting exact weighted rows are treated by exponent raising, discrete midpoint inequalities, and the partial-apex curvature argument. All identities connecting these rows to the original invariants are proved.

The local discrete midpoint proof follows Halikias–Klartag–Slomka, Proposition 2.2, DOI [10.5802/afst.1674](https://doi.org/10.5802/afst.1674). The deletion proof restores the polynomial-support condition from Braden–Vysogorets that is needed for the Laurent fixed-space basis argument in arXiv:2510.01086v1, §3.1; `DeletionIncidencePerverse` proves the supported uniqueness directly. The resulting actual deletion theorem retains the intended scope.

The small vendored incidence and formal-series modules retain their original namespaces. No external family coefficient formula or unproved analytic inequality is assumed.

## Build

Lean 4.34.1 and Mathlib v4.34.1 are pinned at the repository root.
On Windows, use a short checkout path, such as `C:/math`.

From the repository root:

```sh
lake exe cache get
lake --wfail build Dowling
lake script run certificates Dowling
lake script run audit Dowling
lake env leanchecker --fresh Dowling
```

`tests/Certificates.lean` checks the stated results and boundary cases.
`tests/Axioms.lean` lists the logical axioms used by the project.
