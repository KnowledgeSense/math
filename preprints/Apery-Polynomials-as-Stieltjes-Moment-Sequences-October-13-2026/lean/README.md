# Positive moments of Apéry polynomials

For every real `x ≥ 1`, this project proves that

`A_n(x) = Σ j=0..n, (choose n j * choose (n+j) j)^2 * x^j`

is represented, for all natural `n`, by one nonnegative probability measure with compact support in `[0,∞)`. The boundary parameter `x = 1` is included.

The main theorem is `AperyMoments.positive_moments_for_full_parameter_ray`. The property `HasPositiveMomentRepresentation` quantifies over an actual measure, its probability normalization, compact nonnegative support, integrability of every power, and equality with the original finite sums.

## Proof

The proof constructs the real elliptic density and its continued Cauchy transform from actual integrals. It proves the branch identities, holomorphic gluing, positive boundary density, and integrable endpoint bounds. A paired horizontal Cauchy formula and dominated convergence reconstruct the transform without assuming that residual atoms are absent. The moving critical point is translated before applying dominated convergence.

Absolute convergence justifies the reciprocal-series rearrangement. Analytic power-series uniqueness identifies every moment, including the zeroth moment. The resulting measure is `volume.withDensity` of the proved nonnegative density. A pushforward gives the original parameter `x`; the enclosing support used here is `[0,64*x]`. The proof uses sufficient integrable power estimates rather than requiring the sharper logarithmic estimates.

## Build

Lean 4.34.1 and Mathlib v4.34.1 are pinned at the repository root.
On Windows, use a short checkout path, such as `C:/math`.

From the repository root:

```sh
lake exe cache get
lake --wfail build AperyMoments
lake script run certificates AperyMoments
lake script run audit AperyMoments
lake env leanchecker --fresh AperyMoments
```

`tests/Certificates.lean` checks the stated results and boundary cases.
`tests/Axioms.lean` lists the logical axioms used by the project.
