# Strong spatial mixing for edge colorings of trees

Lean formalization accompanying the [manuscript](../article.pdf).

The release theorem concerns every positive ε and sufficiently large maximum
degree Δ, with at least `((3 + sqrt 5) / 2 + ε) * Δ` colors. Its domain is all
finite trees and all feasible pinnings on a common edge set. The decay rate
depends only on ε; the multiplicative constant may depend on Δ, q, and ε.
Distances are measured in the line graph. No later threshold, general-graph
claim, or arbitrary-list coloring theorem is included.

## Principal declarations

- `release_main_theorem : ReleaseMainTheorem`: the original strong-spatial-mixing theorem
- `MatrixTrickleDown.WalkHierarchy.matrix_trickle_down`: the full matrix bound
- `WeightedInjection.column_covariance_bound`: the actual weighted-injection
  covariance estimate, including zero weights
- `release_parameter_choice`: the original asymptotic threshold and uniform
  scalar parameter bounds

All declarations are in the `EdgeColoringMixing` namespace. The counting
modules define actual proper edge colorings, normalized conditional laws,
and the finite-tree message recursion. `MainTheorem.lean` combines the
covariance estimate, arcsine-metric contraction, two-level interpolation buffer,
and the exact counting identities.

## Build

From the repository root, run:

```sh
lake exe cache get
lake --wfail build EdgeColoringMixing
lake script run audit EdgeColoringMixing
lake env leanchecker --fresh EdgeColoringMixing
```

The shared toolchain and dependency revisions are pinned at the repository root.
