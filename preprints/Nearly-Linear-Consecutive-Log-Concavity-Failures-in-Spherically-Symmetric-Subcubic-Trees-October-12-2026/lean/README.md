# Consecutive failures in spherical trees

Lean formalization accompanying the [manuscript](../article.pdf).

`SphericalTreeFailures.nearly_linear_consecutive_failures` proves the full theorem for every positive real `η` and every integer `k ≥ 16384` satisfying `2^(-η) < k/(k+2)`. For the actual binary-core tree with fixed pendant-path length `2*k+1`, it gives consecutive strict log-concavity failures of length at least `C*|V|^(1-η)`, the stated interior bounds, and convergence of their maximum normalized location error to zero.

The construction uses finite `SimpleGraph` independent sets and the standard independence number. The proof includes tuning, a coupled hard-core law, the broadcast martingale and its L² limit, analytic positive densities, non-log-concavity, Fourier inversion, a uniform second-difference local limit theorem, and the integer-run transfer. `maxNormalizedError` is the finite maximum, with value zero on an empty set; the theorem's runs are nonempty for all sufficiently large depths.

The three subsequent application corollaries are not separately formalized: the fixed-gap Galvin consequence (`cor:galvin`), the extremal growth statements for `M₃(N)` and `M(N)` (`cor:extremal`), and the universal log-concavity endpoint bound `b_lc < 1 - 10⁻⁵` (`cor:blc`).

## Build

From the repository root, run:

```sh
lake exe cache get
lake --wfail build SphericalTreeFailures
lake script run audit SphericalTreeFailures
lake env leanchecker --fresh SphericalTreeFailures
```

The shared toolchain and dependency revisions are pinned at the repository root.
