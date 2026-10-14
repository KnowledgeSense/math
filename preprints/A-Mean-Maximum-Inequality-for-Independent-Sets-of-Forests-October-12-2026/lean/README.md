# Mean–maximum inequality for independent sets of forests

Lean formalization accompanying the [manuscript](../article.pdf).

The main declarations concern actual finite graphs and independent sets:
- `mean_maximum_inequality`: every finite forest, including the empty forest,
  has mean independent-set size at least `47/100` times its independence number.
- `Release.invariant_cones_exist`: invariant cones with exactly 32 and 331 distinct primitive
  integer generators, each coordinate of absolute value below `2^87`.
- `weak_peak_limits`: the normalized minimum weak-local-peak sequences over forests
  and trees both converge to the infimum `beta` of mean/independence-number ratios
  over nonempty finite trees, and `0.47 ≤ beta < 0.473403`.

The peak-limit proof uses exact tilted cardinality laws, a bipartite binomial-mixture
identity, local binomial estimates, and uniform variance control. No external
unimodality or log-concavity theorem is assumed. The included
`HardCoreActivityThreshold` sources are the necessary dependency closure from the
hard-core activity threshold formalization of the same fixed release; their proved
arbitrary-degree forest correlation estimate supplies the variance bound.

## Build

From the repository root, run:

```sh
lake exe cache get
lake --wfail build MeanMaximumForests
lake script run audit MeanMaximumForests
lake env leanchecker --fresh MeanMaximumForests
```

The shared toolchain and dependency revisions are pinned at the repository root.
