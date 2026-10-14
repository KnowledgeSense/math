# Checking and update costs in random-walk search

Lean formalization accompanying the [manuscript](../article.pdf).

## Main results

The public entry point is `RandomWalkSearch.lean`. In namespace
`RandomWalkSearch.Cycle`:

- `free_restoration_main` proves the universal `c/L + a/N ≥ 1/64` bound,
  its explicit `L/128`-checks-or-`N/128`-updates consequence, and the independent
  coordinate bounds `c ≥ k/32` and `a ≥ L/64`.
- `consecutive_main` proves the universal `c/L + sqrt(a)/N ≥ 1/(64b)` bound
  and `a ≥ L²/(8192b²)`.
- `endpoints_main` supplies four actual one-setup policies, with certain success
  on every translate, deterministic check bounds, and update/check cost bounds
  `(4(L−1),L)`, `(4(N−1),k)`, `(2L²,L)`, and `(2N²,k)`.
- `no_uniform_split_main` proves the no-uniform-single-marked-cost-split corollary
  at the source threshold `k ≥ max(16(b+1),66C)`, using actual uniform-start
  hitting time and actual marked-set mass.
- `marked_mass_real_exact` proves the exact mass identity
  `1/k + 1/k² − 1/k³` from the concrete interval/progression union.

Here `L=k²`, `N=k⁸`, and the transition probabilities are exactly `1/4,1/2,1/4`.
The universal theorems quantify over arbitrary measurable private randomness
and arbitrary adaptive history policies, with no finite-policy or runtime bound.
Divergent executions and infinite expected operation counts are included;
outputs need not have been visited or checked. The coordinate bounds do not
require the other cost to be finite.

## Proof content

The development proves consistency completion, first-positive-answer coupling,
full infinite-transcript exposure, genuine budget truncation, and integration
of the resulting uniform-translate bounds. It derives measurability of runs,
success, and costs from coordinate-measurable randomized policy decisions.

For consecutive trajectories, the actual endpoint table and consumed tape
prefixes are tracked. The finite-horizon lazy range bound is proved from a
maximal-process potential and finite Cauchy–Schwarz. Actual stopping-time
semantics give expected symmetric exit time `2r²` and almost-sure finite exit.
Restoration frontier retries have genuine expected waiting time `4r`.

Endpoint witnesses run on an explicitly constructed product probability space:
a uniform setup vertex independent of an infinite iid uniform four-symbol tape.
The policies' legality, success, measurability, and operation counts are proved.

For the no-split corollary, the proof derives the sufficient bound `H≤2L²` for
the actual hitting time. It does not require or claim the auxiliary sharper
closed-form hitting-time identity in the paper. No expected cost is defined by
its claimed closed formula.

## Build

From the repository root, run:

```sh
lake exe cache get
lake --wfail build RandomWalkSearch
lake script run audit RandomWalkSearch
lake env leanchecker --fresh RandomWalkSearch
```

The shared toolchain and dependency revisions are pinned at the repository root.
