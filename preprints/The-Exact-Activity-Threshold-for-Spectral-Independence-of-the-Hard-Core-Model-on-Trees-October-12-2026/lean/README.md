# Hard-core activity threshold

Lean formalization accompanying the [manuscript](../article.pdf).

- `HardCoreActivityThreshold.main_a_spectral` proves uniform complete spectral
  independence and a positive size-normalized heat-bath gap for all finite
  forests and all positive activities below any fixed cap strictly below the
  critical activity.
- `HardCoreActivityThreshold.main_b_spectral` proves the simultaneous supercritical
  conclusion on actual finite, unpinned, constant-activity trees: arbitrarily
  large influence spectral radius and arbitrarily small size-scaled gap,
  including at the critical activity.

The laws are normalized hard-core probabilities, influence radii are complex
matrix spectral radii, and the transition is the random-scan heat-bath kernel.
Its stochasticity, reversibility, conditional-variance Dirichlet form, and exact
restriction to the positive-probability state space are proved. The gap is one
minus the second-largest transition eigenvalue, counted with multiplicity,
with value one for a one-state chain. Equality with the Poincaré variational
gap and equality of characteristic polynomials under the symmetric similarity
are proved.

The cubic partition inequality uses kernel-checked rational estimates for the
actual real functions. Forest probability recursions, all fields and pinnings,
finite-tree marginal gadgets, low-activity variance tensorization, and the
finite revealing argument for the lower gap are proved within the project.
There are no assumed analytic, probabilistic, or numerical certificates.

## Build

From the repository root, run:

```sh
lake exe cache get
lake --wfail build HardCoreActivityThreshold
lake script run audit HardCoreActivityThreshold
lake env leanchecker --fresh HardCoreActivityThreshold
```

The shared toolchain and dependency revisions are pinned at the repository root.
