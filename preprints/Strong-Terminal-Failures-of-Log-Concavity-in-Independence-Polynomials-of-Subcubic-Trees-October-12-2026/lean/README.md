# Terminal log-concavity failures

Lean formalization accompanying the [manuscript](../article.pdf).

`MainTheorem.lean` proves `strong_terminal_failures`: for every positive integer pair `r, H`, the explicit release construction is a finite tree of maximum degree at most three, has at most `1200 (r+1)^4 (r+1+h)` vertices, and its last `r` interior independence coefficients violate log-concavity by a factor greater than `H`. Here `h` is the ceiling of `log₂(H+1)`.

`release_two_sided` proves the release's two-sided comparison estimate for every reversed coefficient from zero through `q`. The graph coefficients count actual independent vertex subsets; the independence number is Mathlib's `SimpleGraph.indepNum`. The proofs include the graph construction, polynomial identities, chain estimates, Gaussian comparison, and numerical transfer.

## Build

From the repository root, run:

```sh
lake exe cache get
lake --wfail build TerminalLogConcavity
lake script run audit TerminalLogConcavity
lake env leanchecker --fresh TerminalLogConcavity
```

The shared toolchain and dependency revisions are pinned at the repository root.
