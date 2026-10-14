# Log-concavity of independence polynomials of caterpillars

This project proves that the independent-set counts of every finite caterpillar graph are log-concave.

For a path with `n` spine vertices, attach `m i` leaves to each spine vertex `i`. Let `i_k` be the number of independent vertex sets of size `k`. The main theorem proves

```text
i_(k-1) * i_(k+1) <= i_k^2
```

for every `n`, every leaf multiplicity function `m : Fin n → Nat`, and every `k ≥ 1`.

The counts are defined directly from the independent subsets of the graph. The proof establishes Schur positivity of the product of the two independence polynomials through transfer matrices and a finite sign interpolation formula.

## Build

From the repository root, run:

```sh
lake exe cache get
lake --wfail build R34
lake script run audit R34
lake env leanchecker --fresh R34
```

The shared toolchain and dependency revisions are pinned at the repository root.


## Main theorem

`R34.caterpillar_independentCounts_logConcave` in `R34/Main.lean` proves the inequality for the counts in `R34/CaterpillarCounts.lean`. `Audit.lean` displays its type and axiom dependencies.
