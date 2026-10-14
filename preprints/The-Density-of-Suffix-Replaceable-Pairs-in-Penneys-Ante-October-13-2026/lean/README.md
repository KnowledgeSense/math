# Penney suffix-replacement density

A Lean 4 proof of the positive-density theorem for the Penney
suffix-replacement conjecture of Drexel–Peng–Richey.

## Main theorem

`suffix_replacement_positive_density` proves that the proportion of ordered
binary word pairs having the literal stopped-language replacement property
converges through all positive lengths. Its limit is at least

```
2^(-32) * (1 - 10 * 2^(-16)) > 0.
```

The same limit holds after excluding equal pairs, with either denominator
`4^n` or `4^n - 2^n`. The limit is also at most one.

`StoppedLanguage v w` is the set of finite contexts `u` for which `u ++ v`
has exactly one occurrence of `v`, at the final suffix, and no occurrence of
`w`. Empty contexts are included. `PropertyR` is equality of those actual
languages. `density`, `distinctDensity`, and `distinctNormalizedDensity`
count the original length-indexed binary-word pairs. No derived recurrence
or abstract sequence is substituted for those objects.

## Proof organization

- `Occurrences` and `ForbiddenSuffixes` prove the exact finite forbidden-suffix
  criterion from the literal infinite stopped-language definition
- `Localization` gives a complete deterministic exceptional cover
- `ForestCounting`, `BlockCounting`, and `PairEncoding` give exact finite-bit
  counts, including physically overlapping blocks in the same word
- `BoundaryMarginal`, `ExceptionalBounds`, and `Convergence` prove convergence
  of the entire original density sequence
- `MatchingCounting` through `PositiveLimit` prove strict positivity by an
  independent-boundary argument
- `DiagonalConvention` proves both distinct-pair normalization bridges

For positivity, the proof first passes to the finite independent boundary
marginals. A fixed `0^L`/`1^L` cylinder rules out every overlap shorter than
`2L`; each remaining overlap is a disjoint matching with at most one fixed
endpoint per edge. The exact constrained-assignment count yields the stronger
limit bound `2^(-32) * (1 - 8 * 2^(-16))`. This alternative argument avoids
assuming independence of physically overlapping portions of a single word.
The convergence proof still covers every original pair and every length.

## Build

Lean 4.34.1 and Mathlib v4.34.1 are pinned at the repository root.
On Windows, use a short checkout path, such as `C:/math`.

From the repository root:

```sh
lake exe cache get
lake --wfail build PenneyDensity
lake script run certificates PenneyDensity
lake script run audit PenneyDensity
lake env leanchecker --fresh PenneyDensity
```

`tests/Certificates.lean` checks the stated results and boundary cases.
`tests/Axioms.lean` lists the logical axioms used by the project.
