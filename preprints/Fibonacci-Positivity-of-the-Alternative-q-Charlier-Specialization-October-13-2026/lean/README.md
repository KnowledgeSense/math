# Alternative q-Charlier positivity

This project formalizes strict positivity of every finite clone Schur word for
all real parameters `0 < ρ ≤ 1/4` and `0 < q ≤ 1/5`, including both upper
endpoints. The main results are `AlternativeQCharlier.cloneSchur_pos` and
`AlternativeQCharlier.all_finite_words_pos`.

The sequences `x` and `y` are the displayed alternative q-Charlier sequences of
Petrov and Scott, *Random Fibonacci Words via Clone Schur Functions*,
[doi:10.1017/fms.2025.10165](https://doi.org/10.1017/fms.2025.10165),
Conjecture 6.3. Sequence indices are zero based; the index `n` is the published
index `n+1`. The inverse power in the first entry is retained explicitly.
`A` and `B` are actual tridiagonal matrix determinants from Definition 2.5.
The clone Schur recursion is defined on runs of ones separated by twos, with a
proved encoding of every finite list in the two-letter alphabet.

The proof establishes the determinant recurrence, exact positive rescaling,
all-index parameter bounds, and finite tail estimates. It obtains the uniform
margin `25/88` for every normalized B determinant and then proves positivity by
word induction. No external positivity characterization or infinite-series
criterion is assumed.

## Build

Lean 4.34.1 and Mathlib v4.34.1 are pinned at the repository root.
On Windows, use a short checkout path, such as `C:/math`.

From the repository root:

```sh
lake exe cache get
lake --wfail build AlternativeQCharlier
lake script run certificates AlternativeQCharlier
lake script run audit AlternativeQCharlier
lake env leanchecker --fresh AlternativeQCharlier
```

`tests/Certificates.lean` checks the stated results and boundary cases.
`tests/Axioms.lean` lists the logical axioms used by the project.
