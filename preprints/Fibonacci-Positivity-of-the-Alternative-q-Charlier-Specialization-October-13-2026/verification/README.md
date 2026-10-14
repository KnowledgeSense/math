# Verification for the alternative q-Charlier positivity note

Author: Knowledge Sense

This package accompanies *Fibonacci positivity of the alternative q-Charlier specialization*. It contains `verify.py`, the reference output `results.json`, and this README. It uses Python 3.10 or later and requires no third-party packages.

Run from the extracted directory:

```sh
python verify.py
```

To save the output:

```sh
python verify.py > reproduced-results.json
```

A successful run prints a JSON object with `"result": "pass"`. The output is deterministic and can be compared with `results.json`. A failed equality or inequality raises `AssertionError` and returns a nonzero exit status.

All calculations use exact rational arithmetic. The script compares the original coefficients with their factorization (Lemma 3.1), evaluates the two normalized determinants by Gaussian elimination independently of their closed expansions (Lemma 2.3), and checks the bounds of Lemma 4.1 and Proposition 4.2. It also computes the original and normalized clone Schur values from Definition 2.1 and checks their rescaling relation and the lower bound in Section 5.

The parameter pairs are `(rho,q)=(1/4,1/5)`, `(1/8,1/10)`, and `(1/100,1/5)`. The sequence checks use indices 1 through 16. The determinant checks use `0 <= ell <= 6` and `0 <= m <= 5`. The word checks include all words of weight at most 8, including the empty word, at shifts 0, 1, and 5. The three illustrative values in the Japanese explanation use the separate sequence `t_0=0`, `t_k=1/4^k` for `k>=1`.

These finite calculations supplement the paper. The uniform estimates and induction in the paper prove strict positivity for every finite Fibonacci word and every nonnegative integer shift, throughout `0<rho<=1/4` and `0<q<=1/5`. The script does not enumerate the infinite family or determine the largest positive parameter region.

Reference: L. Petrov and J. Scott, *Random Fibonacci words via clone Schur functions*, Forum of Mathematics, Sigma 14 (2026), e15, DOI: 10.1017/fms.2025.10165.
