# Chowla's cosine problem with near-unit coefficients

Lean formalization accompanying the [manuscript](../article.pdf).

## Main statements

- `ChowlaCosine.chowla_cosine_minimum`: for every N ≥ 1, arbitrary distinct positive integer frequencies, and real coefficients in [0.99, 1.01], an attained global minimum in [0, 1) is at most −N^(1/9)/20.
- `ChowlaCosine.chowla_cosine_main` and `chowla_cosine_main_nat`: the explicit cosine-sum inequality for integer and natural frequencies.
- `ChowlaCosine.symmetric_chowla_minimum`: the symmetric-support theorem at an attained real minimum, with |A| ≤ 10⁸ K⁹.

The proof includes actual Haar-circle Fourier coefficients, convolution and Parseval estimates, weighted Roth and Shankar counting, universal continuous-box bounds for the local quadratic forms, the selector estimates, error absorption, and the original cosine/minimum normalization. The interval checks use kernel-checked reflection.

## Build

From the repository root, run:

```sh
lake exe cache get
lake --wfail build ChowlaCosine
lake script run audit ChowlaCosine
lake env leanchecker --fresh ChowlaCosine
```

The shared toolchain and dependency revisions are pinned at the repository root.
