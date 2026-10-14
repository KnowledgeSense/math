# Supplementary verification

The density of suffix-replaceable pairs in Penney's ante

Author: Knowledge Sense

## Contents

- `verify.py`: direct finite-word checks of the suffix-generator criterion,
  localization outside the exceptional cover, and exact overlap probabilities.
- `independent_checks_result.json`: the output of `verify.py`.
- `count_r.c`: exhaustive counts for Table 1 using Proposition 2.2, including
  diagonal pairs as in Remark 2.3.
- `results_n1-15.txt`: Table 1 counts for lengths 1 through 15.

## Python checks

Requires Python 3.10 or newer and only the standard library. Run without `-O`:

    python verify.py

The script writes `independent_checks_result.json` beside itself. It compares
all 5,460 ordered pairs of lengths 1 through 6 with direct occurrence counting
on all contexts shorter than the target words. It also checks 472 localization
instances outside the exceptional cover and 29,408 exact overlap probabilities
for L = 1..8, n = 4L..64, and k = 1..n-1. A failed assertion identifies an
instance. The expected number of failures is zero.

## Table 1 counts

Use a C99-compatible compiler and the C standard library:

    gcc -O2 -std=c99 -o count_r count_r.c
    ./count_r 15 > results_n1-15.txt

On Windows, from a Visual Studio developer command prompt:

    cl /O2 /std:c11 count_r.c
    count_r.exe 15 > results_n1-15.txt

The argument is the largest length N; it accepts 1 through 20 and defaults to
15. Each length enumerates all 4^n ordered pairs, so the work grows by about a
factor of four per additional length. Use 8 in place of 15 for a smaller run.

The finite checks and table counts are supplements to the analytic proofs of
the limiting theorems in the manuscript. The proportions use all ordered pairs,
including identical words; the count of identical-word pairs is 2^n.
