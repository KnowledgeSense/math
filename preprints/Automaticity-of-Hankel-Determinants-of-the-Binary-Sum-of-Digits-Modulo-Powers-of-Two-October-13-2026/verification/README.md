Exact finite checks for binary digit-sum Hankel determinants

Requires Python 3.10 or later and its standard library only (the script uses int.bit_count, available since Python 3.10).
Run: python -X utf8 verify_r57.py
The script computes defining determinants with integer Bareiss elimination, compares exact normalized recurrences, and checks finite annotated-word calculations. It writes verification_results.json. An assertion failure indicates a mismatch. Finite checks supplement the general proof; no minimal DFA is enumerated.

Files: verify_r57.py, verification_results.json, README.md.

The annotation attached to position i of an input word b_1...b_t is the pair (min(t-i+1, C), [b_i...b_t] mod 2^K) with C = max(K+1, 3), i.e. the suffix data of Lemma 5.5 in the paper.

Recorded run (verification_results.json, script_sha256 02c2718b6cb746b9234a119195b8933a02fb13a71e3056328a523df2e4c450c2):
- 351 exact comparisons of the normalized pair (Q, R) computed from the defining matrices with the recursion, 2 <= N <= 40, 0 <= r <= 8; Q odd and R with odd denominator in every case.
- 468 comparisons of the iteration modulo 2^K with directly computed D(N), 2 <= N <= 40, 1 <= K <= 12.
- 50,010 comparisons of the annotated-word calculation with the iteration, 0 <= n <= 5000, 1 <= K <= 10.
- 720 comparisons for long inputs of 3 to 2048 binary digits, K in {1, 2, 3, 5, 10, 16}.
- 1,440 perturbed annotations, each rejected by the local consistency check.
- mismatches: 0. All checks passed.
