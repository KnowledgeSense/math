# Finite exact checks

Requires Python 3.12 and SymPy 1.14.0. Run `python verify.py`.

The script constructs Eulerian coefficients by the alternating-sum formula, independently reconstructs the reciprocal polynomials for n=1,...,18, and checks the thresholds and exact boundary multiplicities for n=3,...,18. Tangent numbers are generated independently using tan′=1+tan². Root counts and greatest common divisors use exact arithmetic.

Results are written to independent_R30_results.json. Assertions fail if a check fails. These are finite diagnostic checks; the proof for all degrees is in the accompanying manuscript. No network or input-file mutation is used.
