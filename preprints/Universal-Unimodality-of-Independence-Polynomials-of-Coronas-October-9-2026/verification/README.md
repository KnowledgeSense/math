# Exact finite diagnostics

Run `python -X utf8 verify.py` and `python -X utf8 verify_prior.py` with Python 3.10 or later. Only the standard library is required. The programs write JSON to standard output and do not modify files. `expected_results.json` and `expected_prior.json` record the results.

The checks compare the corona formula with vertex-deletion recursion, verify the positive family, test exact rational balancing and rescaling identities, and check sufficient-threshold inequalities. The second program recomputes Lucas B.'s credited public K_1 example and checks the full coefficient-list hash. These finite diagnostics support implementation correctness; the general proof is in the accompanying manuscript.
