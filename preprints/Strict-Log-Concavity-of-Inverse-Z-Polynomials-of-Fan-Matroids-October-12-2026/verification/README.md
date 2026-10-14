# Exact verification of fan inverse-Z log-concavity

Author: Knowledge Sense

Run Python 3.8 or later with the command:

    python -X utf8 verification.py

Only the Python standard library is required. The script writes verification_results.json beside itself and prints the same results. A failed assertion stops execution and identifies the relevant indices.

All computations use integers and exact rational numbers. The checks compare the positive coefficient formula with the recurrence in equation (68) of Gao, Li, and Li, *Inverse Kazhdan–Lusztig polynomials of fan matroids*, arXiv:2603.25254v2.

The recorded run checks ranks 1–80, 3,320 fan coefficients, and 3,160 strict internal inequalities. It also checks 1,125 lower-half kernel positions, 13,525 kernel coefficients, 230 central positions, and 85 polynomial identities for the ratio comparison.

The finite computations corroborate the formulas and their boundaries. The proof for every rank and every positive kernel parameter is the analytic argument in the accompanying manuscript.

Files:

- verification.py: executable verification.
- verification_results.json: results of an exact run.
- README.md: instructions and scope.
