# Verification code

Run with Python 3.10 or later:

    python verify.py

Only the standard library is required. The command writes `certificates.json`.

The program checks the characteristic-three coefficient states over fields of orders 9, 27, 81 and 243 through n=20. It checks the switching construction over fields of orders 25, 49, 121, 125 and 81 using explicit polynomial-basis arithmetic, interpolation and all binary slices. It also computes the recursion counterexamples (q,n)=(7,10) and (19,8) by both quotient-ring arithmetic and weighted-output aggregation.

The JSON records field moduli, exchanged orbits, supports, interpolated coefficients and recurrence coefficients. All arithmetic is exact. These finite computations supplement the general mathematical proof.
