# Exact-integer diagnostics for caterpillar log-concavity

Run `python check.py` with Python 3. No external package is needed. The program writes `results.json` beside the script. Assertions stop execution on a mismatch.

The tests cover all normalized words of length 0-6 with entries 0-5 (55,987 words), all contracted kernels with 1-5 contractions and exponents 1-5 (19,525 kernels), and 102 partial sign-conditioned contraction comparisons in 15 selected words, evaluated at s=2,t=3 by independently enumerating the original and surviving charge colors. All calculations are exact integers. The value -9 in Remark 6.4 of the manuscript is also checked.

These bounded checks supplement the analytic proof. Arbitrary lengths and leaf counts are established by the lemmas in the paper.
