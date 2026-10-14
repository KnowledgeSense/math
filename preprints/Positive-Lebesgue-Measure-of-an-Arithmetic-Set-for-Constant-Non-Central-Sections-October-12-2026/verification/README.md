# Supplementary rational certificate

Author: Knowledge Sense

Run `python check_constants.py` using Python 3.12. Only the standard library is
required. A successful run prints PASS and writes check_constants.json.

The assertions verify the five initial inequalities for the explicit seed,
the strict source Theorem14(a) threshold, and the exact integer comparisons
used in the all-stage tail criterion. The code uses rational intervals for
pi, sqrt(2), and cosine values. Positive rational lower bounds certify each
comparison. The analytic proof covers all stages and all admitted parameters;
the program certifies finite arithmetic used in that proof.
