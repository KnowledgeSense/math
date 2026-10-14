# Exact rational examples for the reciprocal Jackson q-gamma kernel

Requires Python 3.10 or later and its standard library. From this directory, run:

    python verify.py > reproduced-results.json

A successful run prints a JSON object with `status` equal to `PASS`. The deterministic output can be compared with `results.json`.

The checks accompany Theorems 1.1 and 1.2, Corollary 1.3, and Propositions 3.3 and 4.1. They use exact rational arithmetic and compare elimination with the defining permutation sum for each determinant.

- For q = 1/4, 1/2, 3/4 and orders 1 through 4, 24 integer-node examples verify the determinant sign and the positive lower bound, including examples with the first x-node equal to zero.
- Twelve examples check the reciprocal finite-product kernel in Corollary 1.3, with the first n-node equal to zero.
- Twenty-four finite truncations check Proposition 4.1. The smallest truncation attains the fixed-term bound, which remains a lower bound for larger truncations.
- Twelve examples check polynomial minors with skipped degrees.

The illustrative two-by-two example has determinant −4/63, signed determinant 4/63 and lower bound 1/64. For integer y, the infinite-product ratio reduces to the finite product 1/(q;q)_(y−1). These finite examples supplement the manuscript's proof for arbitrary real nodes and every finite order.
