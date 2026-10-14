# Exact finite verification

Author: Knowledge Sense

This supplement accompanies *Enumeration of extendably 312-avoiding alternating sign rectangles*.

Run with Python 3.10 or newer from this directory:

    python verify.py

The program uses only the Python standard library and exact integer and rational arithmetic. It writes `verification_results.json` after all assertions pass. A mismatch stops execution with an assertion error.

The checks compare the formula in equation (1.1) with the recurrences in Proposition 2.3 on 10,416 admissible triples, and with the diagonal generating functions in Theorem 1.2 on 1,701 coefficients. Independently of the recurrences, the program generates all alternating sign matrices of orders 1 through 6 from monotone triangles, checks their defining conditions, and filters for 312 avoidance. It then counts distinct rectangular prefixes satisfying the alternating sign rectangle conditions for all 30 admissible triples with r,k at most 3.

These finite prefix counts exhibit extensions of order at most 6. They do not exhaust arbitrary extension orders. The manuscript provides the proof for the whole parameter domain.

The archive contains only this README, `verify.py`, and the result of a successful run, `verification_results.json`.
