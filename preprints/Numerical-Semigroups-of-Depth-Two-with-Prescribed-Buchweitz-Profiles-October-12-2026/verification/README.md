# Arithmetic checks for prescribed Buchweitz profiles

Author: Knowledge Sense

Run `python construction.py` with Python 3.10 or later. Only the standard library is used. The script writes `certificate.json` alongside itself and prints a concise account of the completed assertions. Any failed assertion terminates execution.

The `construct(N, B, target)` function implements the construction for a tuple of N-1 integers. The code parameter B corresponds to L in the paper. Its parameters are integers N>=2 and B>=1, with all target entries in [-B,B]. It returns C, the pairs (d,t), and the genus. The associated gapset is [1,m-1] union {2m-1-c: c in C}, with m supplied by `params(N,B)`.

The suite includes 574 exhaustive target tuples at small parameters and 30 additional profiles, direct truncated bitset sumset counts, three literal full-gapset counts, the reflection identity for 502 small sets C at eight degrees each, exact quotient comparisons at large parameters, and the example with Buchweitz set {3,6}. Randomized cases use a fixed seed. The certificate records counts, elapsed time, the source hash, and a digest of the numerical records.

All tests are finite. They check arithmetic instances and the implementation; the accompanying proof establishes the theorem for every allowed parameter and all degrees after the specified horizon. The genus in the construction is an explicit bound without an optimality assertion.
