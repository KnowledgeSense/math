# Verification of preorder support polynomials

Run `python verify.py` with Python 3.10 or later. Only the standard library is required. The program writes `certificate.json` next to the script and prints the results.

For every labelled reflexive, transitive relation on n≤5 elements, the program enumerates nonnegative integer vectors satisfying all order-ideal inequalities. It separately counts ordered, disjoint endpoint pairs admitting an upward bijection, compares the resulting gamma expansion with the support polynomial, extracts the gamma coefficients by triangular elimination, and checks reversal of the relation. The exhaustive total is 7,332 preorders.

It also checks support duality and full-support endpoint counting for 689 bipartite graphs with each side of size at most three, tests 100 seeded preorders with six to eight elements, and records an eight-element example. The random seed is 10072026. All arithmetic is integral. Matching tests check existence and count each endpoint pair once.

A successful run prints `"status": "PASS"`. A failed identity raises an assertion with the relevant relation and coefficients. The `seconds` field is elapsed running time and varies across machines. Finite computation supplements the general proof and does not establish it.
