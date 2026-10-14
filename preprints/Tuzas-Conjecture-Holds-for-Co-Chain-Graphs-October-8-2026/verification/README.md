# Verification supplement for Tuza's conjecture in co-chain graphs

Requirements: Python 3.10 or later and its standard library. No network access or optimizer is needed.

Run from this directory:

    python -B verify.py

Do not use Python's -O or -OO flags; the verifier checks this restriction.
Successful termination, exact assertion checks, and a JSON result with passed=true establish the finite verification described in the paper. A failed assertion or nonzero exit code means verification failed.

The verifier enumerates all 2,861 positive-part Ferrers profiles of order at most 12 with at least one odd part; 374,409 sparse scalar tuples after the analytic reduction; and 3,785,892 dense scalar tuples. It checks 11 small packing/cover witnesses, 61 sparse canonical packing witnesses, and the 30 required dense witnesses. Sparse residuals number 82; dense residuals number 70 with 73 integer edge-count values. The three witness collections total 102 records, with some overlap of graph cases.

The algebra checker verifies four exact dense quadratic identities, nine positive principal minors, and the threshold at N=88 using rational arithmetic. The graph checker validates every listed triangle, packing edge-disjointness, small covers, complete residual coverage, and the endpoint form of every large dense residual.

The analytic reductions, all-case covers, support-disjointness arguments, and canonical-subgraph transfer appear in the [accompanying paper](../article.pdf). Their role is to justify why this finite computation suffices for graphs of all orders.

Vertex labels: A={0,...,a-1}, B={a,...,a+b-1}. A degree profile lists cross-degrees of A in nonincreasing order. The two parts are cliques, and vertex i of A is adjacent to the first degrees[i] vertices of B.

The verifier reads inputs and does not modify them. Witness discovery is separate from certificate verification.
