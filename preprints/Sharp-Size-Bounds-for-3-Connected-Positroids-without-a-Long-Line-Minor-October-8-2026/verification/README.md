# Exact diagnostics for the extremal constructions

Requirements: Python 3.10 or later. Only the Python standard library is used.

Run from this directory:

```text
python models_exact_checks.py
python models_contraction_checks.py
```

The first command checks 50 explicitly specified generalized-whirl, Family A,
and Family B constructions. It computes ranks by the exact free-extension rule,
tests all partitions for 3-connectivity, determines the maximum size of a simple
rank-two minor, and checks the global free-point rule and independence of the
extension order. It also checks the weak-image inequality used for contractions.
The second command compares every subset rank in 198 specified contractions
against the proposed lower-rank model, for 111,344 comparisons in total.

Each command raises an assertion error if any mathematical check fails. A
successful run writes the corresponding JSON result file. The included JSON
files were obtained by running these commands. These are finite diagnostics of
the constructions; the all-rank theorems are proved analytically in the paper.

Families and parameter choices are specified in the source. Ranks use exact
integers, with no numerical tolerance. These diagnostics do not enumerate all
positroids and do not establish the completeness of the equality classification.
