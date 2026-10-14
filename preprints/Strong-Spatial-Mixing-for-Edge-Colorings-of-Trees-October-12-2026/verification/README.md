# Exact covariance checks

Author: Knowledge Sense

Run with Python 3.12: python injection_covariance_checks.py

Only the Python standard library is needed. The script enumerates weighted injections using rational arithmetic. It checks posterior second-moment identities, the Gram-matrix recursion, positive-cell bounds and cross-row squared covariance bounds in 12 finite examples (84 color blocks), with seed 20261012. It also displays a counterexample to an invalid matrix-product implication. The result JSON is saved next to the script. These finite checks supplement the analytic proof; they do not establish the universal SSM theorem.
