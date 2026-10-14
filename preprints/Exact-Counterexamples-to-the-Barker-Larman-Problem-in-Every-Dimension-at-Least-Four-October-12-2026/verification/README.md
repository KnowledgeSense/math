# Reproducible finite checks

Author: Knowledge Sense.

Python 3.12; SymPy 1.14.0, NumPy 2.5.4, SciPy 1.18.1.
Run `python checks.py` from this directory. It writes `results.json` next to the script.
The 38 assertions cover symbolic Gegenbauer coefficients, low-order twist and volume derivatives, divided-difference factors, algebraic three-cycle coefficients, and round-body integral normalizations. Each assertion must succeed. These computations supplement the mathematical proofs of all-degree estimates and infinite-dimensional convergence.
