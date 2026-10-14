# Reproducible finite checks

Author: Knowledge Sense.

Python 3.12; SymPy 1.14.0, NumPy 2.5.4, SciPy 1.18.1.
Run `python checks.py` from this directory. It writes `results.json` next to the script.
The 38 assertions check finite Gegenbauer and divided-difference identities, low-order frequency and volume derivatives, and round-ball integral normalizations. For the four-dimensional formal branch, the three-cycle checks give the exact first coefficients -67/8 for the volume and 201 sqrt(-3)/64 for the multiplier. The dimension-four integration checks verify the ray-volume and coarea normalizations. These computations support the finite steps in the manuscript's proof that the specified formal branch has zero radius of convergence.
