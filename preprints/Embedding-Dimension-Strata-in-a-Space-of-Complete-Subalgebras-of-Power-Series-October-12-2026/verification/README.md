# Generator-strata verification

Author: Knowledge Sense.

Python 3.12 and SymPy 1.14.0 are required. Install SymPy in the chosen environment, then run:

    python -X utf8 ri10_verification.py --output-dir results

The program checks the finite-jet monomial enumeration, the five triangular pivots, the A/B formulas and C coordinate, and finite-field algebra closure and cotangent ranks. It writes `ri10_symbolic.json` and `ri10_independent_results.json`. Successful execution means the assertions in these computations hold. The finite samples supplement the universal mathematical proof in the accompanying manuscript.
