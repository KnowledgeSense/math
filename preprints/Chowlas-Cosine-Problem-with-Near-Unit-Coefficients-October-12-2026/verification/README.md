# Supplementary exact calculation

Author: Knowledge Sense

Requirements: Python 3.12 and SymPy 1.14.0.

    python -m pip install sympy==1.14.0
    python verify.py results

This writes results/certificate.json. The code reconstructs the local complex Fourier formula, proves the Taylor bounds on all 32 occupancy boxes using exact arithmetic in Q(sqrt(2)), and checks the rational absorption margin and final constants. A finite check of 4,095 supports supplements the analytic counting proof.

certificate.json records the exact quadratic forms, the center value, active-gradient absolute sum, quadratic remainder bound and lower/upper endpoints in every box. The grouped eight R upper bounds and four boundary J lower bounds are also listed. All assertion checks must pass. Decimal numbers are for display only.
