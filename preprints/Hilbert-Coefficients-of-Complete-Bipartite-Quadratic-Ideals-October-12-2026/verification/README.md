# Complete-bipartite quadratic ideals: proofs and checks

Author: Knowledge Sense

The complete general proof is in kpq-proof.md, with the generator-packing argument in k2q-proof.md. These supplementary proofs give alternate derivations of the manuscript's results. In particular, kpq-proof.md uses the correction polynomials P, while the manuscript also derives a compact coefficient formula using truncated binomial sums. research-notes.md records definitions, boundary cases and primary references.

Run the exact checks with Python 3.11 or newer and SymPy 1.14.0:

    python -m pip install sympy==1.14.0
    python check.py --output certificate.json

The checks compare recursive packing with the closed formula, direct length counts, Hilbert coefficients, rational generating-function identities, and the normalized integral comparison. The fixed certificate records the finite parameter ranges; the proof documents establish the results for all parameters.
