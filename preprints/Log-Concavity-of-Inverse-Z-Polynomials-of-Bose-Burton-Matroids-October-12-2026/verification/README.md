# Supplementary coefficient checks

Knowledge Sense

Run `python verify_coefficients.py` with Python 3.10 or newer; only the standard library is used. The script compares coefficients obtained from inverse KL incidence inversion and the Möbius definition with the signed kernel and positive expansion. It also checks symmetry, positivity, strict log-concavity and normalized concavity for the parameter grid recorded in the output. Finite computation supplements the general proof.
