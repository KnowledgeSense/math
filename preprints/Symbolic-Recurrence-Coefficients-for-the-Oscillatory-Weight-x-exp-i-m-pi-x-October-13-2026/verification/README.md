# Exact checks for symbolic recurrence coefficients

Author: Knowledge Sense

This package accompanies *Symbolic recurrence coefficients for the oscillatory weight x exp(i m pi x)*. It reproduces the finite calculations reported in Section 7 and Table 1, and the coefficient comparison with Lyu and Zhou, arXiv:2607.19797v1, Appendix C(4).

Use Python 3.10 or later. No external packages or network access are needed.

```text
python verify.py
```

The command writes `verification-results.json` and `constructed-polynomials.json` next to the script. The copies supplied in this package are the expected results. To preserve them while rerunning:

```text
python verify.py --output-dir rerun
```

The script computes the moment polynomials M_r and the Hankel and one-column bordered determinants H_n and J_n for n=1,...,10. Bareiss elimination uses integer polynomial arithmetic and checks every division for an exact quotient. Rational normalization constructs the G_j polynomials. Arrays list coefficients from constant term to highest degree; a string such as "3/2" is an exact fraction.

Successful execution prints `all_checks_passed: true`. All 50 entries of Table 1 match, and all 102 coefficients of the 11 printed appendix polynomials match. The script also checks the constant terms, the factor z in n(n+1)H_n-J_n, the low-degree values F_2 and F_3, and the normalizing-constant ratios needed in the recurrence formulas. A mismatch raises an assertion error and stops execution.

These are finite exact checks. The accompanying paper proves the formulas for all stated indices and all nonzero integer m: the alpha formulas have k>=2, and the beta formulas have k>=1, with eta=m*pi. The general proof appears in Sections 3-6 of the paper.

Reference for the appendix fixture: Shulin Lyu and Xun Zhou, *Recurrence coefficients of the orthogonal polynomials for oscillatory Jacobi-type weight functions* (2026), https://arxiv.org/abs/2607.19797v1, Appendix C(4), PDF page 21. The fixture records coefficients of polynomials in z=eta^2; the printed 2G_8 and 2G_11 are divided by 2 before comparison.
