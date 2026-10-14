# Algebraic verification

Run `python -m pip install -r requirements.txt`, then:

```
python verify_identities.py
python verify_spectral_factorization.py
```

The first script checks 38 exact identities: the Hessian term, gauge relation, rational residual, quadratic determinant, spectral factorization, scalar polynomial evaluations, and signs selected through endpoint formulas. The second script uses exact rational Laurent-polynomial arithmetic to check ten intermediate identities, including the spectral inversion at both endpoints. Every coefficient difference must be zero; failure raises an assertion.

These scripts verify algebraic consistency. The analytic inequalities, support argument, and extension to arrays of deficient rank are supplied in the mathematical proof.
