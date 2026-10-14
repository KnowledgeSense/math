# Exact checks for generic valuation semigroups

Author: Knowledge Sense

Requires Python 3 and only its standard library.

```text
python verify.py --audit --output results.json
python verify.py 6 8 10
```

The audit checks 4,025 interpolation minors, 209 weight vectors against direct exponent-vector enumeration, 435 cases against the classical plane-branch genus formula, and 13 correlated exponential witnesses using exact integer elimination. The results include the arithmetic family and the five-generator semigroup in the earlier 2022 statement. Assertions fail on a mismatch. These finite computations are reproducible supplementary checks; the general proof is in the accompanying manuscript, Generic value semigroups with prescribed coordinate orders.

The second command prints the genus, conductor, full gap list, minimal generators and cutoff for the input coordinate orders. Equal coordinate orders remain distinct variables when counting monomials.
