# Numerical checks for Apéry polynomials

Author: Knowledge Sense

This supplement accompanies *Apéry polynomials as Stieltjes moment sequences*.
It integrates the density in Theorem 5.5 for the scaled sequence
`D_n(alpha) = alpha^n A_n(1/alpha)`, where `alpha = 1/x`.
The functions `components` return `h(w)`, `T(w)` and `J(w)` from the paper.
The lower part of the support uses the combination `2*T - h + 2*J`.
The support endpoint `S` satisfies `S/alpha = c_x`.

## Run

Use Python 3.10 or later; all dependencies are in the standard library.
Extract the three files into one directory and run:

```console
python check_density.py
```

The script prints ten JSON records and writes `density_checks.json` beside
the script. The supplied results were generated with Python 3.12.14.

## Files

- `check_density.py`: density integration and comparison with the polynomial coefficients.
- `density_checks.json`: the ten computed records.
- `README.md`: definitions and execution instructions.

## Computation and results

The tested values are `alpha = 1, 0.999, 0.5, 0.1, 0.01`, corresponding to
`x = 1, 1/0.999, 2, 10, 100`. Each record contains moments for `n = 0, 1, 2, 3, 4`.
Gauss-Legendre integration is performed at orders 192 and 384. Complete elliptic
integrals are evaluated by the arithmetic-geometric mean in the complementary
modulus convention. In particular, `spectral(c)` evaluates
`K(1-c*c/16)/(2*pi*pi)` in the parameter convention used in the paper.

`moments_D` contains the integrated moments, `exact_D` the polynomial values,
and `relative_errors` is `(moments_D - exact_D) / exact_D` for each entry.
The name `exact_D` identifies the defining finite polynomial, evaluated in
double precision in this script. `S` is the right endpoint for the scaled measure.

The largest absolute relative error across the 25 moments at order 192 is
3.084575799e-07; at order 384 it is 3.870359546e-08.
The low-support substitution is `q = sqrt(alpha)*exp(-z)` with `0 <= z <= 14`.
These finite, double-precision computations check the density formula at the
listed parameters. The proof for every real `x >= 1` and every integer `n >= 0`,
including endpoint limits, is given in the paper.
