# Exact checks for Dowling matroids with arbitrary joints

Author: Knowledge Sense

This package accompanies *Log-concavity of inverse Z-polynomials of Dowling matroids with arbitrary joints*.

## Run

Use Python 3.10 or later. All imports are from the standard library.

```text
python verify.py
```

The script prints `PASS` and check counts, and writes `verification_results.json` beside the script. A failed assertion gives a nonzero exit status. Run with assertions enabled, using the command above. The included JSON is the result of that command.

## Mathematical scope

For each integer n from 2 through 24, each m in {1,2,3,4,6,10,100,1000}, and every k from 0 through n, the script evaluates coefficient formulas with exact fractions. Here n is the number of vertices, m is the order of the gain group, and k is the number of joints. The case m=1,k=0 has rank n-1 and is checked separately. The other cases have rank n.

`B` evaluates the full-joint coefficient formula in Theorem 1.4. `expected` applies the joint-deletion and positive-decomposition formulas of Section 3. `weights` and `from_weights` evaluate the representations proved in Sections 4-6. The checks compare the representations, test positive integral coefficients and symmetry, verify strict log-concavity of coefficients and weights, and test the constant-coefficient formula of Theorem 1.2(iv).

For the trivial group with at least one joint, the checks also cover the finite attenuation sequence sigma, the coloop closed formula, and the normalized curvature comparison of Section 6. sigma_0 is assigned 1; the formula for sigma_h is evaluated only for 1<=h<=floor(n/2).

For the 22 examples in Table 1, the script separately generates the lattice of flats using the gain-graph rank and closure. It computes P and Z from their defining palindromicity recursion and Y by signed incidence inversion. This calculation is independent of the joint-deletion and generating-function formulas. It includes the noncommutative group S3 and compares it with C6, a commutative group of the same order. Six additional one-vertex cases check ranks zero and one.

These finite computations supplement the analytic proof. The proof in the paper establishes the result for every finite group and all permitted values of n and k.

## Files

- `verify.py`: verification program.
- `verification_results.json`: exact coefficients, counts, and results.
- `README.md`: instructions and scope.
