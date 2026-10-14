# Power-related matrix weights

Lean 4 formalization of the power-related matrix-weight theorem. For every positive size, every nonzero path parameter,
and both exponent schedules, the order-zero differential-operator algebra
consists exactly of complex scalar matrices. The constant weight-symmetric
matrices are exactly the real scalar matrices, and the weight admits no
nontrivial constant-congruence block reduction.

## Objects and scope

`pathMatrix` is the manuscript's alternating-row nearest-neighbor matrix,
with zero-based indices. `factor` is `I + x A`; `polynomialWeight` is
`(I + x A) diag(x^s_i) (I + x A)*`; `weight` multiplies its actual evaluation
by the scalar weight. `Schedule.printed` has exponents `(0,0,1,...)`, and
`Schedule.example` has exponents `(0,1,2,...)`.

`AdmissibleWeight` requires a positive scalar weight and positive diagonal
powers almost everywhere, with finite absolute moments of every order.
The domain is any nonempty open real set, so all nonempty open intervals,
including unbounded intervals, are included. No uniform positive-support
restriction is imposed; size one and the printed size-two case retain the
original admissible negative supports.

`orthogonalSequence` constructs the genuine monic matrix orthogonal
polynomials by inverting each finite positive-definite moment Gram matrix.
`InOrderZeroAlgebra` means the literal right-acting polynomial
multiplication eigenoperator condition for this sequence. The classification
also holds for every other sequence satisfying the same genuine monicity
and orthogonality conditions.

The main results are `power_relation_weight_theorem` and
`order_zero_algebra_eq_scalars`. The former includes existence, classification
for every orthogonal sequence, weight symmetry, and irreducibility.
The polynomial-weight bridge uses a finite weighted polynomial-square
argument, rather than a moment-determinacy or bounded-support assumption.

## Build

Lean 4.34.1 and Mathlib v4.34.1 are pinned at the repository root.
On Windows, use a short checkout path, such as `C:/math`.

From the repository root:

```sh
lake exe cache get
lake --wfail build PowerWeights
lake script run certificates PowerWeights
lake script run audit PowerWeights
lake env leanchecker --fresh PowerWeights
```

`tests/Certificates.lean` checks the stated results and boundary cases.
`tests/Axioms.lean` lists the logical axioms used by the project.
