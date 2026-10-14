# Coefficient checks for power-related matrix weights

Author: Knowledge Sense

This supplement accompanies *Order-zero operators and irreducibility of
power-related matrix weights* by Knowledge Sense.

## Run

Use Python 3.9 or later. No third-party packages are required.

```text
python verify.py --output verification-results.json
```

The command checks 40 combinations: N=1,...,10, the two exponent lists L
and E, and two parameter lists. The parameter lists are all ones and
a_j=(-1)^(j-1)(j+1), indexed from j=1. Some combinations coincide in size 1.
The included JSON is the deterministic output of the command.

## Equations and rank certificate

The code constructs the coefficients of
P(x)=(I+xA) diag(x^s_1,...,x^s_N) (I+xA.T) in the original coordinates.
For odd j, A has a_j in position (j,j+1); for even j, in (j+1,j).
All other entries are zero. The lists are L=(0,0,1,...,N-2) for N>=2,
L=(0) for N=1, and E=(0,1,...,N-1).

Writing F=R+iQ, the equation FP=PF* becomes
RP-PR.T=0 and QP+PQ.T=0, with real R and Q. Each coefficient of x gives
integer linear equations. Gaussian elimination is exact modulo the prime
1000003. In each real system the rank is N^2-1, and in each imaginary
system it is N^2. A nonzero minor modulo this prime is nonzero over the
rationals and reals. The real identity is separately checked in the exact
integer kernel, so its presence also bounds the real rank by N^2-1.
Thus these ranks certify, for each selected case, a one-dimensional real
solution space spanned by I and a zero-dimensional imaginary solution space.
Equivalently, the selected cases have C_R(W)=R I for admissible W=wP.

These are finite checks of constant-matrix coefficient equations. They
supplement the manuscript's proof for every N and all nonzero real
parameters. The manuscript applies the irreducibility criterion and proves
the connection to operators of order zero, including unbounded intervals.
