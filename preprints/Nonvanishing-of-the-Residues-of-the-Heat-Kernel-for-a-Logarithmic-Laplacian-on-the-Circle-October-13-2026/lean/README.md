# Circle logarithmic-Laplacian: every pole is genuine

This project formalizes the diagonal circle-kernel problem in Rosenzweig–Stanfill, *On the fundamental solutions of two nonlocal parabolic equations related to logarithmic Laplacians*, [arXiv:2606.04225v1](https://arxiv.org/abs/2606.04225v1), including the analytic bridge to its residue polynomials.

The concrete positive circle operator is integrated against angular arclength, with difference `f(z) − f(y)` and chord-distance denominator. Both Fourier signs have eigenvalue `μₙ = 4 Σⱼ<ₙ 1/(2j+1)`. For `Re(t) > 1/2`, the original bilateral diagonal spectral series equals the constructed kernel, with zero mode `1/(2π)` and paired positive-frequency factor `1/π`.

`CircleKernel.Main` proves:

- a global meromorphic continuation of that actual kernel
- its exact pole set `t = 1/2 − m`, for every natural `m`, including zero
- meromorphic order exactly `−1` at every such point
- residue `exp(−c/2) exp(cm) p₂ₘ(1/2−m)/(2π)`, which is nonzero, where `c = 4 log 2 + 2γ`
- analyticity everywhere else

The proof derives all-order Bernoulli eigenvalue asymptotics from the literal harmonic recurrence and a discrete tail estimate, proves parameter-uniform Bell remainders, and constructs compatible zeta-subtracted sums by local normal convergence. The residue factors use the unchanged `CircleResidues` arithmetic proofs, including the exact 2-adic valuation. No analytic continuation or residue formula is assumed.

Normalization follows the positive eigenvalues and spectral series in the paper's (1.2)–(1.3); the displayed integral (1.1) has inconsistent variables/signs. The normal-convergence bound proved here is `n^(−2σ−M)`, correcting the exponent typo in the proof of Proposition 2.8. These do not change the stated diagonal all-poles theorem.

## Build

Lean 4.34.1 and Mathlib v4.34.1 are pinned at the repository root.
On Windows, use a short checkout path, such as `C:/math`.

From the repository root:

```sh
lake exe cache get
lake --wfail build CircleKernel
lake script run certificates CircleKernel
lake script run audit CircleKernel
lake env leanchecker --fresh CircleKernel
```

`tests/Certificates.lean` checks the stated results and boundary cases.
`tests/Axioms.lean` lists the logical axioms used by the project.
