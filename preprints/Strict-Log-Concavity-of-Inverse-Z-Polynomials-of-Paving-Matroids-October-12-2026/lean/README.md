# Inverse-Z log-concavity for paving matroids

`Paving.paving_inverseZ_main` proves the ordinary inverse-Z theorem for every
finite loopless paving matroid of positive rank. The polynomial has its
matroid rank as degree, every supported coefficient is positive, the row is
symmetric, and every internal log-concavity inequality is strict. Rank one
has no internal inequality. All ranks and ground-set sizes are allowed,
including free matroids, coloops, and disconnected matroids.

The object is an actual `Matroid α` on a finite ambient type, with arbitrary
ground set. `IsPaving` is the circuit-size definition: every circuit has at
least the matroid rank. The polynomial is
`MatroidInverseZ.matroidInverseZ`, evaluated on the actual ranked flat
lattice and linked to the verified KL incidence characterization.

The proof derives the uniform coefficient formula and paving subtraction
identity rather than assuming them. It proves the actual hyperplane packing
and intersection bounds, evaluates Boolean and uniform restriction
intervals, sums the upper Möbius factors, and separately evaluates the even
central inverse-Q correction. The resulting exact coefficients are
identified with normalized mixtures whose inequalities are proved using
the actual matroid weights. Rank-one and rank-two boundaries are proved
directly. Coefficients above rank vanish independently of the auxiliary
reflected rows.

The `ThagomizerTuran` modules provide the generic incidence-invariant
foundations and reversal argument.

## Build

Lean 4.34.1 and Mathlib v4.34.1 are pinned at the repository root.
On Windows, use a short checkout path, such as `C:/math`.

From the repository root:

```sh
lake exe cache get
lake --wfail build Paving
lake script run certificates Paving
lake script run audit Paving
lake env leanchecker --fresh Paving
```

`tests/Certificates.lean` checks the stated results and boundary cases.
`tests/Axioms.lean` lists the logical axioms used by the project.
