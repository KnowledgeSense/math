# Supplementary computations

Author: Knowledge Sense

This supplement contains the exact finite certificates and symbolic checks for the accompanying manuscript.
The mathematical proofs of the unrestricted ranges are in the manuscript; finite tests establish their specified ranges.

Requires Python 3.12, NumPy and SymPy 1.14.0. Extract the archive before running. Run each top-level program with
`python filename.py`, and boundary programs with `python boundary_moment_v1/filename.py` from the extracted directory.
Programs write JSON results beside themselves. Keep a copy of the supplied results for comparison.

- `certify_cyclic_finite_composition_v1.py`: all 3510 characters for 29<=n<=88, exact finite-field minors,
  denominator checks, root orders and characteristic-zero lifting data.
- `check_cyclic_uniform_origin_rank_v1.py` and `check_cyclic_bulk_moment_symbolic_v1.py`: exact identities
  supporting the unrestricted written arguments.
- The five `certify_boundary_*.py` programs: exact moment coefficient formulas and nonvanishing certificates.
  The other two boundary modules provide their symbolic operations.
- `verify_direct_rational_seed_v1.py`: the genuine rational seed at (d,s)=(11,14), Jacobian rank 896 modulo 32003,
  using `FINITE_SEED_RATIONAL_DATA_v1.json`.
- `check_inductive_ranges.py`: all 188 finite transitions through degree 84, the dimensional formulas,
  Cartesian determinant and algebraic inequalities used in the infinite induction. Its data is
  `data/compile_one_seed_bridge_v2.json`.

The manifest records SHA-256 hashes for the selected files. The supplied JSON certificates record
the exact outputs used by the manuscript.
