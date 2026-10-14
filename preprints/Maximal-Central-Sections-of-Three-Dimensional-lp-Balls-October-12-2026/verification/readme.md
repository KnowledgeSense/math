# Maximal central sections of three-dimensional lp-balls: verification files

Author: Knowledge Sense

These files contain the saved interval enclosures, their C++ generators, exact Python checkers and mathematical derivations for the three-dimensional classification at every finite real p > 2.

## Check the saved certificates

From this directory, run with Python 3:

    python -X utf8 verify.py

Only the Python standard library is needed. The script first checks every distributed file against MANIFEST.json, then runs eight checks. Each must report PASS. It verifies closed-domain coverage and exact binary-rational inequalities. Results are written to results/.

## Relation to the manuscript

| Exponent range | Manuscript section | Files |
| --- | --- | --- |
| 2 < p <= 3 | Section 4 | components/near-two-and-large-exponents/logs/near2_local_full and near2_complement_full |
| 3 <= p <= 4 | Section 5 | components/three-to-four |
| 4 <= p <= 6 | Section 6 | components/four-to-six |
| 6 <= p <= 100 | Section 8 | components/near-two-and-large-exponents/logs/bridge_local_full and bridge_complement_full |
| p >= 100 | Sections 7 and 9 | components/near-two-and-large-exponents/logs/cube_far_bernstein.json and tail_chord_100.json |

The proof/ directory contains the underlying derivations. Appendix A gives the derivative identities, and Appendix B summarizes the certificates. The range 3 <= p <= 4 uses the corrected Hessian constants 9, 6, 2 and 1; the checker computes its variation from these constants.

## Regenerate interval enclosures

The generators in components/*/code use 80-bit MPFI intervals and MPFR directed rounding. They were run on 64-bit Linux with MPFI 1.5.4 and MPFR 4.2.2. Building requires a C++17 compiler and these libraries. For example:

    g++ -O2 -std=c++17 components/near-two-and-large-exponents/code/certify-near2-local.cpp -lmpfi -lmpfr -o local

The sources declare the Linux x86_64 ABI manually. When rebuilding, compare its type layout and rounding constants with the installed headers, retain the stated precision and do not use fast-math flags.

For the local 2 <= p <= 3 roots i = 0,...,39, run `local D i (i+1) PREFIX`, using integer indices. The complementary kernel uses `i (i+1) PREFIX`, i = 0,...,19. Local roots for 6 <= p <= 16 use `T i (i+1) PREFIX`, i = 0,...,4. Complementary roots for 6 <= p <= 100 use `i PREFIX`, i = 0,...,19. Use a fresh output directory for each generation. The root index ranges are half-open; the mathematical parameter boxes are closed.

The Python checks consume the complete supplied certificates. They check saved transcendental enclosures using the documented arithmetic semantics; generating new enclosures requires the C++ programs. This package uses exact postprocessing rather than a proof-assistant formalization.
