# Exact verification for the mean--maximum inequality for forests

Author: Knowledge Sense

## Running the verification

Requires Python 3.11 or later, with no additional packages.
Extract all files into one directory. From that directory run:

    python -X utf8 verify.py . verification_results.json

The program prints its results and writes verification_results.json. A failed check raises an exception. The checks are not disabled by Python optimization flags.

## Contents and checks

- cone_certificate.json gives the 32 and 331 integer cone generators, the inverse-basis indices, and all root and generator-product decompositions. Every one of the 121540 operation records is verified exactly. All 2037 supplied bases are checked; 1029 are used by the operations. The empty vector and both recession rays are also checked.
- upper_witness_certificate.json gives the fresh-root construction and the full partition-function value and cardinality sum. The verifier reconstructs the 71308-vertex tree (maximum degree 8, independence number 48619), matches both full integers and the two root occupation maxima, and verifies the strict integer inequality 1000000 S < 473403 alpha Z.
- verify.py uses integer arithmetic and standard-library Fraction Gaussian elimination. For every basis record it verifies the inverse identity, nonnegative coefficients, and direct reconstruction of the image.
- verification_results.json records a successful run. The mean/maximum ratio of the witness is approximately 0.4734029757422598059645; the strict bound uses integers rather than this rounded value.

The accompanying manuscript explains why these finite checks imply the inequality for every finite forest; there is no vertex-count or degree cutoff. The data support the bounds 0.47 <= beta < 0.473403, without asserting the exact value of beta.

## Data integrity

SHA256 values, also embedded in verify.py:

    cone_certificate.json: 9fe1b777cfb6ba95a4fffdbb55bdaea356103b076f9db4d1b647e8224bdb4f3a
    upper_witness_certificate.json: a569d412c59356d4923ad4e78653ea04b6bc30f3f1e5d775dccc6a28afb5f89c
