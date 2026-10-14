# Verification of the exceptional pair in Sun's circular-permutation problem

This archive supplies the exact finite certificates for all 2,693 prime-power orders that fail the sufficient Hamiltonicity inequality in the range 8 <= q <= 25,000,000. It checks all 659,460,173 nonzero offsets. The zero offset and the infinite tail are proved in the accompanying paper.

Requirements: Python 3 (standard library only) and a C++17 compiler.

    python run_review.py --compiler g++

For Zig, use --compiler with the zig executable. The optional --work-directory argument sets the output directory. No network access is used. The default output directory is run/.

MANIFEST.json binds every source and input. certificate_inputs.json stores the original ASCII bytes of 8,083 input files by basename; the runner reconstructs these files in the output directory. expected_reports.json supplies the exact per-field expected results. Two integer sieves independently regenerate the complete six-column residual catalogue. The field verifier checks arithmetic, the full multiplicative orbit, every offset, and the exact unresolved sets. A separate direct-order verifier checks 30 explicit cycles and the forced-cycle obstruction for (11,2).

Expected totals: fields 2693; nonzero offsets 659460173; compact positive certificates 659460142; explicit positive cycles 30; negative pairs 1; additional candidate checks 1302. RESULT.json and FIELD_REPORTS.json contain the results. The only negative pair is (q,a)=(11,2).

Positive certificates assert existence by the construction lemmas in the accompanying paper. Failure of a compact witness family does not assert nonexistence. Positive fallback cycles include their closing edge. Primitive outputs may repeat.

## Exact arithmetic and file identity

The residual catalogue is AUDITED_RESIDUAL_ORDERS.csv. Its SHA-256 with LF line endings is f9dd4318c6136d78d1d59011d67a2ce75d384d07fb83a96fd54cd8880257d60b. The SHA-256 of source/verify_field.cpp is 02c1e7b330f69cff319fa34dbe75526ca678361b8b59deb6451e7111dbbff481. MANIFEST.json records the hashes and byte lengths of all files in this archive.

The finite order test is (phi(q-1)-2)^2 < 9 * 4^omega(q-1) * q for 8 <= q <= 25,000,000. In this range omega(q-1) <= 8 and both sides are below 6.25e14; unsigned 64-bit arithmetic represents the comparison exactly. Stage lengths are the fixed prefixes recorded in CERTIFICATES.tsv and extras_q.tsv; the replay uses those exact values.
