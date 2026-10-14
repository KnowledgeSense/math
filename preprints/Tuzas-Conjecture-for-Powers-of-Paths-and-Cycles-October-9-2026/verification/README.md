# Supplementary files

Supplementary material for the paper *Tuza's conjecture for powers of paths and cycles* by Knowledge Sense. Section, table and equation numbers below refer to that paper.

## Requirements

Python 3.10 or later, standard library only. No network access or external solver is needed. The programs read their inputs without modifying them, print a JSON summary, and exit with code zero when every check passes.

## How to run

After extracting the archive, change to its root directory (the directory containing this file) and run:

```
python cochain/verify_full_candidate.py
python verify_path_cycle.py
```

The scripts locate their data files relative to their own location, so they may also be started from another directory by giving their full paths.

The first command takes about one minute on a current personal computer; the second takes a few seconds.

## Correspondence with the paper

| File | Role in the paper |
|---|---|
| `cochain/packing_bounds.py` | The functions C and J (Section 2); the packing bounds (S1) to (S9) of Lemma A.9 with the cover size T_sp of Lemma A.7; the bounds (D1) to (D6) of Lemma A.14 with T_0, S_0 = P_F - e and the interval (A.5) |
| `cochain/verify_dense_algebra.py` | The polynomial identities in the proof of Proposition A.15, the data of Table A.2 (points, values, linear forms, matrices and their leading principal minors), and the value 13/12 at N = 88, in exact rational arithmetic |
| `cochain/verify_full_candidate.py` | Runs `verify_dense_algebra.py`; performs the computation of Proposition A.5 (2,861 profiles, 2,850 settled by Lemmas A.1 and A.2) and checks the 11 certificates of Table A.1; performs the computations of Propositions A.12 and A.16 and asserts the counts 374,409, 929, 82, 3,785,892, 70 and 73; checks the 61 packings of Table A.3 and the 30 packings of Table A.4 |
| `cochain/small_exception_certificates.json` | The 11 packings and covers of Table A.1 (Proposition A.5) |
| `cochain/sparse_scalar_failures.json` | The 82 sparse tuples left after the bounds (S1) to (S9) (Proposition A.12) |
| `cochain/sparse_canonical_certificates.json` | The 61 packings of the canonical graphs F of Lemma A.8, listed in Table A.3 |
| `cochain/dense_scalar_failures.json` | The 70 dense tuples with a nonempty interval (A.5), containing 73 values of e (Proposition A.16) |
| `cochain/dense_canonical_certificates.json` | The 30 packings of the canonical graphs F_e, listed in Table A.4 |
| `verify_path_cycle.py` | Recomputes Table 4.1 as exact polynomial identities and checks (2.4) and 2m(k) >= floor(k/2) for 7 <= k <= 10,000. Also checks, on finite ranges of n, Lemma 4.4, Propositions 5.5 and 5.6, the count in Lemma 5.3 and Lemma 3.2. These finite checks corroborate Sections 4 and 5, whose proofs do not depend on them |

## Labelling in the certificate files

A co-chain graph with parameters a, b and profile d has vertices 0, ..., a+b-1. Vertex i < a is a_{i+1}, vertex a+j is b_{j+1}, and {i, a+j} is an edge exactly when j < d_{i+1}. This is the labelling of Table A.1. The packings were found by a search program, which plays no role in the proof; only the listed triangles and the elementary checks in the programs are used.

## Inputs not verified by the programs

The existence of Skolem and hooked Skolem sequences (Theorem 2.6), the triangle packings of complete graphs of Feder and Subi (Lemma 2.2), the theorem of Chahua and Gutierrez for co-chain graphs with two even cliques (Theorem A.4), and Tuza's conjecture for graphs of treewidth at most six (Botler, Fernandes and Gutierrez, Theorem 3.4) are mathematical inputs and are not verified by the programs.
