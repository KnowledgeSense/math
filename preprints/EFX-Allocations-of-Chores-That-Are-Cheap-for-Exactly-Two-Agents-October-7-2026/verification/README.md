# Finite verification for M2 chore EFX

Requirements: Python 3.10 or later, standard library only.

Run from this directory:

    python verify_m2.py

The program implements the permitted-assignment flow, finite global minimization,
and repair cases of the M2 construction. An independent checker tests the resulting
allocations, including conservation of every chore. Each EFX comparison is an
affine inequality in r; the checked outputs satisfy it for every real r >= 2.

It enumerates all numbered-vertex multigraph edge multisets for n=2 (m<=12),
n=3 (m<=10), n=4 (m<=10), n=5 (m<=5), and tests 4,000 random instances with
n=5..9 and m<=7n using seed 20261007. Seven explicit branch certificates and
one token-branch instance are also tested.

The expected summary is 15,325 construction runs and 333,376 ordered affine
comparisons, with status PASS. These counts include repeated constructions for
the branch certificates and are not counts of distinct graph isomorphism classes.

The seven certificates are in data/branch_cases.json. The program independently
checks their initial-state global minima and final witnesses. It writes
independent_results.json; on a construction failure it also writes failure.json.
Expected mathematical results are recorded in expected_results.json.

Finite testing supports the construction and does not establish the universal
theorem for arbitrary n and m. The manuscript contains the general proof.
