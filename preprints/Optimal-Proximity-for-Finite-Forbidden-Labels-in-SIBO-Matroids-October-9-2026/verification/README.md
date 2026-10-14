# Finite verification for optimal SIBO proximity

Requirements: Python 3.10 or later; standard library only.

Run the following commands from the extracted directory:

```
python -X utf8 verify_manuscript_examples.py
python -X utf8 verify_finite_examples.py
```

The first script checks the cyclic construction used in the manuscript for all 781 size tuples with 0 <= k <= 4 and 0 <= q_t <= 4. It checks the forbidden-set cardinalities, the unique allowed number of elements from A in a uniform-matroid basis, and every nonempty interval length in the corresponding interval obstruction. It writes manuscript_examples.json.

The second script checks the equivalent mixed-radix construction for 341 tuples, genuine partition-matroid bases, and exhaustive interval obstructions in three small products of cyclic groups. It writes finite_examples.json. The JSON files included here were produced by these scripts.

All checks pass. These finite calculations supplement the manuscript's proofs. The universal statements about arbitrary finite SIBO matroids and abelian groups are established by those proofs.
