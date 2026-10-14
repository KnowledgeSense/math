# Exact finite checks

Author: Knowledge Sense

Run `python check_semigroups.py` with Python 3.10 or later. No external packages or input files are required. The script writes independent_checks.json and independent_semigroups.json beside itself. Runtime is typically a few seconds.

It enumerates all minimal four-generated numerical semigroups with generators from 2 through 28, computes membership and Apéry representatives by residue shortest paths, and determines the minimal presentation count from the connected components of squarefree divisor graphs. The JSON `violations` list is empty on success; `counts.total` is 4771. Assertions additionally test boundary and socle counts, every legal ordered choice with generators at most 20, parameter-selection graph configurations and small order ideals. The examples include both equality cases and the additive upper-bound obstruction.

The finite range supplies reproducible evidence and does not replace the general proof.
