# Finite verification

Author: Knowledge Sense

Run with Python 3.12: python verify.py
Only Python standard-library modules are required. The program enumerates all four Kunz coordinates in 1..24, checks the three-generator Apéry and first-relation tables, and performs exact rational elimination on all monomial jets for each proposed three-coordinate construction.

Expected counts: 331,776 tuples; 71,970 semigroups; 2,222 distinct (a,b) pairs; 3,220 exact jet checks. Assertions must all pass. Counts by the dimension criterion are descriptive: exclusions of arbitrary analytic parametrizations are proved in the general necessity argument, not established by this finite experiment.

The program writes verification-result.json beside verify.py. The output is deterministic: rerunning the unmodified program reproduces the included JSON byte for byte. The dimension_by_criterion_counts field records the dimensions assigned by the manuscript's criterion.
