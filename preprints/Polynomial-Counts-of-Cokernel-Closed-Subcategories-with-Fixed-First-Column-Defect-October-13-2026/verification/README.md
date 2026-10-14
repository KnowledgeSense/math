# Finite examples for fixed-defect enumeration

Author: Knowledge Sense

Run `python verify_finite.py` with Python 3.10 or later. Only the standard
library is required. The program writes `finite_verification.json` beside
the script and prints the same data.

It checks the equivalence of the point closure and ordered graph rules for
every point subset at n=0,...,4, enumerates all normalized templates for
i=0,...,3, and compares the resulting shifted-binomial formula with direct
counts within that range. Assertions fail if the finite comparisons differ.
The highest template count is also checked against (2i)!/i! for i<=3.

The structural proof establishes the general theorem. These computations
provide finite examples and consistency checks.
