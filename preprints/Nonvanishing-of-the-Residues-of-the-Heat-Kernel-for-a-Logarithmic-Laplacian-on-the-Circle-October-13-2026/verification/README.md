# Exact rational checks

Author: Knowledge Sense

This package accompanies *Nonvanishing of the residues of the heat kernel for a logarithmic Laplacian on the circle*.

Run `python verify_coefficients.py` using Python 3. The script uses only the standard library and writes `verification.json` beside itself. A successful run prints `all_passed: true`; a failed check raises an exception.

The calculations use exact rational arithmetic throughout. They check the nonvanishing and 2-adic valuation of `P_m` for `1 <= m <= 50`, the unique term of minimum valuation in all 683 partitions for `1 <= m <= 15`, and equation (5.4) for `1 <= m <= 12` at five rational shifts. They also compare the reflected `G` generating function coefficient by coefficient.

The Bernoulli numbers are computed from their defining recurrence, with `B_1 = -1/2`. The Bell coefficients are computed from the differential recurrence of their generating function. No rounded decimal arithmetic or third-party dependencies are used.

These finite checks supplement the proofs for all positive integers in Sections 2–3 and Section 5 of the paper. The included `verification.json` records a successful run and can be reproduced by running the script.
