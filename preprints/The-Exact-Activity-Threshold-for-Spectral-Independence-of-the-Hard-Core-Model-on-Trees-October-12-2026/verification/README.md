# Exact cubic partition inequality: computational certificates

Author: Knowledge Sense

Python 3.10 or later; standard library only. Run:

    python check_cubic_intervals.py
    python check_independent.py

The first checker uses decimal fixed-point integers and an atanh logarithm
series; it writes the certificate to stdout. The independent checker uses
binary fixed-point integers, a Mercator logarithm series and symbolic derivative
generation; it writes independent_result.json and independent_cover.json.
All mathematical comparisons use directed integer intervals, not floating-point
sampling. Execution time is the only floating-point field and is omitted from
the archived certificates. Any failure raises an exception.

These files accompany "The exact activity threshold for spectral independence
of the hard-core model on trees" by Knowledge Sense. They certify the scalar
estimates (P1)–(P6) in Proposition 3.2, including algebraic constants, full
interval coverage and the coefficient bounds used near zero. Section 7 explains
the exact arithmetic and the remaining analytic bounds. The arbitrary-list
partition inequality, its application to forests and the spectral gap are
proved in the paper.
