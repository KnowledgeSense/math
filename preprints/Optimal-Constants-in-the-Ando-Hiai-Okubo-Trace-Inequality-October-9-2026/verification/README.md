# Trace-word verification

Use Python 3 with mpmath 1.3.0. Install the dependency with:

    python -m pip install -r requirements.txt

Then run:

    python trace_word_verification.py
    python manuscript_additional_verification.py

The first script checks exact rational exponent vectors against every cut,
the Ando–Hiai–Okubo splitting correspondence, and cyclic invariance. It also
evaluates two positive-definite examples in high-precision arithmetic.
The second checks the cyclic-interval formulation for equal B exponents and
reproduces the six-factor example's numerical table in 2000-digit arithmetic.
Each script writes its corresponding JSON results file.

The finite checks illustrate the formulas. The arbitrary-length statement
for all real nonnegative exponents is proved analytically in the [accompanying paper](../article.pdf). Numerical values are approximations.
