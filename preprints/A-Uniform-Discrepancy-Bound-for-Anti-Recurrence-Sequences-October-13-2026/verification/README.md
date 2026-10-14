# Finite checks for positive anti-recurrences

Run python verify_bound.py with Python 3. No third-party packages or network access are required.

The program constructs complementary mex sequences using exact integers and checks the block identity, gap bound, rank inequalities, earlier-index condition, envelope inequality and final discrepancy bound.

It writes checks.json, reporting the parameters, number of checked indices and special cases. A failed assertion stops execution. The finite checks supplement the general proof given in the paper "A uniform discrepancy bound for anti-recurrence sequences" by Knowledge Sense.
