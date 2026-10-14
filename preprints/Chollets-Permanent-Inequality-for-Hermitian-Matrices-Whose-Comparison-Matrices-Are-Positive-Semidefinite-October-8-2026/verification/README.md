# Exact verification of the forest coefficient formula

Requires Python 3 and SymPy (tested with SymPy 1.14.0).
Run: python forest_coefficient_exact_certificate.py
The program prints JSON with status PASS and checks nine coefficient identities on two rational complex examples by direct permutation expansion and by the forest formula. The output also records repeated edges, unicyclic and overfull components, zero masses, and the component mass bounds. The analytic theorem is proved in the accompanying manuscript; these finite examples do not prove the general result.
