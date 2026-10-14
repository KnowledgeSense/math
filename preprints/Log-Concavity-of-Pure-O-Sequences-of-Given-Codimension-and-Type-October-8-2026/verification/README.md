# Exact verification of the pure O-sequence constructions

Requirements: Python 3, standard library only.

Run `python verify.py` after extracting this archive. It writes recomputed_certificate.json and terminates with exit code 0 when all exact assertions hold.

The program generates the full rank polynomial of a union of divisor boxes using disjoint coordinate slices. It also enumerates every exponent vector in the type-three witness's bounding box, checks downward closure and its three maximal elements, and compares the two rank counts. The displayed witness has degree 76, rank triple (532,509,487) at degrees 54,55,56, and defect -3.

The further parameter checks cover 88 choices across the three negative families and 12,012 three-variable pairs of same-degree generators in degrees 1 through 12. These are finite exact checks; the infinite parameter ranges are proved analytically in the accompanying manuscript.

certificate.json records the degree-76 example. Source code contains no external service calls and requires no private data.
