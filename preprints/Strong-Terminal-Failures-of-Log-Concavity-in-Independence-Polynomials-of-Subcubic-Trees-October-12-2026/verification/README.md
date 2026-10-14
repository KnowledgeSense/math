# Strong terminal failures of log-concavity in independence polynomials of subcubic trees

Author: Knowledge Sense

Run `python -X utf8 verify.py` with Python 3.11 or newer. Only the standard library is needed.
The script explicitly constructs adjacency lists and counts complementary vertex covers using integer arithmetic.
It checks 18 rooted blocks, small instances by enumeration, the finite coefficient model for q=2,...,8, and nine full trees.
Six full trees use the theorem parameters. Three use smaller recursion heights and lie outside the parameter range used to prove the theorem; they illustrate the role of the threshold.
Each assertion verifies a specified identity or inequality. Successful completion writes verification-results.json with all_assertions_satisfied=true.
These finite checks supplement the symbolic proof in the paper.
For (r,H)=(1,1), the script also checks the exact power bounds on the ratio and its relative difference of less than 10^-5 from the model ratio a^2/4.

Construction.positive_gap(p,t) builds X_t[p], and Construction.interface(p,m,t) builds G_t[p,m]. Construction.zero_gap(p,t) builds X_t[p] with one additional vertex adjacent to its root, taking that additional vertex as the new root. The script's parameter sum P is S in the paper, and H.bit_length() is h = ceil(log_2(H+1)) for positive integer H. The dynamic program stores vertex-cover counts for the two states in which the current root is included or excluded. Vertex covers are counted because complementation is a bijection between independent sets of size alpha-j and vertex covers of size |V|-alpha+j.
The model constants K0 and K in the script correspond to kappa_0 and kappa in the paper.
