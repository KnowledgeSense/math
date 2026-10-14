# Exact finite diagnostics

Run python verify.py with Python 3.10 or newer. Only the standard library is used.

The program directly enumerates dominating subsets of paths and cycles and compares the counts with the bounded-gap coefficient formulas. It separately enumerates general bounded-gap subsets and counts restricted positive compositions by dynamic programming. All coefficient inequalities are checked with integers or rational numbers.

Ranges: 0<=n<=16, 1<=ell<=n+2 for graphs; 1<=v<=10, 1<=q<=8, q<=m<=12 for bounded-gap subsets; 1<=n<=50, 2<=t<=9 for compositions.

The program writes results.json. The saved result records the expected exact case and assertion counts. Execution time may differ. These finite checks supplement the analytic proof and do not establish an unbounded theorem on their own.
