# Uniform weak Clergyman bound

For every integer `k ≥ 2`, every positive integral coefficient vector
`a : Fin k → ℕ`, and every strictly increasing complementary pair of positive
integer sequences satisfying the weighted anti-recurrence, this project proves

```text
|A_n − (k τ + 1)n| ≤ 2(k τ + 1),    n ≥ 1,    τ = ∑ a_j.
```

The main theorem is `WeakClergyman.uniform_discrepancy`. Its `AntiRecurrence`
structure contains the actual sequences, their positivity, strict increase,
complementarity, and original weighted block equation. Lean indexes these
sequences from zero; the theorem uses `S.A (n-1)` for the original `A_n`.

The proof establishes finite rank counting, separation, the initial block,
the one-hole block bound, strictly earlier bracketing indices, and strong
induction. Every coefficient vector and every positive index is covered.
Existence and uniqueness of a complementary pair are not asserted here.

This formalizes the uniform bound for the original model of Fokkink and Joshi,
*Anti-recurrence sequences*, INTEGERS 26 (2026), A24, whose Conjecture 2 discussion
identifies bounded discrepancy as the weak Clergyman assertion:
https://math.colgate.edu/~integers/aa24/aa24.pdf

## Build

Lean 4.34.1 and Mathlib v4.34.1 are pinned at the repository root.
On Windows, use a short checkout path, such as `C:/math`.

From the repository root:

```sh
lake exe cache get
lake --wfail build WeakClergyman
lake script run certificates WeakClergyman
lake script run audit WeakClergyman
lake env leanchecker --fresh WeakClergyman
```

`tests/Certificates.lean` checks the stated results and boundary cases.
`tests/Axioms.lean` lists the logical axioms used by the project.
