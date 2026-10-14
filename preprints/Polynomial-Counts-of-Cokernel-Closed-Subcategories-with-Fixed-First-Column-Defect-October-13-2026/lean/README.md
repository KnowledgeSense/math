# Cokernel-closed subcategories of a chain: fixed-defect polynomiality

This project formalizes the full categorical enumeration theorem and its finite
combinatorial model. The ambient category consists of finite-dimensional complex
representations of the reverse oriented chain on vertices `0, …, n`.
`CokernelSubcategory n` describes actual replete full additive, idempotent-split
subcategories closed under the ambient categorical cokernel. `categoryCount n k`
counts these subcategories with exactly `k` interval classes `[0,b]`.

`CokernelPolynomiality.categoricalFixedDefectPolynomiality` proves that for every
natural `i` there is a rational polynomial evaluating to
`categoryCount n (n+1-i)` for every `i ≤ n+1`, with exact degree `2*i` and leading
coefficient `1/i!`. The finite-count theorem `fixedDefectPolynomiality` and the
explicit shifted-binomial polynomial `defectPolynomial` are retained.

## Proof

The representation-theoretic reduction is formalized directly:
finite-dimensional chain representations are constructively decomposed into
intervals; actual interval morphisms and cokernels are computed; arbitrary maps
are reduced by invertible scalar normalization and square-zero shears; and the
resulting antichain cokernel is proved by exactness and a suffix-sum right inverse.
The actual categorical universal properties are established, rather than assumed.

`categoricalClosedPointEquiv` identifies these subcategories, preserving the
first-column statistic, with the closed subsets of
`{(a,b) : 0 ≤ a ≤ b ≤ n}`. The finite proof then establishes the point-set/graph
correspondence, graph/cutoff-code bijection, finite-template count, and top-template
bijection with injections from `Fin i` to `Fin (2*i)`. Every admissible boundary
rank is included. The counts are independently defined from their objects.

## Build

Lean 4.34.1 and Mathlib v4.34.1 are pinned at the repository root.
On Windows, use a short checkout path, such as `C:/math`.

From the repository root:

```sh
lake exe cache get
lake --wfail build CokernelPolynomiality
lake script run certificates CokernelPolynomiality
lake script run audit CokernelPolynomiality
lake env leanchecker --fresh CokernelPolynomiality
```

`tests/Certificates.lean` checks the stated results and boundary cases.
`tests/Axioms.lean` lists the logical axioms used by the project.
