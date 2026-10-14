# Positive measure for arithmetic sections

Lean formalization accompanying the [manuscript](../article.pdf).

`ArithmeticSections.positive_measure_in_every_neighborhood` proves that every
neighborhood of the stated explicit volume A₀ contains a Borel subset of the
original Haddad–Ryabogin arithmetic set with positive Lebesgue measure.
`arithmeticSet_positive_volume` gives the positive-measure conclusion, and
`measurableSet_arithmeticSet` proves the set itself is Borel.

The definitions use the original cube-root/arctangent volume parameter, the
actual nearest-integer distances of odd multiples, and their first two order
statistics. The proof uses actual Gauss digits and continued-fraction cylinders,
countable exclusion estimates, and the smooth volume-coordinate inverse.
The seed's infinite inequalities are proved directly from its odd convergents;
its five initial inequalities are checked with proved rational cosine bounds.
The cited geometric rigidity theorem is not re-proved here.

## Build

From the repository root, run:

```sh
lake exe cache get
lake --wfail build ArithmeticSections
lake script run audit ArithmeticSections
lake env leanchecker --fresh ArithmeticSections
```

The shared toolchain and dependency revisions are pinned at the repository root.
