# Sun's circular-permutation conjecture: a counterexample

In the field with 11 elements, there is no circular permutation of all ten nonzero elements for which every adjacent expression `2 + xy` is primitive. The closing pair between the last and first positions is included.

The theorem `SunCounterexample.no_circular_permutation` states this using a bijection from `Fin 10` to the nonzero elements of `ZMod 11` and Mathlib's `IsPrimitiveRoot` predicate. The primitive elements are exactly `{2, 6, 7, 8}`. The two distinct neighbors of each of `2` and `9` must be `3` and `8`; two distinct positions on a ten-cycle cannot share both neighboring positions.

## Build

From the repository root, run:

```sh
lake exe cache get
lake --wfail build R32SunCounterexample
lake script run audit R32SunCounterexample
lake env leanchecker --fresh R32SunCounterexample
```

The shared toolchain and dependency revisions are pinned at the repository root.

The full classification of the other finite-field cases is checked by the accompanying programs in [verification](../verification/README.md).
