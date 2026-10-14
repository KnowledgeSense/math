# Buchweitz profiles

Lean formalization accompanying the [manuscript](../article.pdf).

`BuchweitzProfiles.prescribed_buchweitz_profile` constructs a numerical
semigroup with the stated multiplicity, conductor and genus, realizes every
prescribed bounded integer profile through order `N`, and proves strict
negativity at every later order. Its hypotheses are only `N ≥ 2`, `L ≥ 1`
and the prescribed coefficient bounds.

The semigroup is an actual additive submonoid of the natural numbers, represented
by its membership predicate and closure laws. Finite complement is expressed
by eventual membership. Its finite gapset is explicitly identified with its
complement. The profile counts genuine iterated finite sumsets.

## Proof organization

- `Definitions`, `DepthTwo`, `Sumsets`, `Reflection`: semigroups, reflection,
  interval filling and the gapset profile identity.
- `Construction`, `NatParameters`, `Pairs`, `PrescribedPairs`: parameters and
  the finite list of pairs realizing the prescribed differences.
- `Counting`, `ConstructionSet`, `LargeGenerators`, `ConstructionCount`:
  actual generators, their separation, and exact sumset counts for every order.
- `CountDifferences`, `ProfileInduction`, `ProfileBridge`, `Main`: the
  prescribed values, the infinite negative tail and the main theorem.
- `Data/Example`, `Example`: the genus-172 example, including its complete
  Buchweitz set `{3, 6}`. Weierstrass realizability is outside this formalization.
- `Tests`: theorem-signature, parameter and example checks.

## Build

From the repository root, run:

```sh
lake exe cache get
lake --wfail build BuchweitzProfiles
lake script run audit BuchweitzProfiles
lake env leanchecker --fresh BuchweitzProfiles
```

The shared toolchain and dependency revisions are pinned at the repository root.
