# Ordinary and restricted sumset sizes

Lean formalization accompanying the [manuscript](../article.pdf).

For every `h ≥ 2` and `k ≥ (2h)^80`:

- `SumsetRanges.restricted_main` proves that the cardinalities of restricted h-fold sums of k-element integer sets are exactly `[h(k-h)+1, choose(k,h)]`.
- `SumsetRanges.ordinary_main` proves that the ordinary cardinalities are exactly `[hk-h+1, choose(h+k-1,h)]` excluding the original triangular intervals `Δ(h,k)`.

Both theorems include an actual k-element integer witness in `[0,k^E_h]` or `[0,k^F_h]` for every attainable cardinality. `Definitions.lean` gives the exact release formulas for `Δ`, `E_h`, and `F_h`. The ordinary exclusion theorem is unconditional; the full normalized Lev growth theorem and the needed Kneser theorem are proved in Lean. No project axiom or placeholder theorem is used.

## Build

From the repository root, run:

```sh
lake exe cache get
lake --wfail build SumsetRanges
lake script run audit SumsetRanges
lake env leanchecker --fresh SumsetRanges
```

The shared toolchain and dependency revisions are pinned at the repository root.

## Third-party attribution

`SumsetRanges/Kneser/MulStab.lean` and `SumsetRanges/Kneser/Kneser.lean` adapt the Apache-2.0-licensed CamCombi proofs by Mantas Bakšys and Yaël Dillies, from [commit 58efa34adc943ba7f55f9ae9a423215dafccf52a](https://github.com/YaelDillies/cam-combi/tree/58efa34adc943ba7f55f9ae9a423215dafccf52a/LeanCamCombi/Kneser), dated November 22, 2024. Original Git blobs are `d76fe0c3f32f4737eb9f6449ac694b3bed9eddf9` and `7c51799f7838d524492e1e9f487be3bcda02800c`, respectively. The adaptations update imports, syntax, instance handling, and theorem names for the pinned toolchain. Original notices remain in the files; the full license is in `SumsetRanges/Kneser/LICENSE`.
