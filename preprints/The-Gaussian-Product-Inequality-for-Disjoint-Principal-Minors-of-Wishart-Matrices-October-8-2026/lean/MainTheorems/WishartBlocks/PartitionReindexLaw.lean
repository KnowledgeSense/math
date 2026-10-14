import MainTheorems.WishartBlocks.FullShapeResponse

namespace ResearchMain.WishartBlocks

open Matrix MeasureTheory
open scoped BigOperators

namespace BlockPartition

theorem head_tail_dimension {p d : ℕ} (P : BlockPartition p (d + 1)) :
    P.size 0 + ∑ j : Fin d, P.size j.succ = p := by
  rw [← Fin.sum_univ_succ, P.total_size]

theorem headReindex_shape {p d : ℕ} (P : BlockPartition p (d + 1)) {α : ℝ}
    (hα : (p : ℝ) - 1 < α) :
    ((P.size 0 + ∑ j : Fin d, P.size j.succ : ℕ) : ℝ) - 1 < α := by
  rwa [P.head_tail_dimension]

theorem headReindex_covariance_positive {p d : ℕ} (P : BlockPartition p (d + 1))
    {S : Matrix (Fin p) (Fin p) ℝ} (hS : S.PosDef) :
    (S.submatrix P.headReindex.symm P.headReindex.symm).PosDef :=
  hS.submatrix P.headReindex.symm.injective

theorem headReindex_law {p d : ℕ} (P : BlockPartition p (d + 1)) {α : ℝ}
    (hα : (p : ℝ) - 1 < α) {S : Matrix (Fin p) (Fin p) ℝ} (hS : S.PosSemidef) :
    (bartlettLaw α S).map (fun W => W.submatrix P.headReindex.symm P.headReindex.symm) =
      bartlettLaw α (S.submatrix P.headReindex.symm P.headReindex.symm) :=
  bartlettLaw_principal_marginal hα (P.headReindex_shape hα) hS P.headReindex.symm

theorem headReindex_integral {p d : ℕ} (P : BlockPartition p (d + 1)) {α : ℝ}
    (hα : (p : ℝ) - 1 < α) {S : Matrix (Fin p) (Fin p) ℝ} (hS : S.PosSemidef)
    {f : Matrix (Fin (P.size 0 + ∑ j : Fin d, P.size j.succ))
      (Fin (P.size 0 + ∑ j : Fin d, P.size j.succ)) ℝ → ℝ} (hf : Measurable f) :
    (∫ W, f (W.submatrix P.headReindex.symm P.headReindex.symm) ∂(bartlettLaw α S)) =
      ∫ W, f W ∂(bartlettLaw α (S.submatrix P.headReindex.symm P.headReindex.symm)) :=
  bartlett_principal_integral hα (P.headReindex_shape hα) hS P.headReindex.symm hf

theorem determinantProduct_headReindex_integral {p d : ℕ} (P : BlockPartition p (d + 1))
    (ν : Fin (d + 1) → ℝ) {α : ℝ} (hα : (p : ℝ) - 1 < α)
    {S : Matrix (Fin p) (Fin p) ℝ} (hS : S.PosSemidef) :
    (∫ W, P.determinantProduct ν W ∂(bartlettLaw α S)) =
      ∫ W, (principalPair (k := P.size 0) (m := ∑ j : Fin d, P.size j.succ) W).1.det ^ ν 0 *
        P.tail.determinantProduct (fun j => ν j.succ) (principalPair W).2
          ∂(bartlettLaw α (S.submatrix P.headReindex.symm P.headReindex.symm)) := by
  have hf : Measurable (fun W : Matrix (Fin (P.size 0 + ∑ j : Fin d, P.size j.succ))
      (Fin (P.size 0 + ∑ j : Fin d, P.size j.succ)) ℝ =>
      (principalPair (k := P.size 0) (m := ∑ j : Fin d, P.size j.succ) W).1.det ^ ν 0 *
        P.tail.determinantProduct (fun j => ν j.succ) (principalPair W).2) := by
    exact (by fun_prop : Measurable (fun W => (principalPair (k := P.size 0)
      (m := ∑ j : Fin d, P.size j.succ) W).1.det ^ ν 0)).mul
        ((P.tail.measurable_determinantProduct (fun j => ν j.succ)).comp
          (measurable_snd.comp measurable_principalPair))
  rw [← P.headReindex_integral hα hS hf]
  apply integral_congr_ae
  exact ae_of_all _ fun W => by
    dsimp only
    rw [P.reindex_head_block, ← P.determinantProduct_head_tail]

theorem determinantPower_marginal_integral {p d : ℕ} (P : BlockPartition p d)
    (ν : Fin d → ℝ) (j : Fin d) {α : ℝ} (hα : (p : ℝ) - 1 < α)
    {S : Matrix (Fin p) (Fin p) ℝ} (hS : S.PosSemidef) :
    (∫ W, P.determinantPower ν W j ∂(bartlettLaw α S)) =
      ∫ B, B.det ^ ν j ∂(bartlettLaw α (P.block S j)) := by
  have hj : P.size j ≤ p := by
    have hs : P.size j ≤ ∑ i, P.size i :=
      Finset.single_le_sum (fun i _ => Nat.zero_le (P.size i)) (Finset.mem_univ j)
    exact hs.trans_eq P.total_size
  have hjR : (P.size j : ℝ) ≤ p := by exact_mod_cast hj
  have hg : Measurable (fun B : Matrix (Fin (P.size j)) (Fin (P.size j)) ℝ =>
      B.det ^ ν j) := by fun_prop
  exact bartlett_principal_integral hα (by linarith) hS (P.inclusion j) hg

theorem tail_determinantPower_integral {p d : ℕ} (P : BlockPartition p (d + 1))
    (ν : Fin (d + 1) → ℝ) (j : Fin d) {α : ℝ} (hα : (p : ℝ) - 1 < α)
    {S : Matrix (Fin p) (Fin p) ℝ} (hS : S.PosSemidef) :
    (∫ W, P.determinantPower ν W j.succ ∂(bartlettLaw α S)) =
      ∫ B, P.tail.determinantPower (fun i => ν i.succ) B j
        ∂(bartlettLaw α (principalPair (k := P.size 0) (m := ∑ i : Fin d, P.size i.succ)
          (S.submatrix P.headReindex.symm P.headReindex.symm)).2) := by
  have ht : (∑ i : Fin d, P.size i.succ : ℕ) ≤ p := by
    have he := P.head_tail_dimension
    omega
  have htR : ((∑ i : Fin d, P.size i.succ : ℕ) : ℝ) ≤ p := by exact_mod_cast ht
  have hSt : (principalPair (k := P.size 0) (m := ∑ i : Fin d, P.size i.succ)
      (S.submatrix P.headReindex.symm P.headReindex.symm)).2.PosSemidef :=
    (hS.submatrix P.headReindex.symm).submatrix (fun i => finSumFinEquiv (Sum.inr i))
  rw [P.determinantPower_marginal_integral ν j.succ hα hS,
    P.tail.determinantPower_marginal_integral (fun i => ν i.succ) j (by linarith) hSt,
    P.reindex_tail_block]
  rfl

end BlockPartition
end ResearchMain.WishartBlocks
