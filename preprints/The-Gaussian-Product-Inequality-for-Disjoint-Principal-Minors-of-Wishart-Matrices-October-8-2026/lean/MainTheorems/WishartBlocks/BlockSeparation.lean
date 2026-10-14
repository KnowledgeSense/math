import MainTheorems.WishartBlocks.PartitionReindexLaw
import MainTheorems.WishartBlocks.SpectralLaw.DeterminantAssociation

namespace ResearchMain.WishartBlocks

open Matrix MeasureTheory
open scoped BigOperators MatrixOrder Matrix.Norms.Elementwise

namespace BlockPartition

theorem response_full_shape_monotone {k m d : ℕ} (P : BlockPartition m (d + 1))
    (ν : Fin (d + 1) → ℝ) (hν : ∀ j, 0 ≤ ν j) (hk : 0 < k)
    {α : ℝ} (hα : ((k + m : ℕ) : ℝ) - 1 < α)
    {S : Matrix (Fin m) (Fin m) ℝ} (hS : S.PosDef)
    (K : Matrix (Fin k) (Fin m) ℝ) :
    MonotoneOn (P.noncentralProductResponse α S K ν) {W | W.PosDef} := by
  cases k with
  | zero => omega
  | succ n =>
    cases d with
    | zero =>
      rw [P.oneBlock_response]
      exact noncentralDeterminantResponse_full_shape_monotone hα (hν 0) hS K
    | succ e =>
      exact P.noncentralProductResponse_full_shape_monotone ν hν hα hS K

theorem head_tail_separation {k m d : ℕ} (P : BlockPartition m (d + 1))
    (ν : Fin (d + 1) → ℝ) (hν : ∀ j, 0 ≤ ν j) (hk : 0 < k)
    {α a : ℝ} (hα : ((k + m : ℕ) : ℝ) - 1 < α) (ha : 0 ≤ a)
    {S₀ : Matrix (Fin (k + m)) (Fin (k + m)) ℝ} (hS₀ : S₀.PosDef) :
    (∫ A, A.det ^ a ∂(bartlettLaw α (principalPair (k := k) (m := m) S₀).1)) *
      (∫ B, P.determinantProduct ν B ∂(bartlettLaw α (principalPair (k := k) (m := m) S₀).2)) ≤
      ∫ W, (principalPair (k := k) (m := m) W).1.det ^ a *
        P.determinantProduct ν (principalPair (k := k) (m := m) W).2 ∂(bartlettLaw α S₀) := by
  have hr : (m : ℝ) - 1 < α - (k : ℝ) := by push_cast at hα; linarith
  have hαA : (k : ℝ) - 1 < α := by
    push_cast at hα
    linarith [Nat.cast_nonneg (α := ℝ) m]
  have hA : (principalPair (k := k) (m := m) S₀).1.PosDef :=
    hS₀.submatrix (finSumFinEquiv.injective.comp Sum.inl_injective)
  have hS := schurCovariance_positiveDefinite hS₀
  have h := wishart_determinant_association hαA hA ha
    (P.noncentralProductResponse_measurable ν hν hr _ _)
    (P.noncentralProductResponse_continuousOn ν hν hr _ _)
    (P.response_full_shape_monotone ν hν hk hα hS (regressionCoefficient S₀))
    (fun W _ => P.noncentralProductResponse_nonneg ν α _ _ W)
    (P.noncentralProductResponse_growth ν hν hr _ _)
  rw [P.wishart_tailProduct_response_integral ν hν hα hS₀] at h
  rw [← P.wishart_determinant_product_regression_integral ν hν hα ha hS₀] at h
  exact h

end BlockPartition
end ResearchMain.WishartBlocks
