import MainTheorems.WishartBlocks.BlockPartitionSplit

namespace ResearchMain.WishartBlocks

open Matrix MeasureTheory
open scoped BigOperators Matrix.Norms.Elementwise

namespace BlockPartition

noncomputable def productMatrixConstant {p d : ℕ} (P : BlockPartition p d) (ν : Fin d → ℝ) : ℝ :=
  ∏ j, (Fintype.card (Equiv.Perm (Fin (P.size j))) : ℝ) ^ ν j

theorem productMatrixConstant_nonneg {p d : ℕ} (P : BlockPartition p d) (ν : Fin d → ℝ) :
    0 ≤ P.productMatrixConstant ν :=
  Finset.prod_nonneg fun _j _ => Real.rpow_nonneg (Nat.cast_nonneg _) _

theorem determinantProduct_matrix_growth {p d : ℕ} (P : BlockPartition p d)
    (ν : Fin d → ℝ) (hν : ∀ j, 0 ≤ ν j) (W : Matrix (Fin p) (Fin p) ℝ) :
    ‖P.determinantProduct ν W‖ ≤ P.productMatrixConstant ν * (1 + ‖W‖) ^ P.productGrowthExponent ν := by
  simpa only [shiftedDeterminantProduct, determinantProduct, determinantPower, add_zero,
    norm_zero, add_zero, one_pow, mul_one, productMatrixConstant, productGrowthExponent] using
      P.shiftedDeterminantProduct_growth (fun _ => 0) ν hν W

theorem principalPair_product_integrable {k m d : ℕ} (P : BlockPartition m d)
    (ν : Fin d → ℝ) (hν : ∀ j, 0 ≤ ν j) {α a : ℝ}
    (hα : ((k + m : ℕ) : ℝ) - 1 < α) (ha : 0 ≤ a)
    (S₀ : Matrix (Fin (k + m)) (Fin (k + m)) ℝ) :
    Integrable (fun W => (principalPair (k := k) (m := m) W).1.det ^ a *
      P.determinantProduct ν (principalPair (k := k) (m := m) W).2) (bartlettLaw α S₀) := by
  exact principal_power_product_integrable hα ha (P.productMatrixConstant_nonneg ν)
    (Finset.sum_nonneg fun j _ => mul_nonneg (Nat.cast_nonneg _) (hν j)) S₀
    (fun i => finSumFinEquiv (Sum.inl i)) (fun i => finSumFinEquiv (Sum.inr i))
    (P.measurable_determinantProduct ν) (P.determinantProduct_matrix_growth ν hν)

theorem principalPair_tailProduct_integrable {k m d : ℕ} (P : BlockPartition m d)
    (ν : Fin d → ℝ) (hν : ∀ j, 0 ≤ ν j) {α : ℝ}
    (hα : ((k + m : ℕ) : ℝ) - 1 < α) (S₀ : Matrix (Fin (k + m)) (Fin (k + m)) ℝ) :
    Integrable (fun W => P.determinantProduct ν (principalPair (k := k) (m := m) W).2)
      (bartlettLaw α S₀) := by
  exact principal_growth_integrable hα (P.productMatrixConstant_nonneg ν)
    (Finset.sum_nonneg fun j _ => mul_nonneg (Nat.cast_nonneg _) (hν j)) S₀
    (fun i => finSumFinEquiv (Sum.inr i)) (P.measurable_determinantProduct ν)
    (P.determinantProduct_matrix_growth ν hν)

theorem wishart_determinant_product_regression_integral {k m d : ℕ} (P : BlockPartition m d)
    (ν : Fin d → ℝ) (hν : ∀ j, 0 ≤ ν j) {α a : ℝ}
    (hα : ((k + m : ℕ) : ℝ) - 1 < α) (ha : 0 ≤ a)
    {S₀ : Matrix (Fin (k + m)) (Fin (k + m)) ℝ} (hS₀ : S₀.PosDef) :
    (∫ W, (principalPair (k := k) (m := m) W).1.det ^ a *
      P.determinantProduct ν (principalPair (k := k) (m := m) W).2 ∂(bartlettLaw α S₀)) =
      ∫ A, A.det ^ a * P.noncentralProductResponse α (schurCovariance S₀) (regressionCoefficient S₀) ν A
        ∂(bartlettLaw α (principalPair (k := k) (m := m) S₀).1) := by
  have hi : (m : ℝ) - 1 < α - (k : ℝ) := by push_cast at hα; linarith
  exact wishart_regression_covarianceResponse_integral hα hS₀ (fun A => A.det ^ a)
    (P.determinantProduct ν) (by fun_prop) (P.measurable_determinantProduct ν)
    (P.noncentralProductResponse_measurable ν hν hi _ _) (P.principalPair_product_integrable ν hν hα ha S₀)

theorem wishart_tailProduct_response_integral {k m d : ℕ} (P : BlockPartition m d)
    (ν : Fin d → ℝ) (hν : ∀ j, 0 ≤ ν j) {α : ℝ}
    (hα : ((k + m : ℕ) : ℝ) - 1 < α)
    {S₀ : Matrix (Fin (k + m)) (Fin (k + m)) ℝ} (hS₀ : S₀.PosDef) :
    (∫ A, P.noncentralProductResponse α (schurCovariance S₀) (regressionCoefficient S₀) ν A
      ∂(bartlettLaw α (principalPair (k := k) (m := m) S₀).1)) =
      ∫ B, P.determinantProduct ν B ∂(bartlettLaw α (principalPair (k := k) (m := m) S₀).2) := by
  have hi : (m : ℝ) - 1 < α - (k : ℝ) := by push_cast at hα; linarith
  change (∫ A, covarianceResponse α (schurCovariance S₀) (regressionCoefficient S₀)
      (P.determinantProduct ν) A ∂(bartlettLaw α (principalPair (k := k) (m := m) S₀).1)) =
    ∫ B, P.determinantProduct ν B ∂(bartlettLaw α (principalPair (k := k) (m := m) S₀).2)
  rw [← wishart_regression_response_integral hα hS₀ (P.determinantProduct ν)
    (P.measurable_determinantProduct ν) (P.noncentralProductResponse_measurable ν hν hi _ _)
    (P.principalPair_tailProduct_integrable ν hν hα S₀)]
  have hm : (m : ℝ) - 1 < α := by
    push_cast at hα
    linarith [Nat.cast_nonneg (α := ℝ) k]
  exact bartlett_principal_integral hα hm hS₀.posSemidef (fun i => finSumFinEquiv (Sum.inr i))
    (P.measurable_determinantProduct ν)

end BlockPartition
end ResearchMain.WishartBlocks
