import MainTheorems.WishartBlocks.NoncentralResponseGrowth
import MainTheorems.WishartBlocks.WishartRegressionIntegral

namespace ResearchMain.WishartBlocks

open MeasureTheory Matrix
open scoped MatrixOrder Matrix.Norms.Elementwise

noncomputable def covarianceResponse {k m : ℕ} (α : ℝ)
    (S : Matrix (Fin m) (Fin m) ℝ) (K : Matrix (Fin k) (Fin m) ℝ)
    (g : Matrix (Fin m) (Fin m) ℝ → ℝ) (W : Matrix (Fin k) (Fin k) ℝ) : ℝ :=
  noncentralMeanExpectation α S g (covarianceMeanRows W K)

theorem covarianceResponse_measurable {k m : ℕ} {α : ℝ}
    (hα : (m : ℝ) - 1 < α - (k : ℝ)) (S : Matrix (Fin m) (Fin m) ℝ)
    (K : Matrix (Fin k) (Fin m) ℝ) {g : Matrix (Fin m) (Fin m) ℝ → ℝ}
    (hg : Continuous g) {C β : ℝ} (hC : 0 ≤ C) (hβ : 0 ≤ β)
    (hgB : ∀ B, ‖g B‖ ≤ C * (1 + ‖B‖) ^ β) :
    Measurable (covarianceResponse α S K g) :=
  (noncentralMeanExpectation_continuous hα S hg hC hβ hgB).measurable.comp
    (covarianceMeanRows_measurable K)

theorem regressionMean_law_canonical {k m : ℕ} {α : ℝ}
    (hα : (m : ℝ) - 1 < α - (k : ℝ)) {S : Matrix (Fin m) (Fin m) ℝ} (hS : S.PosDef)
    (A : Matrix (Fin k) (Fin k) ℝ) (K : Matrix (Fin k) (Fin m) ℝ)
    (x : Fin k × Fin k → ℝ) :
    noncentralWishartLaw α S (regressionMean A K x) =
      noncentralWishartLaw α S (covarianceMeanRows (bartlettValue A x) K) := by
  apply noncentralWishart_meanGram_eq hα hα hS
  rw [regressionMean_gram, covarianceMeanRows_gram (bartlettValue_positiveSemidefinite A x)]

theorem wishart_regression_covarianceResponse_integral {k m : ℕ} {α : ℝ}
    (hα : ((k + m : ℕ) : ℝ) - 1 < α)
    {S₀ : Matrix (Fin (k + m)) (Fin (k + m)) ℝ} (hS₀ : S₀.PosDef)
    (f : Matrix (Fin k) (Fin k) ℝ → ℝ) (g : Matrix (Fin m) (Fin m) ℝ → ℝ)
    (hf : Measurable f) (hg : Measurable g)
    (hG : Measurable (covarianceResponse α (schurCovariance S₀) (regressionCoefficient S₀) g))
    (hI : Integrable (fun W => f (principalPair (k := k) (m := m) W).1 *
      g (principalPair (k := k) (m := m) W).2) (bartlettLaw α S₀)) :
    (∫ W, f (principalPair (k := k) (m := m) W).1 *
      g (principalPair (k := k) (m := m) W).2 ∂(bartlettLaw α S₀)) =
      ∫ A, f A * covarianceResponse α (schurCovariance S₀) (regressionCoefficient S₀) g A
        ∂(bartlettLaw α (principalPair (k := k) (m := m) S₀).1) := by
  rw [wishart_block_regression_product_integral hα hS₀ f g hf hg hI]
  have hi : (m : ℝ) - 1 < α - (k : ℝ) := by push_cast at hα; linarith
  have he : (fun x => f (bartlettValue (principalPair (k := k) (m := m) S₀).1 x) *
      ∫ B, g B ∂(noncentralWishartLaw α (schurCovariance S₀)
        (regressionMean (principalPair S₀).1 (regressionCoefficient S₀) x))) =
      fun x => f (bartlettValue (principalPair S₀).1 x) *
        covarianceResponse α (schurCovariance S₀) (regressionCoefficient S₀) g
          (bartlettValue (principalPair S₀).1 x) := by
    funext x
    rw [regressionMean_law_canonical hi (schurCovariance_positiveDefinite hS₀)]
    rfl
  rw [he, bartlettLaw]
  simpa only [Pi.mul_apply] using
    (integral_map (measurable_bartlettValue (principalPair S₀).1).aemeasurable
      (hf.mul hG).aestronglyMeasurable).symm

theorem wishart_regression_response_integral {k m : ℕ} {α : ℝ}
    (hα : ((k + m : ℕ) : ℝ) - 1 < α)
    {S₀ : Matrix (Fin (k + m)) (Fin (k + m)) ℝ} (hS₀ : S₀.PosDef)
    (g : Matrix (Fin m) (Fin m) ℝ → ℝ) (hg : Measurable g)
    (hG : Measurable (covarianceResponse α (schurCovariance S₀) (regressionCoefficient S₀) g))
    (hI : Integrable (fun W => g (principalPair (k := k) (m := m) W).2) (bartlettLaw α S₀)) :
    (∫ W, g (principalPair (k := k) (m := m) W).2 ∂(bartlettLaw α S₀)) =
      ∫ A, covarianceResponse α (schurCovariance S₀) (regressionCoefficient S₀) g A
        ∂(bartlettLaw α (principalPair (k := k) (m := m) S₀).1) := by
  simpa only [one_mul] using wishart_regression_covarianceResponse_integral hα hS₀
    (fun _ => (1 : ℝ)) g measurable_const hg hG (by simpa only [one_mul] using hI)

end ResearchMain.WishartBlocks
