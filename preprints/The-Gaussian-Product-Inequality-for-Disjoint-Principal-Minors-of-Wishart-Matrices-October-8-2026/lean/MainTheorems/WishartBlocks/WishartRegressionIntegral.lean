import MainTheorems.WishartBlocks.WishartSchurRegression

namespace ResearchMain.WishartBlocks

open MeasureTheory ProbabilityTheory Matrix
open scoped MatrixOrder

theorem wishart_block_regression_integral {k m : ℕ} {α : ℝ}
    (hα : ((k + m : ℕ) : ℝ) - 1 < α)
    {S₀ : Matrix (Fin (k + m)) (Fin (k + m)) ℝ} (hS₀ : S₀.PosDef)
    (F : Matrix (Fin k) (Fin k) ℝ × Matrix (Fin m) (Fin m) ℝ → ℝ)
    (hF : Measurable F)
    (hI : Integrable (fun W => F (principalPair (k := k) (m := m) W))
      (bartlettLaw α S₀)) :
    ∫ W, F (principalPair (k := k) (m := m) W) ∂(bartlettLaw α S₀) =
      ∫ x, ∫ B, F (bartlettValue (principalPair S₀).1 x, B)
        ∂(noncentralWishartLaw α (schurCovariance S₀)
          (regressionMean (principalPair S₀).1 (regressionCoefficient S₀) x))
        ∂(bartlettMeasure k α) := by
  let A := (principalPair (k := k) (m := m) S₀).1
  let S := schurCovariance S₀
  let K := regressionCoefficient S₀
  have hr : (m : ℝ) - 1 < α - (k : ℝ) := by push_cast at hα; linarith
  have hαk : (k : ℝ) - 1 < α := by
    have hm : (0 : ℝ) ≤ m := Nat.cast_nonneg m
    push_cast at hα
    linarith
  let : IsProbabilityMeasure (bartlettMeasure k α) := bartlett_measure_probability hαk
  let : IsProbabilityMeasure (bartlettLaw (α - (k : ℝ)) S) :=
    bartlett_law_probability hr S
  have hLaw := wishart_block_regression_general hα hS₀
  have hMapped : Integrable F ((bartlettLaw α S₀).map
      (principalPair (k := k) (m := m))) :=
    (integrable_map_measure hF.aestronglyMeasurable measurable_principalPair.aemeasurable).mpr hI
  rw [hLaw] at hMapped
  have hInput : Integrable (fun xvz => F (regressionPairValue A S K xvz))
      (regressionInputLaw (k := k) α S) :=
    (integrable_map_measure hF.aestronglyMeasurable
      (regressionPair_measurable A S K).aemeasurable).mp hMapped
  rw [← integral_map measurable_principalPair.aemeasurable hF.aestronglyMeasurable,
    hLaw, integral_map (regressionPair_measurable A S K).aemeasurable
      hF.aestronglyMeasurable, regressionInputLaw, integral_prod _ hInput]
  apply integral_congr_ae
  exact ae_of_all _ fun x => by
    change (∫ vz, F (regressionPairValue A S K (x, vz))
      ∂((bartlettLaw (α - (k : ℝ)) S).prod
        (Measure.pi fun _ : Fin k => stdGaussian (EuclideanSpace ℝ (Fin m))))) =
      ∫ B, F (bartlettValue A x, B)
        ∂(noncentralWishartLaw α S (regressionMean A K x))
    have hFx : Measurable (fun B : Matrix (Fin m) (Fin m) ℝ =>
        F (bartlettValue A x, B)) :=
      hF.comp ((measurable_const : Measurable
        (fun _ : Matrix (Fin m) (Fin m) ℝ => bartlettValue A x)).prodMk measurable_id)
    rw [noncentralWishartLaw, integral_map
      (measurable_noncentralWishartValue S (regressionMean A K x)).aemeasurable
      hFx.aestronglyMeasurable]
    rfl

theorem wishart_block_regression_product_integral {k m : ℕ} {α : ℝ}
    (hα : ((k + m : ℕ) : ℝ) - 1 < α)
    {S₀ : Matrix (Fin (k + m)) (Fin (k + m)) ℝ} (hS₀ : S₀.PosDef)
    (f : Matrix (Fin k) (Fin k) ℝ → ℝ) (g : Matrix (Fin m) (Fin m) ℝ → ℝ)
    (hf : Measurable f) (hg : Measurable g)
    (hI : Integrable (fun W => f (principalPair (k := k) (m := m) W).1 *
      g (principalPair (k := k) (m := m) W).2) (bartlettLaw α S₀)) :
    ∫ W, f (principalPair (k := k) (m := m) W).1 *
        g (principalPair (k := k) (m := m) W).2 ∂(bartlettLaw α S₀) =
      ∫ x, f (bartlettValue (principalPair S₀).1 x) *
        (∫ B, g B ∂(noncentralWishartLaw α (schurCovariance S₀)
          (regressionMean (principalPair S₀).1 (regressionCoefficient S₀) x)))
        ∂(bartlettMeasure k α) := by
  rw [wishart_block_regression_integral hα hS₀ (fun AB => f AB.1 * g AB.2)
    ((hf.comp measurable_fst).mul (hg.comp measurable_snd)) hI]
  simp_rw [integral_const_mul]

end ResearchMain.WishartBlocks
