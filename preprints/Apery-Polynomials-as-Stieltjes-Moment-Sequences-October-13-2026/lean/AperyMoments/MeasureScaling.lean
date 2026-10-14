import AperyMoments.Reciprocal
import Mathlib.MeasureTheory.Measure.Typeclasses.Probability

noncomputable section
open MeasureTheory Set
namespace AperyMoments

/-- Pushforward transfers a genuine all-moment representation of the reciprocal
polynomials to the original Apéry polynomials. -/
theorem original_moments_of_reciprocal {α R : ℝ} (hα : 0 < α) (hR : 0 ≤ R)
    (μ : Measure ℝ) (hprob : IsProbabilityMeasure μ) (hsupport : μ (Icc 0 R)ᶜ = 0)
    (hmom : ∀ n : ℕ, Integrable (fun t : ℝ => t ^ n) μ ∧
      (∫ t : ℝ, t ^ n ∂μ) = reciprocalPolynomial n α) :
    HasPositiveMomentRepresentation α⁻¹ := by
  let ν := Measure.map (fun t : ℝ => t / α) μ
  have hg : Measurable (fun t : ℝ => t / α) := by fun_prop
  have hν : IsProbabilityMeasure ν := by
    constructor
    change (Measure.map (fun t : ℝ => t / α) μ) univ = 1
    rw [Measure.map_apply hg MeasurableSet.univ, preimage_univ]
    exact hprob.measure_univ
  refine ⟨ν, hν, R / α, div_nonneg hR hα.le, ?_, ?_⟩
  · change (Measure.map (fun t : ℝ => t / α) μ) (Icc 0 (R / α))ᶜ = 0
    rw [Measure.map_apply hg measurableSet_Icc.compl]
    apply measure_mono_null _ hsupport
    intro t ht ht'
    apply ht
    exact ⟨div_nonneg ht'.1 hα.le, (div_le_div_iff_of_pos_right hα).mpr ht'.2⟩
  · intro n
    have hp : AEStronglyMeasurable (fun t : ℝ => t ^ n) ν := by fun_prop
    have hi : Integrable (fun t : ℝ => (t / α) ^ n) μ := by
      simpa only [div_pow] using (hmom n).1.div_const (α ^ n)
    refine ⟨(integrable_map_measure hp hg.aemeasurable).mpr hi, ?_⟩
    change (∫ t : ℝ, t ^ n ∂Measure.map (fun t : ℝ => t / α) μ) = _
    rw [integral_map hg.aemeasurable hp]
    simp_rw [div_pow]
    rw [integral_div, (hmom n).2, reciprocalPolynomial_eq n hα.ne']
    exact mul_div_cancel_left₀ _ (pow_ne_zero n hα.ne')

end AperyMoments
