import MainTheorems.WishartBlocks.BartlettLaw
import MainTheorems.WishartBlocks.GammaMoments
import Mathlib.Probability.Distributions.Gaussian.Fernique
import Mathlib.MeasureTheory.SpecificCodomains.Pi

namespace ResearchMain.WishartBlocks

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

theorem gamma_id_memLp {a r : ℝ} (ha : 0 < a) (hr : 0 < r)
    (s : ℝ≥0∞) (hs : s ≠ ∞) : MemLp id s (gammaMeasure a r) := by
  by_cases h0 : s = 0
  · rw [h0, memLp_zero_iff_aestronglyMeasurable]
    exact measurable_id.aestronglyMeasurable
  apply (integrable_norm_rpow_iff measurable_id.aestronglyMeasurable h0 hs).mp
  apply (gamma_moment_integrable (β := s.toReal) ha hr
    (show 0 ≤ s.toReal from ENNReal.toReal_nonneg)).congr
  filter_upwards [gammaMeasure_ae_positive a r] with x hx
  simp only [id_eq, Real.norm_eq_abs, abs_of_pos hx]

theorem bartlett_coordinate_memLp {p : ℕ} {α : ℝ} (hα : (p : ℝ) - 1 < α)
    (ij : Fin p × Fin p) (s : ℝ≥0∞) (hs : s ≠ ∞) :
    MemLp id s (bartlettCoordinate α ij) := by
  unfold bartlettCoordinate
  split_ifs
  · apply gamma_id_memLp _ (by norm_num) s hs
    have hi : (ij.1 : ℕ) + 1 ≤ p := ij.1.isLt
    have hi' : ((ij.1 : ℕ) : ℝ) + 1 ≤ p := by exact_mod_cast hi
    linarith
  · exact IsGaussian.memLp_id _ s hs

theorem bartlett_input_memLp {p : ℕ} {α : ℝ} (hα : (p : ℝ) - 1 < α)
    (s : ℝ≥0∞) (hs : s ≠ ∞) : MemLp id s (bartlettMeasure p α) := by
  let : ∀ ij : Fin p × Fin p, IsProbabilityMeasure (bartlettCoordinate α ij) :=
    bartlett_coordinate_probability hα
  change MemLp id s (Measure.pi (bartlettCoordinate α))
  apply MemLp.of_eval
  intro ij
  simpa only [Function.comp_def, id_eq, Function.eval] using
    (bartlett_coordinate_memLp hα ij s hs).comp_measurePreserving
      (measurePreserving_eval (μ := bartlettCoordinate α) ij)

theorem bartlett_input_polynomial_integrable {p : ℕ} {α : ℝ}
    (hα : (p : ℝ) - 1 < α) (k : ℕ) :
    Integrable (fun x : Fin p × Fin p → ℝ => (1 + ‖x‖) ^ k) (bartlettMeasure p α) := by
  let : IsProbabilityMeasure (bartlettMeasure p α) := bartlett_measure_probability hα
  have hX : MemLp id (k : ℝ≥0∞) (bartlettMeasure p α) :=
    bartlett_input_memLp hα _ (by simp)
  have hI : Integrable (fun x : Fin p × Fin p → ℝ => ‖x‖ ^ k) (bartlettMeasure p α) :=
    hX.integrable_norm_pow' (p := k)
  have hB : Integrable (fun x : Fin p × Fin p → ℝ =>
      (2 : ℝ) ^ (k - 1) * (1 + ‖x‖ ^ k)) (bartlettMeasure p α) :=
    ((integrable_const 1).add hI).const_mul _
  apply hB.mono' (by fun_prop)
  exact ae_of_all _ fun x => by
    rw [Real.norm_of_nonneg (by positivity)]
    simpa only [one_pow] using add_pow_le (zero_le_one (α := ℝ)) (norm_nonneg x) k

end ResearchMain.WishartBlocks
