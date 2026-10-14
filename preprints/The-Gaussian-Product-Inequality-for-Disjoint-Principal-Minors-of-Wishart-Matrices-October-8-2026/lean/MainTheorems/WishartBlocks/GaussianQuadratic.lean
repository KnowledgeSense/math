import Mathlib.Probability.Distributions.Gaussian.Real
import Mathlib.Tactic

namespace ResearchMain.WishartBlocks

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

theorem gaussian_quadratic_integral (μ : ℝ) {v : ℝ≥0} (hv : v ≠ 0) {t : ℝ}
    (ht : 0 ≤ t) :
    ∫ x : ℝ, Real.exp (-(t * x ^ 2)) ∂(gaussianReal μ v) =
      (Real.sqrt (2 * Real.pi * ((v : ℝ) / (1 + 2 * (v : ℝ) * t))) /
        Real.sqrt (2 * Real.pi * v)) *
        Real.exp (-(t * μ ^ 2) / (1 + 2 * (v : ℝ) * t)) := by
  have hv' : 0 < (v : ℝ) := by exact_mod_cast (pos_iff_ne_zero.mpr hv)
  let D : ℝ := 1 + 2 * (v : ℝ) * t
  have hD : 0 < D := by dsimp [D]; positivity
  let w : ℝ≥0 := ⟨(v : ℝ) / D, (div_pos hv' hD).le⟩
  have hw : 0 < (w : ℝ) := div_pos hv' hD
  have hwne : w ≠ 0 := by exact_mod_cast hw.ne'
  have hsw : Real.sqrt (2 * Real.pi * w) ≠ 0 := (Real.sqrt_pos.mpr (by positivity)).ne'
  have hsv : Real.sqrt (2 * Real.pi * v) ≠ 0 := (Real.sqrt_pos.mpr (by positivity)).ne'
  have hex : ∀ x : ℝ, -(x - μ) ^ 2 / (2 * (v : ℝ)) + -(t * x ^ 2) =
      -(t * μ ^ 2) / D + -(x - μ / D) ^ 2 / (2 * (w : ℝ)) := by
    intro x
    rw [show (w : ℝ) = (v : ℝ) / D from rfl]
    dsimp [D]
    have hdne : 1 + 2 * (v : ℝ) * t ≠ 0 := hD.ne'
    field_simp
    ring
  let C : ℝ := (Real.sqrt (2 * Real.pi * w) / Real.sqrt (2 * Real.pi * v)) *
    Real.exp (-(t * μ ^ 2) / D)
  have he : ∀ x : ℝ, gaussianPDFReal μ v x * Real.exp (-(t * x ^ 2)) =
      C * gaussianPDFReal (μ / D) w x := by
    intro x
    unfold gaussianPDFReal
    dsimp [C]
    calc
      (Real.sqrt (2 * Real.pi * v))⁻¹ * Real.exp (-(x - μ) ^ 2 / (2 * (v : ℝ))) *
          Real.exp (-(t * x ^ 2)) =
        (Real.sqrt (2 * Real.pi * v))⁻¹ *
          Real.exp (-(x - μ) ^ 2 / (2 * (v : ℝ)) + -(t * x ^ 2)) := by
            rw [Real.exp_add]
            ring
      _ = (Real.sqrt (2 * Real.pi * v))⁻¹ *
          (Real.exp (-(t * μ ^ 2) / D) *
            Real.exp (-(x - μ / D) ^ 2 / (2 * (w : ℝ)))) := by
              rw [hex, Real.exp_add]
      _ = _ := by field_simp
  rw [integral_gaussianReal_eq_integral_smul hv]
  simp only [smul_eq_mul]
  rw [integral_congr_ae (Filter.Eventually.of_forall he), integral_const_mul,
    integral_gaussianPDFReal_eq_one (μ / D) hwne, mul_one]
  rfl

end ResearchMain.WishartBlocks
