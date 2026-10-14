import MainTheorems.Chollet.RankCoefficients.ComponentMass
import MainTheorems.Chollet.BorderSchur

noncomputable section

namespace ResearchMain.Chollet.RankCoefficients

variable {I : Type*} [DecidableEq I]

omit [DecidableEq I] in
theorem normalized_phase_sum (a : ℝ) (z c : I → ℂ) (s : Finset I) :
    (∑ i ∈ s, c i * normalizedBorder a z i) =
      (∑ i ∈ s, c i * z i) / (Real.sqrt a : ℂ) := by
  simp only [normalizedBorder, mul_div_assoc, Finset.sum_div]

omit [DecidableEq I] in
theorem normalized_phase_norm (a : ℝ) (z c : I → ℂ) (s : Finset I) (ha : 0 < a) :
    ‖∑ i ∈ s, c i * normalizedBorder a z i‖ ^ 2 =
      ‖∑ i ∈ s, c i * z i‖ ^ 2 / a := by
  rw [normalized_phase_sum, norm_div, Complex.norm_real,
    Real.norm_eq_abs, abs_of_pos (Real.sqrt_pos.mpr ha), div_pow, Real.sq_sqrt ha.le]

omit [DecidableEq I] in
theorem normalized_componentRatio (a : ℝ) (d : I → ℝ) (z c : I → ℂ)
    (s : Finset I) (ha : 0 < a) :
    ‖∑ i ∈ s, c i * normalizedBorder a z i‖ ^ 2 / (∑ i ∈ s, d i) =
      componentRatio a d z c s := by
  rw [normalized_phase_norm a z c s ha, div_div]
  rfl

end ResearchMain.Chollet.RankCoefficients
