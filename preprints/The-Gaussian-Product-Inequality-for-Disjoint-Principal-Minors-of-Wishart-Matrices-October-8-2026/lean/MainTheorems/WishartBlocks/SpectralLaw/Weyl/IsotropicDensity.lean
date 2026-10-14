import MainTheorems.WishartBlocks.SpectralLaw.Weyl.IsotropicIntegral

namespace ResearchMain.WishartBlocks

open MeasureTheory
open scoped ENNReal

theorem isotropicEigenvalueLaw_density {n : ℕ} {α : ℝ}
    (hα : (n : ℝ) - 1 < α) :
    ∃ c : ℝ, 0 < c ∧ isotropicEigenvalueLaw n α =
      volume.withDensity (fun lam => ENNReal.ofReal (c * eigenvalueWeight α lam)) := by
  let : IsProbabilityMeasure (bartlettLaw α (1 : Matrix (Fin n) (Fin n) ℝ)) :=
    bartlett_law_probability hα 1
  let K := Weyl.isotropicSpectralNNConstant n α
  let Z := ∫⁻ lam : Fin n → ℝ, ENNReal.ofReal (eigenvalueWeight α lam)
  have hnorm : K * Z = 1 := by
    simpa only [K, Z, mul_one, lintegral_one, measure_univ] using
      (Weyl.isotropicEigenvalueLaw_lintegral_weight hα
        (measurable_const : Measurable (fun _ : Fin n → ℝ => (1 : ℝ≥0∞)))).symm
  have hKzero : K ≠ 0 := by
    intro h
    rw [h, zero_mul] at hnorm
    exact zero_ne_one hnorm
  have hZzero : Z ≠ 0 := by
    intro h
    rw [h, mul_zero] at hnorm
    exact zero_ne_one hnorm
  have hfinite : K < ∞ ∧ Z < ∞ := by
    have hlt : K * Z < ∞ := by rw [hnorm]; exact ENNReal.one_lt_top
    rcases ENNReal.mul_lt_top_iff.mp hlt with h | h | h
    · exact h
    · exact (hKzero h).elim
    · exact (hZzero h).elim
  let c := K.toReal
  have hc : 0 < c := ENNReal.toReal_pos hKzero hfinite.1.ne
  have hcoe : ENNReal.ofReal c = K := ENNReal.ofReal_toReal hfinite.1.ne
  refine ⟨c, hc, ?_⟩
  apply Measure.ext_of_lintegral
  intro f hf
  rw [Weyl.isotropicEigenvalueLaw_lintegral_weight hα hf]
  calc
    _ = ∫⁻ lam, ENNReal.ofReal (c * eigenvalueWeight α lam) * f lam := by
      simp_rw [ENNReal.ofReal_mul hc.le, hcoe, mul_assoc]
      exact (lintegral_const_mul K
        ((measurable_eigenvalueWeight α).ennreal_ofReal.mul hf)).symm
    _ = _ :=
      (lintegral_withDensity_eq_lintegral_mul volume
        (f := fun lam => ENNReal.ofReal (c * eigenvalueWeight α lam)) (g := f)
        ((measurable_const.mul (measurable_eigenvalueWeight α)).ennreal_ofReal) hf).symm

end ResearchMain.WishartBlocks
