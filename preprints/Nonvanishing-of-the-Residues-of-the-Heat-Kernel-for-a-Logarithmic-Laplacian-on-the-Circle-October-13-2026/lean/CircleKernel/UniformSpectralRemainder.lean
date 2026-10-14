import CircleKernel.UniformPerturbation

noncomputable section
open Filter Asymptotics Finset
open scoped Topology
namespace CircleKernel

theorem uniform_normalized_spectral_remainder (M : ℕ) (hM : 0 < M)
    (R : ℝ) (hR : 0 ≤ R) :
    ∃ B ≥ 0, ∃ N : ℕ, ∀ n : ℕ, N ≤ n → ∀ t : ℂ, ‖t‖ ≤ R →
      ‖Complex.exp (-t*(spectralCorrection n : ℂ)) -
        ∑ j ∈ range M, (complexResiduePolynomial j).eval t/(n : ℂ)^j‖ ≤ B/(n : ℝ)^M := by
  obtain ⟨C,hC,hbound⟩ := (eigenvalueError_bigO M hM).exists_pos
  obtain ⟨N,hN⟩ := eventually_atTop.mp hbound.bound
  obtain ⟨B,hB,h⟩ := uniform_perturbed_exponential M R C hR (le_of_lt hC)
  refine ⟨B,hB,max N 1,?_⟩
  intro n hn t ht
  have hnN : N ≤ n := le_trans (le_max_left _ _) hn
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast le_trans (le_max_right _ _) hn
  have hz : ‖(1 : ℂ)/(n : ℂ)‖ ≤ 1 := by
    simp only [norm_div, norm_one, Complex.norm_natCast]
    exact (div_le_one (by linarith)).mpr hn1
  have he : ‖(spectralCorrection n : ℂ)-
      ((exponentPolynomial M).map (Rat.castHom ℂ)).eval (1/(n : ℂ))‖ ≤
      C*‖(1 : ℂ)/(n : ℂ)‖^M := by
    rw [spectralCorrection_decomposition M n, add_sub_cancel_left]
    have hb := hN n hnN
    simpa only [Complex.norm_real, Real.norm_eq_abs, norm_div, norm_one, Complex.norm_natCast,
      one_div_pow, abs_pow, Nat.abs_cast] using hb
  have hh := h t (1/(n : ℂ)) (spectralCorrection n) ht hz he
  simpa only [one_div_pow, mul_one_div, norm_div, norm_one, Complex.norm_natCast] using hh

end CircleKernel
