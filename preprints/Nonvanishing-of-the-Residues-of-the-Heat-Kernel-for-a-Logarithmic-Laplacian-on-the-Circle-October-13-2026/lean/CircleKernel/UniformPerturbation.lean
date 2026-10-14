import CircleKernel.SpectralNormalization

noncomputable section
open Finset Polynomial
namespace CircleKernel

theorem uniform_perturbed_exponential (M : ℕ) (R C : ℝ) (hR : 0 ≤ R) (hC : 0 ≤ C) :
    ∃ B ≥ 0, ∀ t z w : ℂ, ‖t‖ ≤ R → ‖z‖ ≤ 1 →
      ‖w-((exponentPolynomial M).map (Rat.castHom ℂ)).eval z‖ ≤ C*‖z‖^M →
      ‖Complex.exp (-t*w)-∑ j ∈ range M, (complexResiduePolynomial j).eval t*z^j‖ ≤ B*‖z‖^M := by
  obtain ⟨A,hA,hq⟩ := exponentPolynomial_linear_bound M
  obtain ⟨B,hB,hexp⟩ := uniform_exponential_polynomial M R hR
  let L := R*C*Real.exp (R*A+R*C)
  have hL : 0 ≤ L := by dsimp [L]; positivity
  refine ⟨L+B, add_nonneg hL hB, ?_⟩
  intro t z w ht hz hw
  let v := -t*((exponentPolynomial M).map (Rat.castHom ℂ)).eval z
  have hv : ‖v‖ ≤ R*A := by
    dsimp [v]
    rw [norm_mul, norm_neg]
    calc
      ‖t‖*‖((exponentPolynomial M).map (Rat.castHom ℂ)).eval z‖ ≤ R*(A*‖z‖) :=
        mul_le_mul ht (hq z hz) (norm_nonneg _) hR
      _ ≤ R*A := by simpa only [mul_one, mul_assoc] using mul_le_mul_of_nonneg_left hz (mul_nonneg hR hA)
  have hd : ‖-t*w-v‖ ≤ R*C*‖z‖^M := by
    have he : -t*w-v = -t*(w-((exponentPolynomial M).map (Rat.castHom ℂ)).eval z) := by
      dsimp [v]
      ring
    rw [he, norm_mul, norm_neg]
    calc
      ‖t‖*‖w-((exponentPolynomial M).map (Rat.castHom ℂ)).eval z‖ ≤ R*(C*‖z‖^M) :=
        mul_le_mul ht hw (norm_nonneg _) hR
      _ = _ := by ring
  have hzM : ‖z‖^M ≤ 1 := pow_le_one₀ (norm_nonneg _) hz
  have hd' : ‖-t*w-v‖ ≤ R*C := hd.trans (by nlinarith [mul_nonneg hR hC])
  have hdiff : ‖Complex.exp (-t*w)-Complex.exp v‖ ≤ L*‖z‖^M := by
    apply (complex_exp_difference_bound (-t*w) v).trans
    calc
      ‖-t*w-v‖*Real.exp (‖v‖+‖-t*w-v‖) ≤
          (R*C*‖z‖^M)*Real.exp (R*A+R*C) := by gcongr
      _ = _ := by dsimp [L]; ring
  calc
    ‖Complex.exp (-t*w)-∑ j ∈ range M, (complexResiduePolynomial j).eval t*z^j‖ ≤
        ‖Complex.exp (-t*w)-Complex.exp v‖+
          ‖Complex.exp v-∑ j ∈ range M, (complexResiduePolynomial j).eval t*z^j‖ := by
      simpa only [dist_eq_norm] using dist_triangle (Complex.exp (-t*w)) (Complex.exp v)
        (∑ j ∈ range M, (complexResiduePolynomial j).eval t*z^j)
    _ ≤ L*‖z‖^M+B*‖z‖^M := add_le_add hdiff (hexp t z ht hz)
    _ = _ := by ring

end CircleKernel
