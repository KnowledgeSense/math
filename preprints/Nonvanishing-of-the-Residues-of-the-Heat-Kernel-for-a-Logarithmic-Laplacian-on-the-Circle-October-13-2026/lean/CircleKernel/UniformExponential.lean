import CircleKernel.UniformTaylorPolynomial
import Mathlib.Analysis.Complex.Exponential

noncomputable section
open Finset Polynomial
namespace CircleKernel

theorem exponentPolynomial_zero (M : ℕ) : (exponentPolynomial M).coeff 0 = 0 := by
  simp [exponentPolynomial, PowerSeries.coeff_trunc, PowerSeries.coeff_mk]

theorem exponentPolynomial_linear_bound (M : ℕ) :
    ∃ A ≥ 0, ∀ z : ℂ, ‖z‖ ≤ 1 →
      ‖((exponentPolynomial M).map (Rat.castHom ℂ)).eval z‖ ≤ A*‖z‖ := by
  obtain ⟨A,hA,h⟩ := polynomial_tail_bound ((exponentPolynomial M).map (Rat.castHom ℂ)) 1
  refine ⟨A,hA,?_⟩
  intro z hz
  simpa [exponentPolynomial_zero] using h z hz

theorem exponentialTaylorPolynomial_eval (M : ℕ) (t z : ℂ) :
    (exponentialTaylorPolynomial M t).eval z =
      ∑ ell ∈ range M, (-t*((exponentPolynomial M).map (Rat.castHom ℂ)).eval z)^ell /
        (ell.factorial : ℂ) := by
  simp only [exponentialTaylorPolynomial, eval_finsetSum, eval_mul, eval_C, eval_pow]
  apply sum_congr rfl
  intro ell hell
  rw [mul_pow]
  ring

theorem uniform_exponential_polynomial (M : ℕ) (R : ℝ) (hR : 0 ≤ R) :
    ∃ B ≥ 0, ∀ t z : ℂ, ‖t‖ ≤ R → ‖z‖ ≤ 1 →
      ‖Complex.exp (-t*((exponentPolynomial M).map (Rat.castHom ℂ)).eval z) -
        ∑ j ∈ range M, (complexResiduePolynomial j).eval t*z^j‖ ≤ B*‖z‖^M := by
  obtain ⟨A,hA,hq⟩ := exponentPolynomial_linear_bound M
  obtain ⟨B,hB,hpoly⟩ := exponentialTaylorPolynomial_tail M R hR
  let K := R*A
  have hK : 0 ≤ K := mul_nonneg hR hA
  refine ⟨K^M*Real.exp K+B, by positivity, ?_⟩
  intro t z ht hz
  let w := -t*((exponentPolynomial M).map (Rat.castHom ℂ)).eval z
  have hw : ‖w‖ ≤ K*‖z‖ := by
    dsimp [w,K]
    rw [norm_mul, norm_neg]
    calc
      ‖t‖*‖((exponentPolynomial M).map (Rat.castHom ℂ)).eval z‖ ≤ R*(A*‖z‖) :=
        mul_le_mul ht (hq z hz) (norm_nonneg _) hR
      _ = _ := by ring
  have hwK : ‖w‖ ≤ K := hw.trans (by nlinarith)
  have hexp : ‖Complex.exp w-(exponentialTaylorPolynomial M t).eval z‖ ≤
      K^M*Real.exp K*‖z‖^M := by
    rw [exponentialTaylorPolynomial_eval]
    apply (Complex.norm_exp_sub_sum_le_norm_mul_exp w M).trans
    calc
      ‖w‖^M*Real.exp ‖w‖ ≤ (K*‖z‖)^M*Real.exp K := by
        gcongr
      _ = _ := by rw [mul_pow]; ring
  calc
    ‖Complex.exp w-∑ j ∈ range M, (complexResiduePolynomial j).eval t*z^j‖ ≤
        ‖Complex.exp w-(exponentialTaylorPolynomial M t).eval z‖ +
        ‖(exponentialTaylorPolynomial M t).eval z-
          ∑ j ∈ range M, (complexResiduePolynomial j).eval t*z^j‖ := by simpa only [dist_eq_norm] using dist_triangle (Complex.exp w) ((exponentialTaylorPolynomial M t).eval z) (∑ j ∈ range M, (complexResiduePolynomial j).eval t*z^j)
    _ ≤ K^M*Real.exp K*‖z‖^M+B*‖z‖^M := add_le_add hexp (hpoly t z ht hz)
    _ = _ := by ring

end CircleKernel
