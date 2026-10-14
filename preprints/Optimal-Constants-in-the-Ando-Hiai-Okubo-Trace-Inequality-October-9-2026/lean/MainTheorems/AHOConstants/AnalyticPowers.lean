import MainTheorems.AHOConstants.ComplexPowers
import Mathlib.Analysis.Complex.Hadamard
import Mathlib.Analysis.Complex.Trigonometric

namespace ResearchMain.AHOConstants

open scoped ComplexOrder MatrixOrder Matrix.Norms.L2Operator

variable {I : Type*} [Fintype I] [DecidableEq I]

theorem complexPower_differentiable {A : Matrix I I ℂ} (hA : A.PosDef) :
    Differentiable ℂ (complexPower hA) := by
  let E : ℂ → I → ℂ := fun z i =>
    Complex.exp ((Real.log (hA.isHermitian.eigenvalues i) : ℂ) * z)
  have hE : Differentiable ℂ E := by
    apply differentiable_pi.mpr
    intro i
    dsimp [E]
    fun_prop
  let D : (I → ℂ) →L[ℂ] Matrix I I ℂ :=
    (Matrix.diagonalLinearMap I ℂ ℂ).toContinuousLinearMap
  let K : Matrix I I ℂ →L[ℂ] Matrix I I ℂ :=
    (Unitary.conjStarAlgAut ℂ (Matrix I I ℂ) hA.isHermitian.eigenvectorUnitary).toAlgEquiv.toLinearEquiv.toLinearMap.toContinuousLinearMap
  exact K.differentiable.comp (D.differentiable.comp hE)

theorem exponential_strip_bound (a t : ℝ) (ht₀ : 0 ≤ t) (ht₁ : t ≤ 1) :
    Real.exp (a * t) ≤ max 1 (Real.exp a) := by
  by_cases ha : 0 ≤ a
  · apply (Real.exp_le_exp.mpr (by nlinarith)).trans
    exact le_max_right _ _
  · have h : a * t ≤ 0 := mul_nonpos_of_nonpos_of_nonneg (le_of_lt (lt_of_not_ge ha)) ht₀
    calc
      Real.exp (a * t) ≤ Real.exp 0 := Real.exp_le_exp.mpr h
      _ = 1 := Real.exp_zero
      _ ≤ max 1 (Real.exp a) := le_max_left _ _

theorem complexPower_bounded_strip {A : Matrix I I ℂ} (hA : A.PosDef) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ z : ℂ, 0 ≤ z.re → z.re ≤ 1 → ‖complexPower hA z‖ ≤ C := by
  let U : Matrix I I ℂ := hA.isHermitian.eigenvectorUnitary
  let M : ℝ := ‖fun i : I => max 1 (Real.exp (Real.log (hA.isHermitian.eigenvalues i)))‖
  have hM : 0 ≤ M := norm_nonneg _
  refine ⟨‖U‖ * M * ‖U‖, by positivity, fun z hz₀ hz₁ => ?_⟩
  have hd : ‖Matrix.diagonal (fun i : I =>
      Complex.exp ((Real.log (hA.isHermitian.eigenvalues i) : ℂ) * z))‖ ≤ M := by
    rw [Matrix.l2_opNorm_diagonal]
    apply (pi_norm_le_iff_of_nonneg hM).2
    intro i
    rw [Complex.norm_exp]
    simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
    calc
      Real.exp (Real.log (hA.isHermitian.eigenvalues i) * z.re) ≤
        max 1 (Real.exp (Real.log (hA.isHermitian.eigenvalues i))) :=
          exponential_strip_bound _ _ hz₀ hz₁
      _ ≤ M := by
        have hi := norm_le_pi_norm
          (fun j : I => max 1 (Real.exp (Real.log (hA.isHermitian.eigenvalues j)))) i
        simpa only [Real.norm_of_nonneg (le_trans (by norm_num : (0 : ℝ) ≤ 1)
          (le_max_left 1 _))] using hi
  unfold complexPower
  rw [Unitary.conjStarAlgAut_apply]
  change ‖U * Matrix.diagonal _ * star U‖ ≤ ‖U‖ * M * ‖U‖
  calc
    ‖U * Matrix.diagonal _ * star U‖ ≤ ‖U * Matrix.diagonal _‖ * ‖star U‖ := norm_mul_le _ _
    _ ≤ (‖U‖ * ‖Matrix.diagonal _‖) * ‖star U‖ :=
      mul_le_mul_of_nonneg_right (norm_mul_le _ _) (norm_nonneg _)
    _ ≤ (‖U‖ * M) * ‖U‖ := by rw [norm_star]; gcongr

end ResearchMain.AHOConstants
