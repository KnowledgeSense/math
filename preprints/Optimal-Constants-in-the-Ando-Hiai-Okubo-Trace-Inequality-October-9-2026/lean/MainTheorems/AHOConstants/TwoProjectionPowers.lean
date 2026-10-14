import MainTheorems.AHOConstants.MatrixFunctionalCalculus
import Mathlib.Tactic.Module

namespace ResearchMain.AHOConstants

open scoped ComplexOrder MatrixOrder Matrix.Norms.L2Operator

variable {I : Type*} [Fintype I] [DecidableEq I]

omit [DecidableEq I] in
theorem orthogonal_projections_reverse {P Q : Matrix I I ℂ}
    (hP : P.PosSemidef) (hQ : Q.PosSemidef) (hPQ : P * Q = 0) : Q * P = 0 := by
  have h := congrArg star hPQ
  simpa only [star_mul, hP.isHermitian.isSelfAdjoint.star_eq,
    hQ.isHermitian.isSelfAdjoint.star_eq, star_zero] using h

theorem twoProjection_spectrum {P Q : Matrix I I ℂ} (hP : P.PosSemidef)
    (hQ : Q.PosSemidef) (hPP : P * P = P) (hQQ : Q * Q = Q)
    (hPQ : P * Q = 0) {ε : ℝ} (hε : 0 ≤ ε) :
    ∀ x ∈ spectrum ℝ (ε • P + Q), x = 0 ∨ x = ε ∨ x = 1 := by
  let A := ε • P + Q
  have hA : A.PosSemidef := (hP.smul hε).add hQ
  have hQP := orthogonal_projections_reverse hP hQ hPQ
  have h₂ : A * A = ε ^ 2 • P + Q := by
    dsimp [A]
    simp only [add_mul, mul_add, Matrix.smul_mul, Matrix.mul_smul, smul_smul,
      hPP, hQQ, hPQ, hQP, smul_zero, zero_add, add_zero]
    rw [show ε * ε = ε ^ 2 by ring]
  have h₃ : A * A * A = ε ^ 3 • P + Q := by
    rw [h₂]
    dsimp [A]
    simp only [add_mul, mul_add, Matrix.smul_mul, Matrix.mul_smul, smul_smul,
      hPP, hQQ, hPQ, hQP, smul_zero, zero_add, add_zero]
    rw [show ε * ε ^ 2 = ε ^ 3 by ring]
  have hpoly : A * (A - ε • 1) * (A - 1) = 0 := by
    calc
      _ = A * A * A - (ε + 1) • (A * A) + ε • A := by
        simp only [mul_sub, sub_mul, Matrix.mul_smul, Matrix.smul_mul,
          Matrix.mul_one]
        module
      _ = 0 := by rw [h₃, h₂]; dsimp [A]; module
  have hf : cfc (fun x : ℝ => x * (x - ε) * (x - 1)) A = 0 := by
    rw [matrix_cfc_mul, matrix_cfc_mul, matrix_cfc_sub, matrix_cfc_sub,
      cfc_id' ℝ A hA.isHermitian.isSelfAdjoint,
      cfc_const ε A hA.isHermitian.isSelfAdjoint,
      cfc_const (1 : ℝ) A hA.isHermitian.isSelfAdjoint,
      Algebra.algebraMap_eq_smul_one, Algebra.algebraMap_eq_smul_one]
    simpa only [one_smul] using hpoly
  have hfg : cfc (fun x : ℝ => x * (x - ε) * (x - 1)) A = cfc (fun _ : ℝ => 0) A := by
    rw [hf, cfc_const_zero]
  have heq := eqOn_of_cfc_eq_cfc hfg (by fun_prop) (by fun_prop) hA.isHermitian.isSelfAdjoint
  intro x hx
  have hz : x * (x - ε) * (x - 1) = 0 := heq hx
  rcases mul_eq_zero.mp hz with hz | hz
  · rcases mul_eq_zero.mp hz with hz | hz
    · exact Or.inl hz
    · exact Or.inr (Or.inl (sub_eq_zero.mp hz))
  · exact Or.inr (Or.inr (sub_eq_zero.mp hz))

theorem twoProjection_spectralPower {P Q : Matrix I I ℂ}
    (hP : P.PosSemidef) (hQ : Q.PosSemidef) (hPP : P * P = P) (hQQ : Q * Q = Q)
    (hPQ : P * Q = 0) {ε r : ℝ} (hε₀ : 0 < ε) (hε₁ : ε < 1) (hr : 0 < r) :
    spectralPower (ε • P + Q) r = ε ^ r • P + Q := by
  let A := ε • P + Q
  have hA : A.PosSemidef := (hP.smul hε₀.le).add hQ
  let c := (ε ^ r - ε ^ 2) / (ε - ε ^ 2)
  let d := (ε - ε ^ r) / (ε - ε ^ 2)
  have hden : ε - ε ^ 2 ≠ 0 := by
    have hp : 0 < ε * (1 - ε) := mul_pos hε₀ (by linarith)
    nlinarith
  have hc : c * ε + d * ε ^ 2 = ε ^ r := by
    dsimp [c, d]
    rw [div_mul_eq_mul_div, div_mul_eq_mul_div, ← add_div]
    apply (div_eq_iff hden).mpr
    ring
  have hcd : c + d = 1 := by
    dsimp [c, d]
    rw [← add_div]
    apply (div_eq_iff hden).mpr
    ring
  have hspec := twoProjection_spectrum hP hQ hPP hQQ hPQ hε₀.le
  have he : cfc (fun x : ℝ => x ^ r) A = cfc (fun x : ℝ => c * x + d * x ^ 2) A := by
    apply cfc_congr
    intro x hx
    rcases hspec x hx with rfl | rfl | rfl
    · simp [Real.zero_rpow hr.ne']
    · exact hc.symm
    · simpa only [Real.one_rpow, one_pow, mul_one] using hcd.symm
  change A ^ r = _
  rw [CFC.rpow_eq_cfc_real hA.nonneg, he, matrix_cfc_add, matrix_cfc_const_mul,
    matrix_cfc_const_mul,
    cfc_id' ℝ A hA.isHermitian.isSelfAdjoint, cfc_pow_id A 2 hA.isHermitian.isSelfAdjoint]
  have hQP := orthogonal_projections_reverse hP hQ hPQ
  have h₂ : A ^ 2 = ε ^ 2 • P + Q := by
    rw [pow_two]
    dsimp [A]
    simp only [add_mul, mul_add, Matrix.smul_mul, Matrix.mul_smul, smul_smul,
      hPP, hQQ, hPQ, hQP, smul_zero, zero_add, add_zero]
    rw [show ε * ε = ε ^ 2 by ring]
  rw [h₂]
  calc
    c • A + d • (ε ^ 2 • P + Q) =
        (c * ε + d * ε ^ 2) • P + (c + d) • Q := by dsimp [A]; module
    _ = _ := by rw [hc, hcd, one_smul]

end ResearchMain.AHOConstants
