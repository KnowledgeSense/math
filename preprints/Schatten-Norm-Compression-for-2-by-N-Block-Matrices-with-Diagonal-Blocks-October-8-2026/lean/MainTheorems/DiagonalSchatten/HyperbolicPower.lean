import MainTheorems.DiagonalSchatten.HyperbolicBounds
import Mathlib.Analysis.SpecialFunctions.Pow.Real

namespace ResearchMain.DiagonalSchatten

theorem exponential_sinh_ratio (m : ℝ) {x : ℝ} (hx : x ≠ 0) :
    (1 - Real.exp (-2 * m * x)) / (Real.exp (2 * x) - 1) =
      Real.exp (-(m + 1) * x) * (Real.sinh (m * x) / Real.sinh x) := by
  have he : Real.exp x ≠ 0 := (Real.exp_pos x).ne'
  have hf : Real.exp (m * x) ≠ 0 := (Real.exp_pos (m * x)).ne'
  have htwo : Real.exp (2 * x) = Real.exp x ^ 2 := by
    rw [pow_two, ← Real.exp_add]
    congr 1
    ring
  have hnegative : Real.exp (-2 * m * x) = (Real.exp (m * x) ^ 2)⁻¹ := by
    rw [show -2 * m * x = -(m * x + m * x) by ring,
      Real.exp_neg, Real.exp_add, pow_two]
  have hweight : Real.exp (-(m + 1) * x) = (Real.exp (m * x) * Real.exp x)⁻¹ := by
    rw [show -(m + 1) * x = -(m * x + x) by ring,
      Real.exp_neg, Real.exp_add]
  have hen : Real.exp x ^ 2 - 1 ≠ 0 := by
    intro h
    have h' : Real.exp (2 * x) = Real.exp 0 := by rw [htwo]; simpa using (sub_eq_zero.mp h)
    have hzero := Real.exp_injective h'
    apply hx
    linarith
  have hsinh : Real.exp x - (Real.exp x)⁻¹ ≠ 0 := by
    intro h
    have hs : Real.sinh x = 0 := by rw [Real.sinh_eq, Real.exp_neg, h]; norm_num
    exact hx (Real.sinh_eq_zero.mp hs)
  rw [htwo, hnegative, hweight]
  simp only [Real.sinh_eq, Real.exp_neg]
  field_simp [he, hf, hen, hsinh]

theorem negative_divided_power_ge_baseline {m t : ℝ}
    (hm : 1 ≤ m) (ht : 0 < t) (hneq : t ≠ 1) :
    m * t ^ (-(m + 1) / 2) ≤ (1 - t ^ (-m)) / (t - 1) := by
  let x := Real.log t / 2
  have hx : x ≠ 0 := by
    intro h
    have hl := Real.log_ne_zero_of_pos_of_ne_one ht hneq
    apply hl
    dsimp [x] at h
    linarith
  have hratio := exponential_sinh_ratio m hx
  have htExp : Real.exp (2 * x) = t := by
    dsimp [x]
    rw [show 2 * (Real.log t / 2) = Real.log t by ring, Real.exp_log ht]
  have hnegative : Real.exp (-2 * m * x) = t ^ (-m) := by
    rw [Real.rpow_def_of_pos ht]
    congr 1
    dsimp [x]
    ring
  have hweight : Real.exp (-(m + 1) * x) = t ^ (-(m + 1) / 2) := by
    rw [Real.rpow_def_of_pos ht]
    congr 1
    dsimp [x]
    ring
  rw [htExp, hnegative, hweight] at hratio
  have hs := sinh_ratio_bound hm hx
  have h := mul_le_mul_of_nonneg_left hs (Real.rpow_pos_of_pos ht (-(m + 1) / 2)).le
  rw [← hratio] at h
  simpa only [mul_comm] using h

end ResearchMain.DiagonalSchatten
