import Mathlib.Analysis.Convex.SpecificFunctions.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic

namespace ResearchMain.DiagonalSchatten

noncomputable section

theorem negative_power_tangent {r t : ℝ} (hr : r ≤ 0) (ht : 0 < t) :
    1 + r * (t - 1) ≤ t ^ r := by
  have hlog := Real.log_le_sub_one_of_pos ht
  have hmul := mul_le_mul_of_nonpos_left hlog hr
  have hexp := Real.add_one_le_exp (r * Real.log t)
  have hp : t ^ r = Real.exp (r * Real.log t) := by
    rw [Real.rpow_def_of_pos ht]
    congr 1
    ring
  rw [hp]
  linarith

theorem negative_power_tangent_strict {r t : ℝ}
    (hr : r < 0) (ht : 0 < t) (hneq : t ≠ 1) :
    1 + r * (t - 1) < t ^ r := by
  have hlog := Real.log_le_sub_one_of_pos ht
  have hmul := mul_le_mul_of_nonpos_left hlog hr.le
  have hexp := Real.add_one_lt_exp
    (mul_ne_zero hr.ne (Real.log_ne_zero_of_pos_of_ne_one ht hneq))
  have hp : t ^ r = Real.exp (r * Real.log t) := by
    rw [Real.rpow_def_of_pos ht]
    congr 1
    ring
  rw [hp]
  linarith

def lowerPowerRemainder (m t : ℝ) : ℝ :=
  t + 1 - 2 * m + m * t ^ (-(m - 1) / 2) + (m - 2) * t ^ ((m + 1) / 2)

def lowerPowerQuadratic (m t y : ℝ) : ℝ :=
  t * y ^ 2 + (t + 1 - 2 * m) * y + m * (m - 2)

theorem lowerPowerRemainder_positive {m t : ℝ}
    (hm : 2 ≤ m) (ht : 0 < t) (hneq : t ≠ 1) :
    0 < lowerPowerRemainder m t := by
  have hm0 : 0 < m := lt_of_lt_of_le (by norm_num) hm
  have hm2 : 0 ≤ m - 2 := sub_nonneg.mpr hm
  have hr : -(m - 1) / 2 < 0 := by linarith
  have hfirst := negative_power_tangent_strict hr ht hneq
  have hsecond : 1 + ((m + 1) / 2) * (t - 1) ≤ t ^ ((m + 1) / 2) := by
    have h := one_add_mul_self_le_rpow_one_add
      (s := t - 1) (by linarith) (p := (m + 1) / 2) (by linarith)
    simpa only [show 1 + (t - 1) = t by ring] using h
  have hfirst' := mul_lt_mul_of_pos_left hfirst hm0
  have hsecond' := mul_le_mul_of_nonneg_left hsecond hm2
  unfold lowerPowerRemainder
  nlinarith

theorem lowerPowerQuadratic_at_baseline {m t : ℝ} (ht : 0 < t) :
    lowerPowerQuadratic m t (m * t ^ (-(m + 1) / 2)) =
      m * t ^ (-(m + 1) / 2) * lowerPowerRemainder m t := by
  have hfirst : t ^ (-(m + 1) / 2) * t ^ (-(m - 1) / 2) =
      t * (t ^ (-(m + 1) / 2)) ^ 2 := by
    rw [← Real.rpow_add ht]
    have he : -(m + 1) / 2 + -(m - 1) / 2 = 1 + (-(m + 1) / 2) * 2 := by ring
    rw [he, Real.rpow_add ht, Real.rpow_one,
      Real.rpow_mul ht.le, Real.rpow_two]
  have hsecond : t ^ (-(m + 1) / 2) * t ^ ((m + 1) / 2) = 1 := by
    rw [← Real.rpow_add ht, show -(m + 1) / 2 + (m + 1) / 2 = 0 by ring, Real.rpow_zero]
  unfold lowerPowerQuadratic lowerPowerRemainder
  linear_combination -m ^ 2 * hfirst - m * (m - 2) * hsecond

theorem lowerPowerQuadratic_baseline_positive {m t : ℝ}
    (hm : 2 ≤ m) (ht : 0 < t) (hneq : t ≠ 1) :
    0 < lowerPowerQuadratic m t (m * t ^ (-(m + 1) / 2)) := by
  rw [lowerPowerQuadratic_at_baseline ht]
  have hm0 : 0 < m := lt_of_lt_of_le (by norm_num) hm
  exact mul_pos (mul_pos hm0 (Real.rpow_pos_of_pos ht _))
    (lowerPowerRemainder_positive hm ht hneq)

end

end ResearchMain.DiagonalSchatten
