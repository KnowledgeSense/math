import SphericalTreeFailures.FourierScale

namespace SphericalTreeFailures

 theorem power_contraction_bound {ρ D T : ℝ} (hρ0 : 0 < ρ) (hρ1 : ρ < 1)
    (hD : 0 < D) (n : ℕ) (hT : T ≤ D * n) :
    ρ ^ n ≤ Real.exp (-(-Real.log ρ / D) * T) := by
  have hl : Real.log ρ < 0 := Real.log_neg hρ0 hρ1
  have he : ρ ^ n = Real.exp ((n : ℝ) * Real.log ρ) := by
    rw [Real.exp_nat_mul, Real.exp_log hρ0]
  rw [he]
  apply Real.exp_le_exp.mpr
  have ht := mul_le_mul_of_nonpos_left hT hl.le
  have hd := (div_le_div_iff_of_pos_right hD).mpr ht
  convert hd using 1 <;> field_simp

theorem contraction_constant_pos {ρ D : ℝ} (hρ0 : 0 < ρ) (hρ1 : ρ < 1) (hD : 0 < D) :
    0 < -Real.log ρ / D := div_pos (neg_pos.mpr (Real.log_neg hρ0 hρ1)) hD

theorem small_frequency_exponential_bound {c β t : ℝ} (hc : 0 ≤ c) (hβ : 0 ≤ β) (ht : |t| ≤ 1) :
    1 ≤ Real.exp c * Real.exp (-c * |t| ^ β) := by
  rw [← Real.exp_add, ← Real.exp_zero]
  apply Real.exp_le_exp.mpr
  have h := Real.rpow_le_rpow (abs_nonneg t) ht hβ
  rw [Real.one_rpow] at h
  nlinarith

end SphericalTreeFailures
