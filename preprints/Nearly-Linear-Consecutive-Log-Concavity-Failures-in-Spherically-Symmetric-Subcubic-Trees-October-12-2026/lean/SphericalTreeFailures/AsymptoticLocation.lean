import SphericalTreeFailures.IndependenceNumber
import SphericalTreeFailures.TotalDecomposition
import Mathlib.Analysis.SpecificLimits.Normed

namespace SphericalTreeFailures
open Filter
open scoped Topology

theorem inverse_two_pow_tendsto :
    Tendsto (fun m : ℕ => ((2 : ℝ) ^ m)⁻¹) atTop (𝓝 0) := by
  simpa only [inv_pow] using
    (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0 : ℝ) ≤ 2⁻¹)
      (by norm_num : (2 : ℝ)⁻¹ < 1))

theorem normalized_independence_error (m k : ℕ) :
    |(independenceNumberOfTree m (2 * k + 1) : ℝ) / 2 ^ m - (k + 5 / 3)| ≤
      2 / (3 * (2 : ℝ) ^ m) := by
  have h := independenceNumber_identity m k
  have he : 3 * (independenceNumberOfTree m (2 * k + 1) : ℝ) +
      (if m % 2 = 0 then (2 : ℝ) else 1) = (3 * (k : ℝ) + 5) * 2 ^ m := by
    exact_mod_cast h
  have hb : (1 : ℝ) ≤ (if m % 2 = 0 then (2 : ℝ) else 1) ∧
      (if m % 2 = 0 then (2 : ℝ) else 1) ≤ 2 := by split_ifs <;> norm_num
  have hd : (2 : ℝ) ^ m ≠ 0 := by positivity
  have hx : (independenceNumberOfTree m (2 * k + 1) : ℝ) / 2 ^ m - (k + 5 / 3) =
      -(if m % 2 = 0 then (2 : ℝ) else 1) / (3 * 2 ^ m) := by
    apply (eq_div_iff (by positivity : (3 : ℝ) * 2 ^ m ≠ 0)).mpr
    field_simp
    nlinarith
  rw [hx, abs_div, abs_neg, abs_of_nonneg (by linarith : 0 ≤ (if m % 2 = 0 then (2 : ℝ) else 1)),
    abs_of_pos (by positivity : (0 : ℝ) < 3 * 2 ^ m)]
  exact div_le_div_of_nonneg_right hb.2 (by positivity)

theorem normalized_independence_tendsto (k : ℕ) :
    Tendsto (fun m => (independenceNumberOfTree m (2 * k + 1) : ℝ) / 2 ^ m)
      atTop (𝓝 ((k : ℝ) + 5 / 3)) := by
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  have ht := inverse_two_pow_tendsto.const_mul (2 / 3 : ℝ)
  simp only [mul_zero] at ht
  apply squeeze_zero (fun _ => norm_nonneg _)
    (fun m => ?_) ht
  rw [Real.norm_eq_abs]
  convert normalized_independence_error m k using 1
  ring

theorem normalized_totalCenter_tendsto (p : ℝ) (k : ℕ) (activity : ℝ) :
    Tendsto (fun m => totalCenter p k m activity / 2 ^ m) atTop
      (𝓝 (totalCenterDensity p k activity)) := by
  have ht := (tendsto_const_nhds (x := totalCenterDensity p k activity)).sub (inverse_two_pow_tendsto.const_mul (stationaryProbability p))
  simp only [mul_zero, sub_zero] at ht
  apply ht.congr'
  exact Eventually.of_forall fun m => by
    unfold totalCenter
    field_simp

theorem totalCenter_location_tendsto (p : ℝ) (k : ℕ) (activity : ℝ) :
    Tendsto (fun m => totalCenter p k m activity /
      (independenceNumberOfTree m (2 * k + 1) : ℝ)) atTop
      (𝓝 (totalCenterDensity p k activity / (k + 5 / 3))) := by
  have ht := (normalized_totalCenter_tendsto p k activity).div (normalized_independence_tendsto k)
    (by positivity : (k : ℝ) + 5 / 3 ≠ 0)
  apply ht.congr'
  exact Eventually.of_forall fun m => by
    change (_ / (2 : ℝ) ^ m) / (_ / (2 : ℝ) ^ m) = _
    rw [div_div_div_cancel_right₀ (by positivity : (2 : ℝ) ^ m ≠ 0)]

end SphericalTreeFailures
