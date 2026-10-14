import SphericalTreeFailures.ReversedPartition
import SphericalTreeFailures.ParameterBounds

namespace SphericalTreeFailures

noncomputable def tunedActivity (r : ℝ) : ℝ := r * (1 + r) ^ 2

theorem tunedActivity_pos {r : ℝ} (hr : 0 < r) : 0 < tunedActivity r := by
  unfold tunedActivity
  positivity

theorem tuning_scaled_argument_bound {k : ℕ} {r : ℝ} (hk : 16384 ≤ k)
    (hr : (k : ℝ) / 2 ≤ r) :
    (reverseScale k : ℝ) / tunedActivity r ≤ 1 / 128 := by
  have hk' : (16384 : ℝ) ≤ k := by exact_mod_cast hk
  have hk0 : (0 : ℝ) < k := by linarith
  have hr0 : 0 < r := by linarith
  have ha := tunedActivity_pos hr0
  have hD : (reverseScale k : ℝ) ≤ 16 * (k : ℝ) ^ 2 := by
    simp only [reverseScale, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_pow, Nat.cast_add, Nat.cast_one]
    nlinarith
  have hp := pow_le_pow_left₀ (by positivity : (0 : ℝ) ≤ (k : ℝ) / 2) hr 3
  have hA : (k : ℝ) ^ 3 / 8 ≤ tunedActivity r := by
    unfold tunedActivity
    nlinarith [sq_nonneg r]
  have hlarge : 2048 * (k : ℝ) ^ 2 ≤ (k : ℝ) ^ 3 / 8 := by
    nlinarith [mul_nonneg (show 0 ≤ (k : ℝ) - 16384 by linarith) (sq_nonneg (k : ℝ))]
  apply (div_le_iff₀ ha).mpr
  nlinarith

theorem small_exp_bound {z : ℝ} (hz : 0 ≤ z) (hsmall : z ≤ 1 / 128) :
    Real.exp z ≤ 3 / 2 := by
  have h := Real.exp_bound_div_one_sub_of_interval hz (by linarith)
  have hd : 0 < 1 - z := by linarith
  have hh : 1 / (1 - z) ≤ (3 / 2 : ℝ) := (div_le_iff₀ hd).mpr (by linarith)
  exact h.trans hh

theorem tuning_reverseSum_bounds {k : ℕ} {r : ℝ} (hk : 16384 ≤ k)
    (hr : (k : ℝ) / 2 ≤ r) :
    1 ≤ oddReverseSum k (1 / tunedActivity r) ∧
    oddReverseSum k (1 / tunedActivity r) ≤ 3 / 2 ∧
    1 ≤ evenReverseSum k (1 / tunedActivity r) ∧
    evenReverseSum k (1 / tunedActivity r) ≤ 3 / 2 := by
  have hk' : (16384 : ℝ) ≤ k := by exact_mod_cast hk
  have ha := tunedActivity_pos (by linarith : 0 < r)
  have hy : 0 ≤ 1 / tunedActivity r := by positivity
  have hs : (reverseScale k : ℝ) * (1 / tunedActivity r) ≤ 1 / 128 := by
    simpa only [mul_one_div] using tuning_scaled_argument_bound hk hr
  have he := small_exp_bound (mul_nonneg (Nat.cast_nonneg _) hy) hs
  exact ⟨oddReverseSum_lower k hy, (oddReverseSum_upper k hy).trans he,
    evenReverseSum_lower k hy, (evenReverseSum_upper k hy).trans he⟩

end SphericalTreeFailures
