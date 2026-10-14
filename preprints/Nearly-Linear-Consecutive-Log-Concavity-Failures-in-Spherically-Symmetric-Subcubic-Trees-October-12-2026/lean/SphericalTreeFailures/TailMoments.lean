import SphericalTreeFailures.TuningExistence

namespace SphericalTreeFailures
open Finset

noncomputable def oddDeficit (k : ℕ) (y : ℝ) : ℝ :=
  (∑ j ∈ range (k + 2), (j : ℝ) * oddReverseCoefficient k j * y ^ j) /
    oddReverseSum k y
noncomputable def evenDeficit (k : ℕ) (y : ℝ) : ℝ :=
  (∑ j ∈ range (k + 1), (j : ℝ) * evenReverseCoefficient k j * y ^ j) /
    evenReverseSum k y

theorem tuning_scaled_argument_refined {k : ℕ} {r : ℝ} (hk : 16384 ≤ k)
    (hr : (k : ℝ) / 2 ≤ r) :
    (reverseScale k : ℝ) / tunedActivity r ≤ 128 / k := by
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
  apply (div_le_div_iff₀ ha hk0).mpr
  have hm := mul_le_mul_of_nonneg_right hD (le_of_lt hk0)
  nlinarith

theorem oddDeficit_bounds (k : ℕ) {y : ℝ} (hy : 0 ≤ y) :
    0 ≤ oddDeficit k y ∧
      oddDeficit k y ≤ (reverseScale k : ℝ) * y * Real.exp ((reverseScale k : ℝ) * y) := by
  have hs := oddReverseSum_lower k hy
  have hn : 0 ≤ ∑ j ∈ range (k + 2), (j : ℝ) * oddReverseCoefficient k j * y ^ j :=
    sum_nonneg (fun j hj => by unfold oddReverseCoefficient; positivity)
  constructor
  · exact div_nonneg hn (by linarith)
  · have h := finite_weighted_exponential_bound (Nat.cast_nonneg _) hy
      (oddReverseCoefficient_exponential_bound k) (k + 2)
    exact (div_le_self hn hs).trans h

theorem evenDeficit_bounds (k : ℕ) {y : ℝ} (hy : 0 ≤ y) :
    0 ≤ evenDeficit k y ∧
      evenDeficit k y ≤ (reverseScale k : ℝ) * y * Real.exp ((reverseScale k : ℝ) * y) := by
  have hs := evenReverseSum_lower k hy
  have hn : 0 ≤ ∑ j ∈ range (k + 1), (j : ℝ) * evenReverseCoefficient k j * y ^ j :=
    sum_nonneg (fun j hj => by unfold evenReverseCoefficient; positivity)
  constructor
  · exact div_nonneg hn (by linarith)
  · have h := finite_weighted_exponential_bound (Nat.cast_nonneg _) hy
      (evenReverseCoefficient_exponential_bound k) (k + 1)
    exact (div_le_self hn hs).trans h

theorem tuned_deficit_bounds {k : ℕ} {r : ℝ} (hk : 16384 ≤ k)
    (hr : (k : ℝ) / 2 ≤ r) :
    0 ≤ oddDeficit k (1 / tunedActivity r) ∧
    oddDeficit k (1 / tunedActivity r) ≤ 256 / k ∧
    0 ≤ evenDeficit k (1 / tunedActivity r) ∧
    evenDeficit k (1 / tunedActivity r) ≤ 256 / k ∧ (256 / (k : ℝ)) ≤ 1 / 64 := by
  have hk' : (16384 : ℝ) ≤ k := by exact_mod_cast hk
  have hk0 : (0 : ℝ) < k := by linarith
  have ha := tunedActivity_pos (by linarith : 0 < r)
  have hy : 0 ≤ 1 / tunedActivity r := by positivity
  have hz0 : 0 ≤ (reverseScale k : ℝ) * (1 / tunedActivity r) := mul_nonneg (Nat.cast_nonneg _) hy
  have hz := tuning_scaled_argument_bound hk hr
  have hzr := tuning_scaled_argument_refined hk hr
  rw [← mul_one_div] at hz hzr
  have he := small_exp_bound hz0 hz
  have hp := mul_le_mul_of_nonneg_left he hz0
  have hbound : (reverseScale k : ℝ) * (1 / tunedActivity r) *
      Real.exp ((reverseScale k : ℝ) * (1 / tunedActivity r)) ≤ 256 / k := by
    have hn : 0 ≤ (128 / (k : ℝ)) := by positivity
    have hh := mul_le_mul_of_nonneg_right hzr (by norm_num : (0 : ℝ) ≤ 3 / 2)
    have hid : (256 / (k : ℝ)) = 2 * (128 / k) := by ring
    rw [hid]
    nlinarith
  obtain ⟨ho0, ho⟩ := oddDeficit_bounds k hy
  obtain ⟨he0, he'⟩ := evenDeficit_bounds k hy
  refine ⟨ho0, ho.trans hbound, he0, he'.trans hbound, ?_⟩
  exact (div_le_iff₀ hk0).mpr (by linarith)

end SphericalTreeFailures
