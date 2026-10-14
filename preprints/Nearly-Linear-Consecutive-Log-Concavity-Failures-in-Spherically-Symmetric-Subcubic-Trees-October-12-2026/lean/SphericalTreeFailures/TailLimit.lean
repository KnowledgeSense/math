import SphericalTreeFailures.TotalTailVariance
import SphericalTreeFailures.CensusLimit

namespace SphericalTreeFailures
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal Topology

noncomputable def normalizedTailL2 (p : unitInterval) (k m : ℕ) (activity : ℝ)
    (ha : 0 < activity) (i : Bool) (γ : ℝ) : Lp ℝ 2 (totalSizeMeasure p k activity ha) :=
  ((memLp_tailNoise p k m activity ha i 2).const_mul ((-γ) ^ m)⁻¹).toLp
    (fun ω => ((-γ) ^ m)⁻¹ * tailNoise k m activity i ω)

theorem normalizedTailL2_sq_bound (p : unitInterval) (k m : ℕ) (activity : ℝ)
    (ha : 0 < activity) (i : Bool) (γ : ℝ) :
    ‖normalizedTailL2 p k m activity ha i γ‖ ^ 2 ≤
      (2 * (k : ℝ) + 1) ^ 2 * (2 / γ ^ 2) ^ m := by
  rw [normalizedTailL2, norm_toLp_sq]
  simp_rw [mul_pow]
  rw [integral_const_mul]
  have h := mul_le_mul_of_nonneg_left (total_tail_variance_bound p k m activity ha i)
    (sq_nonneg (((-γ) ^ m)⁻¹))
  refine h.trans_eq ?_
  rw [inv_pow, ← pow_mul, Nat.mul_comm m 2, pow_mul, neg_sq, div_pow]
  rw [div_eq_mul_inv]
  ring

theorem normalizedTailL2_norm_bound (p : unitInterval) (k m : ℕ) (activity : ℝ)
    (ha : 0 < activity) (i : Bool) (γ : ℝ) :
    ‖normalizedTailL2 p k m activity ha i γ‖ ≤
      (2 * (k : ℝ) + 1) * Real.sqrt (2 / γ ^ 2) ^ m := by
  apply (sq_le_sq₀ (norm_nonneg _) (by positivity)).mp
  rw [mul_pow, ← pow_mul, Nat.mul_comm m 2, pow_mul, Real.sq_sqrt (by positivity)]
  exact normalizedTailL2_sq_bound p k m activity ha i γ

theorem normalizedTailL2_tendsto (p : unitInterval) (k : ℕ) (activity : ℝ)
    (ha : 0 < activity) (i : Bool) (γ : ℝ) (hc : 2 < γ ^ 2) :
    Tendsto (fun m => normalizedTailL2 p k m activity ha i γ) atTop (𝓝 0) := by
  apply tendsto_zero_iff_norm_tendsto_zero.mpr
  have hr : Real.sqrt (2 / γ ^ 2) < 1 := by
    apply (Real.sqrt_lt' (by norm_num : (0 : ℝ) < 1)).mpr
    simpa using (div_lt_one (by positivity : 0 < γ ^ 2)).mpr hc
  have ht := (tendsto_pow_atTop_nhds_zero_of_lt_one (Real.sqrt_nonneg _) hr).const_mul
    (2 * (k : ℝ) + 1)
  simp only [mul_zero] at ht
  exact squeeze_zero (fun _ => norm_nonneg _)
    (fun m => normalizedTailL2_norm_bound p k m activity ha i γ) ht

end SphericalTreeFailures
