import SphericalTreeFailures.IntegerRuns
import SphericalTreeFailures.AsymptoticLocation

namespace SphericalTreeFailures
open Filter
open scoped Topology

theorem releaseScale_normalized_tendsto (k : ℕ) (hk : 16384 ≤ k) :
    Tendsto (fun m => releaseScale k hk m / (2 : ℝ) ^ m) atTop (𝓝 0) := by
  have hγ0 := release_scale_gt_one k hk
  have hγ2 := (fluctuationScale_bounds hk (releaseParameter_spec k hk).1).2.1
  simpa only [releaseScale, div_pow] using
    tendsto_pow_atTop_nhds_zero_of_lt_one
      (by positivity : 0 ≤ fluctuationScale (releaseParameter k hk) / 2)
      ((div_lt_one (by norm_num : (0 : ℝ) < 2)).mpr hγ2)

theorem releaseScale_alpha_tendsto (k : ℕ) (hk : 16384 ≤ k) :
    Tendsto (fun m => releaseScale k hk m / (independenceNumberOfTree m (2 * k + 1) : ℝ))
      atTop (𝓝 0) := by
  have h := (releaseScale_normalized_tendsto k hk).div (normalized_independence_tendsto k)
    (by positivity : (k : ℝ) + 5 / 3 ≠ 0)
  simp only [zero_div] at h
  apply h.congr'
  exact Eventually.of_forall fun m => by
    change (releaseScale k hk m / (2 : ℝ) ^ m) / ((independenceNumberOfTree m (2 * k + 1) : ℝ) / (2 : ℝ) ^ m) = _
    rw [div_div_div_cancel_right₀ (by positivity : (2 : ℝ) ^ m ≠ 0)]

theorem releaseCenter_location_tendsto (k : ℕ) (hk : 16384 ≤ k) :
    Tendsto (fun m => releaseCenter k hk m / (independenceNumberOfTree m (2 * k + 1) : ℝ))
      atTop (𝓝 (locationFraction k (releaseParameter k hk))) := by
  have h := totalCenter_location_tendsto (releaseBroadcastParameter k hk) k
    (tunedActivity (releaseParameter k hk))
  change Tendsto _ _ (𝓝 (totalCenterDensity (broadcastParameter (releaseParameter k hk)) k (tunedActivity (releaseParameter k hk)) / (k + 5 / 3))) at h
  rw [totalCenterDensity_tuned] at h
  exact h

theorem run_grid_bounded (k : ℕ) (hk : 16384 ≤ k) (a b : ℝ) (m : ℕ)
    {j : ℤ} (hj : j ∈ releaseRun k hk a b m) :
    |releaseGrid k hk m j| ≤ |a| + |b| := by
  have h := (mem_releaseRun k hk a b m j).mp hj
  have ha := neg_abs_le a
  have hb := le_abs_self b
  have hz := abs_nonneg a
  have hz' := abs_nonneg b
  have hab : |(-1 : ℝ) ^ m * releaseGrid k hk m j| ≤ |a| + |b| :=
    abs_le.mpr ⟨by linarith [h.1], by linarith [h.2]⟩
  simpa only [abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul] using hab

theorem run_location_error (k : ℕ) (hk : 16384 ≤ k) (a b : ℝ) (m : ℕ)
    {j : ℤ} (hj : j ∈ releaseRun k hk a b m) :
    |(j : ℝ) / independenceNumberOfTree m (2 * k + 1) - locationFraction k (releaseParameter k hk)| ≤
      (|a| + |b|) * (releaseScale k hk m / independenceNumberOfTree m (2 * k + 1)) +
      |releaseCenter k hk m / independenceNumberOfTree m (2 * k + 1) - locationFraction k (releaseParameter k hk)| := by
  have hα : (0 : ℝ) ≤ independenceNumberOfTree m (2 * k + 1) := by positivity
  have hH := releaseScale_pos k hk m
  have hgrid := run_grid_bounded k hk a b m hj
  have he : |(j : ℝ) - releaseCenter k hk m| ≤ (|a| + |b|) * releaseScale k hk m := by
    unfold releaseGrid at hgrid
    rwa [abs_div, abs_of_pos hH, div_le_iff₀ hH] at hgrid
  calc
    _ ≤ |((j : ℝ) - releaseCenter k hk m) / independenceNumberOfTree m (2 * k + 1)| +
      |releaseCenter k hk m / independenceNumberOfTree m (2 * k + 1) - locationFraction k (releaseParameter k hk)| := by
      convert abs_add_le (((j : ℝ) - releaseCenter k hk m) / independenceNumberOfTree m (2 * k + 1))
        (releaseCenter k hk m / independenceNumberOfTree m (2 * k + 1) - locationFraction k (releaseParameter k hk)) using 1
      congr 1
      ring
    _ ≤ _ := by
      apply add_le_add_left
      rw [abs_div, abs_of_nonneg hα]
      convert div_le_div_of_nonneg_right he hα using 1
      ring

theorem releaseRun_location_uniform (k : ℕ) (hk : 16384 ≤ k) (a b : ℝ) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ m in atTop, ∀ j ∈ releaseRun k hk a b m,
      |(j : ℝ) / independenceNumberOfTree m (2 * k + 1) - locationFraction k (releaseParameter k hk)| < ε := by
  have hc := ((releaseCenter_location_tendsto k hk).sub_const (locationFraction k (releaseParameter k hk))).abs
  simp only [sub_self, abs_zero] at hc
  have ht := ((releaseScale_alpha_tendsto k hk).const_mul (|a| + |b|)).add hc
  simp only [mul_zero, zero_add] at ht
  filter_upwards [ht.eventually (gt_mem_nhds hε)] with m hm
  intro j hj
  exact (run_location_error k hk a b m hj).trans_lt hm

end SphericalTreeFailures
