import SphericalTreeFailures.LocalLimitMultipliers
import SphericalTreeFailures.ReleaseLimitDecay
import SphericalTreeFailures.ReleaseFourierDecay

namespace SphericalTreeFailures
open MeasureTheory Filter Set
open scoped Topology

noncomputable def releaseFrequencyWindow (k : ℕ) (hk : 16384 ≤ k) (m : ℕ) : Set ℝ :=
  Icc (-(Real.pi * fluctuationScale (releaseParameter k hk) ^ m))
    (Real.pi * fluctuationScale (releaseParameter k hk) ^ m)

noncomputable def finiteLimitKernel (k : ℕ) (hk : 16384 ≤ k) (d : DifferenceKind) (m : ℕ) (t : ℝ) : ℂ :=
  (releaseFrequencyWindow k hk m).indicator
    (fun t => differenceMultiplier d (fluctuationScale (releaseParameter k hk) ^ m) t *
      finiteReleaseCharacteristic k hk m t) t

noncomputable def limitKernel (k : ℕ) (hk : 16384 ≤ k) (d : DifferenceKind) (m : ℕ) (t : ℝ) : ℂ :=
  limitMultiplier d t * releaseCharacteristic k hk ((-1 : ℝ) ^ m * t)

 theorem finiteReleaseCharacteristic_continuous (k : ℕ) (hk : 16384 ≤ k) (m : ℕ) :
    Continuous (finiteReleaseCharacteristic k hk m) := by
  unfold finiteReleaseCharacteristic centeredGraphCharacteristic totalCharacteristic
  apply Continuous.mul
  · unfold sizeExponential
    fun_prop
  · exact (polynomialCharacteristic_continuous _ _).comp (continuous_id.div_const _)

theorem finiteReleaseCharacteristic_norm_le (k : ℕ) (hk : 16384 ≤ k) (m : ℕ) (t : ℝ) :
    ‖finiteReleaseCharacteristic k hk m t‖ ≤ scaledEnvelope m k (releaseParameter k hk) t := by
  unfold finiteReleaseCharacteristic centeredGraphCharacteristic
  rw [norm_mul, sizeExponential_norm, one_mul]
  exact tuned_totalCharacteristic_norm_le k (releaseParameter_pos k hk)
    (releaseParameter_spec k hk).2.2 m _

theorem finiteLimitKernel_integrable (k : ℕ) (hk : 16384 ≤ k) (d : DifferenceKind) (m : ℕ) :
    Integrable (finiteLimitKernel k hk d m) := by
  apply (integrable_indicator_iff measurableSet_Icc).mpr
  exact ((differenceMultiplier_continuous d _).mul (finiteReleaseCharacteristic_continuous k hk m)).integrableOn_Icc

theorem limitKernel_measurable (k : ℕ) (hk : 16384 ≤ k) (d : DifferenceKind) (m : ℕ) :
    Measurable (limitKernel k hk d m) := by
  apply Measurable.mul
  · unfold limitMultiplier
    fun_prop
  · exact (releaseCharacteristic_continuous k hk).measurable.comp
      (measurable_const.mul measurable_id)

theorem releaseFrequencyWindow_eventual (k : ℕ) (hk : 16384 ≤ k) (t : ℝ) :
    ∀ᶠ m in atTop, t ∈ releaseFrequencyWindow k hk m := by
  have h := (tendsto_pow_atTop_atTop_of_one_lt (release_scale_gt_one k hk)).const_mul_atTop Real.pi_pos
  filter_upwards [h.eventually (eventually_ge_atTop |t|)] with m hm
  exact abs_le.mp hm

theorem finiteRelease_characteristic_error_tendsto (k : ℕ) (hk : 16384 ≤ k) (t : ℝ) :
    Tendsto (fun m => ‖finiteReleaseCharacteristic k hk m t -
      releaseCharacteristic k hk ((-1 : ℝ) ^ m * t)‖) atTop (𝓝 0) := by
  have ht := (rootErrorNorm_tendsto (releaseBroadcastParameter k hk) (releaseBroadcast_supercritical k hk)
    k (tunedActivity (releaseParameter k hk)) (tunedActivity_pos (releaseParameter_pos k hk))).const_mul |t|
  simp only [mul_zero] at ht
  exact squeeze_zero (fun _ => norm_nonneg _) (fun m => finiteRelease_characteristic_error k hk m t) ht

theorem localLimitKernel_pointwise (k : ℕ) (hk : 16384 ≤ k) (d : DifferenceKind) (t : ℝ) :
    Tendsto (fun m => finiteLimitKernel k hk d m t - limitKernel k hk d m t) atTop (𝓝 0) := by
  have h := multiplier_error_tendsto
    (differenceMultiplier_tendsto (release_scale_gt_one k hk) d t)
    (finiteRelease_characteristic_error_tendsto k hk t)
    (fun m => releaseCharacteristic_norm_le_one k hk ((-1 : ℝ) ^ m * t))
  apply h.congr'
  filter_upwards [releaseFrequencyWindow_eventual k hk t] with m hm
  simp only [finiteLimitKernel, limitKernel, indicator_of_mem hm]

end SphericalTreeFailures
