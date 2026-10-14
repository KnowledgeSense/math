import SphericalTreeFailures.RootCharacteristicLimit
import SphericalTreeFailures.ScaledLatticeInversion
import SphericalTreeFailures.ReleaseParameters

namespace SphericalTreeFailures
open MeasureTheory ProbabilityTheory Filter
open scoped Topology

noncomputable def releaseCharacteristic (k : ℕ) (hk : 16384 ≤ k) (t : ℝ) : ℂ :=
  censusMixtureCharacteristic (releaseBroadcastParameter k hk) (tailShift k (releaseParameter k hk) * t)

noncomputable def finiteReleaseCharacteristic (k : ℕ) (hk : 16384 ≤ k) (m : ℕ) (t : ℝ) : ℂ :=
  centeredGraphCharacteristic m k (tunedActivity (releaseParameter k hk))
    (totalCenter (releaseBroadcastParameter k hk) k m (tunedActivity (releaseParameter k hk)))
    (fluctuationScale (releaseParameter k hk) ^ m) t

 theorem normalizedRootSample_characteristic (p : unitInterval) (k m : ℕ) {r : ℝ}
    (hr : 0 < r) (hp : (p : ℝ) = broadcastParameter r)
    (htune : tunedActivity r * pathPartition (2 * k) (tunedActivity r) =
      r * pathPartition (2 * k + 1) (tunedActivity r)) (t : ℝ) :
    (∫ ω, sizeExponential (normalizedRootSample p k m (tunedActivity r) ω) t
      ∂totalSizeMeasure p k (tunedActivity r) (tunedActivity_pos hr)) =
      centeredGraphCharacteristic m k (tunedActivity r) (totalCenter p k m (tunedActivity r))
        ((-censusScale p) ^ m) t := by
  unfold normalizedRootSample centeredGraphCharacteristic
  simp_rw [sizeExponential_scalar, sizeExponential_sub]
  rw [integral_const_mul]
  rw [show ((-censusScale p) ^ m)⁻¹ * t = t / (-censusScale p) ^ m by ring,
    rootSelected_characteristic_graph p k hr hp htune, ← totalCharacteristic_graph]

theorem scaledRootLimit_characteristic (p : unitInterval) (hc : 1 < 2 * (p : ℝ) ^ 2)
    (k : ℕ) (activity : ℝ) (ha : 0 < activity) (t : ℝ) :
    (∫ ω, sizeExponential (scaledRootLimit p k activity ω) t ∂totalSizeMeasure p k activity ha) =
      censusMixtureCharacteristic p
        ((tailMeanDifference k activity + censusScale p / (1 + censusScale p)) * t) := by
  unfold scaledRootLimit
  simp_rw [sizeExponential_scalar]
  have h := integral_fun_fst (μ := broadcastMeasure p) (ν := tailInputMeasure k activity ha)
    (fun ω => sizeExponential (rootMixtureLimit p ω)
      ((tailMeanDifference k activity + censusScale p / (1 + censusScale p)) * t))
  simp only [probReal_univ, one_smul] at h
  rw [show totalSizeMeasure p k activity ha = (broadcastMeasure p).prod
    (tailInputMeasure k activity ha) from rfl, h]
  rw [← charFun_map_sizeExponential _ (measurable_rootMixtureLimit p), (rootMixtureLimit_law p hc).map_eq]
  rfl

theorem signed_frequency_identity {γ : ℝ} (hγ : γ ≠ 0) (m : ℕ) (t : ℝ) :
    ((-1 : ℝ) ^ m * t) / (-γ) ^ m = t / γ ^ m := by
  apply (div_eq_div_iff (pow_ne_zero _ (neg_ne_zero.mpr hγ)) (pow_ne_zero _ hγ)).mpr
  rw [neg_pow]
  ring

theorem finiteRelease_characteristic_error (k : ℕ) (hk : 16384 ≤ k) (m : ℕ) (t : ℝ) :
    ‖finiteReleaseCharacteristic k hk m t - releaseCharacteristic k hk ((-1 : ℝ) ^ m * t)‖ ≤
      |t| * rootErrorNorm (releaseBroadcastParameter k hk) k m
        (tunedActivity (releaseParameter k hk)) (tunedActivity_pos (releaseParameter_pos k hk)) := by
  let p := releaseBroadcastParameter k hk
  let r := releaseParameter k hk
  have hp : 0 < (p : ℝ) := by
    have := (broadcastParameter_bounds hk (releaseParameter_spec k hk).1).2.1
    change 0 < broadcastParameter r
    dsimp [r]
    linarith
  have h := root_characteristic_error_bound p hp k m (tunedActivity r)
    (tunedActivity_pos (releaseParameter_pos k hk)) ((-1 : ℝ) ^ m * t)
  rw [normalizedRootSample_characteristic p k m (releaseParameter_pos k hk) rfl
    (releaseParameter_spec k hk).2.2, scaledRootLimit_characteristic p (releaseBroadcast_supercritical k hk)] at h
  have hg : censusScale p ≠ 0 := by unfold censusScale; positivity
  unfold centeredGraphCharacteristic at h
  rw [signed_frequency_identity hg] at h
  simpa only [abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul,
    finiteReleaseCharacteristic, releaseCharacteristic, centeredGraphCharacteristic, p, r,
    releaseBroadcastParameter, censusScale, fluctuationScale, tailShift, tailMeanDifference] using h

end SphericalTreeFailures
