import SphericalTreeFailures.NormalizedCharacteristic
import SphericalTreeFailures.ReleaseParameters

namespace SphericalTreeFailures
open MeasureTheory ProbabilityTheory Filter
open scoped Topology

theorem release_scaledEnvelope_eq (k : ℕ) (hk : 16384 ≤ k) (m : ℕ) (t : ℝ) :
    scaledEnvelope m k (releaseParameter k hk) t =
      max ‖∫ ω, sizeExponential (normalizedSample (releaseBroadcastParameter k hk) k m
        (tunedActivity (releaseParameter k hk)) false ω) t
        ∂totalSizeMeasure (releaseBroadcastParameter k hk) k (tunedActivity (releaseParameter k hk))
          (tunedActivity_pos (releaseParameter_pos k hk))‖
      ‖∫ ω, sizeExponential (normalizedSample (releaseBroadcastParameter k hk) k m
        (tunedActivity (releaseParameter k hk)) true ω) t
        ∂totalSizeMeasure (releaseBroadcastParameter k hk) k (tunedActivity (releaseParameter k hk))
          (tunedActivity_pos (releaseParameter_pos k hk))‖ := by
  rw [normalizedSample_characteristic_norm, normalizedSample_characteristic_norm,
    sampledCharacteristic_signed_norm, sampledCharacteristic_signed_norm]
  obtain ⟨h0, h1⟩ := sampledCharacteristic_graph (releaseBroadcastParameter k hk) k
    (releaseParameter_pos k hk) rfl (releaseParameter_spec k hk).2.2 m
    (t / fluctuationScale (releaseParameter k hk) ^ m)
  change _ = max ‖sampledCharacteristic _ _ _ _ _ false (t / fluctuationScale (releaseParameter k hk) ^ m)‖
    ‖sampledCharacteristic _ _ _ _ _ true (t / fluctuationScale (releaseParameter k hk) ^ m)‖
  rw [h0, h1]
  rfl

theorem release_scaledEnvelope_uniform (k : ℕ) (hk : 16384 ≤ k) (R ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ m in atTop, ∀ t : ℝ, |t| ≤ R →
      |scaledEnvelope m k (releaseParameter k hk) t -
        censusEnvelope (releaseBroadcastParameter k hk) (tailShift k (releaseParameter k hk) * t)| < ε := by
  let p := releaseBroadcastParameter k hk
  let r := releaseParameter k hk
  have hr := releaseParameter_pos k hk
  have h0 := finite_characteristic_uniform_on_bounded p (releaseBroadcast_supercritical k hk)
    k (tunedActivity r) (tunedActivity_pos hr) false R ε hε
  have h1 := finite_characteristic_uniform_on_bounded p (releaseBroadcast_supercritical k hk)
    k (tunedActivity r) (tunedActivity_pos hr) true R ε hε
  filter_upwards [h0, h1] with m hm0 hm1
  intro t ht
  have he0 := hm0 t ht
  have he1 := hm1 t ht
  rw [scaledCensusLimit_characteristic] at he0 he1
  change ‖_ - censusCharacteristic p false (tailShift k r * t)‖ < ε at he0
  change ‖_ - censusCharacteristic p true (tailShift k r * t)‖ < ε at he1
  rw [release_scaledEnvelope_eq]
  unfold censusEnvelope
  exact (abs_max_sub_max_le_max _ _ _ _).trans_lt
    (max_lt ((abs_norm_sub_norm_le _ _).trans_lt he0) ((abs_norm_sub_norm_le _ _).trans_lt he1))

end SphericalTreeFailures
