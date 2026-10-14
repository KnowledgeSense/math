import SphericalTreeFailures.TuningExistence
import SphericalTreeFailures.TotalLimit

namespace SphericalTreeFailures

noncomputable def releaseParameter (k : ℕ) (hk : 16384 ≤ k) : ℝ :=
  Classical.choose (exists_tuning_parameter hk)

theorem releaseParameter_spec (k : ℕ) (hk : 16384 ≤ k) :
    (k : ℝ) / 2 < releaseParameter k hk ∧ releaseParameter k hk < 2 * k ∧
      tunedActivity (releaseParameter k hk) * pathPartition (2 * k) (tunedActivity (releaseParameter k hk)) =
        releaseParameter k hk * pathPartition (2 * k + 1) (tunedActivity (releaseParameter k hk)) :=
  Classical.choose_spec (exists_tuning_parameter hk)

theorem releaseParameter_pos (k : ℕ) (hk : 16384 ≤ k) : 0 < releaseParameter k hk := by
  have h := (releaseParameter_spec k hk).1
  have hk' : (16384 : ℝ) ≤ k := by exact_mod_cast hk
  linarith

noncomputable def releaseBroadcastParameter (k : ℕ) (hk : 16384 ≤ k) : unitInterval :=
  ⟨broadcastParameter (releaseParameter k hk), by
    obtain ⟨_, h0, h1⟩ := broadcastParameter_bounds hk (releaseParameter_spec k hk).1
    constructor <;> linarith⟩

theorem releaseBroadcast_supercritical (k : ℕ) (hk : 16384 ≤ k) :
    1 < 2 * (releaseBroadcastParameter k hk : ℝ) ^ 2 := by
  have h := (broadcastParameter_bounds hk (releaseParameter_spec k hk).1).2.1
  change 1 < 2 * broadcastParameter (releaseParameter k hk) ^ 2
  nlinarith

theorem release_location_bounds (k : ℕ) (hk : 16384 ≤ k) :
    99 / 100 < locationFraction k (releaseParameter k hk) ∧
      locationFraction k (releaseParameter k hk) < 1 - 1 / (3 * ((2 : ℝ) * k + 1) + 7) := by
  rw [show 3 * ((2 : ℝ) * k + 1) + 7 = 6 * k + 10 by ring]
  exact locationFraction_bounds hk (releaseParameter_spec k hk).1

theorem release_shift_negative (k : ℕ) (hk : 16384 ≤ k) :
    tailShift k (releaseParameter k hk) < -1 / 4 :=
  tuned_tailShift_negative hk (releaseParameter_spec k hk).1

end SphericalTreeFailures
