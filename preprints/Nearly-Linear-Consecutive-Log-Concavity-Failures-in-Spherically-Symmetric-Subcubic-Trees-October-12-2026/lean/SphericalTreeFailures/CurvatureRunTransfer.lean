import SphericalTreeFailures.IntegerRuns

namespace SphericalTreeFailures
open Filter
open scoped Topology

theorem releaseRun_probability_failures (k : ℕ) (hk : 16384 ≤ k)
    {a b δ : ℝ} (hδ : 0 < δ)
    (hcurv : ∀ x ∈ Set.Icc a b, δ ≤ releaseCurvature k hk x) :
    ∀ᶠ m in atTop, ∀ j ∈ releaseRun k hk a b m,
      releaseMass k hk m j ^ 2 < releaseMass k hk m (j - 1) * releaseMass k hk m (j + 1) := by
  filter_upwards [curvature_local_limit_uniform k hk hδ] with m hm
  intro j hj
  have hc := hcurv _ ((mem_releaseRun k hk a b m j).mp hj)
  have he := (abs_lt.mp (hm j)).1
  have hpos : 0 < releaseScale k hk m ^ 4 *
      (releaseMass k hk m (j - 1) * releaseMass k hk m (j + 1) - releaseMass k hk m j ^ 2) := by
    linarith
  have hdiff := (mul_pos_iff_of_pos_left (pow_pos (releaseScale_pos k hk m) 4)).mp hpos
  linarith

end SphericalTreeFailures
