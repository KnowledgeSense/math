import SphericalTreeFailures.CurvatureRunTransfer
import SphericalTreeFailures.RunInteriority

namespace SphericalTreeFailures
open Filter
open scoped Topology

theorem releaseMass_failure_coefficients (k : ℕ) (hk : 16384 ≤ k) (m : ℕ) {j : ℤ} (hj : 0 < j)
    (h : releaseMass k hk m j ^ 2 < releaseMass k hk m (j - 1) * releaseMass k hk m (j + 1)) :
    coefficient m (2 * k + 1) j.toNat ^ 2 <
      coefficient m (2 * k + 1) (j.toNat - 1) * coefficient m (2 * k + 1) (j.toNat + 1) := by
  lift j to ℕ using hj.le
  cases j with
  | zero => simp at hj
  | succ n =>
    have he1 : ((n + 1 : ℕ) : ℤ) - 1 = (n : ℤ) := by omega
    have he2 : ((n + 1 : ℕ) : ℤ) + 1 = ((n + 2 : ℕ) : ℤ) := by omega
    unfold releaseMass at h
    rw [he1, he2, graphLatticeMass_nat, graphLatticeMass_nat, graphLatticeMass_nat] at h
    have hc := (tilting_preserves_failure m (2 * k + 1) n
      (tunedActivity_pos (releaseParameter_pos k hk))).mp h
    simpa only [Int.toNat_natCast, Nat.add_sub_cancel, Nat.add_assoc, Nat.reduceAdd] using hc

theorem releaseRun_coefficient_failures (k : ℕ) (hk : 16384 ≤ k)
    {a b δ : ℝ} (hδ : 0 < δ)
    (hcurv : ∀ x ∈ Set.Icc a b, δ ≤ releaseCurvature k hk x) :
    ∀ᶠ m in atTop, ∀ j ∈ releaseRun k hk a b m,
      0 < j ∧ j < independenceNumberOfTree m (2 * k + 1) ∧
      coefficient m (2 * k + 1) j.toNat ^ 2 <
        coefficient m (2 * k + 1) (j.toNat - 1) * coefficient m (2 * k + 1) (j.toNat + 1) := by
  filter_upwards [releaseRun_probability_failures k hk hδ hcurv, releaseRun_interior k hk a b] with m hf hi
  intro j hj
  have hb := hi j hj
  have hc := (interiorFraction_location_bounds k hk).1
  have hα : (0 : ℝ) < independenceNumberOfTree m (2 * k + 1) := by
    exact_mod_cast independenceNumberOfTree_pos m k
  have hj0 : (0 : ℝ) < j := (mul_pos hc hα).trans_le hb.1
  have hjα : (j : ℝ) < independenceNumberOfTree m (2 * k + 1) := by nlinarith [mul_pos hc hα]
  have hj0' : (0 : ℤ) < j := by exact_mod_cast hj0
  exact ⟨hj0', by exact_mod_cast hjα, releaseMass_failure_coefficients k hk m hj0' (hf j hj)⟩

end SphericalTreeFailures
