import SphericalTreeFailures.RunLocation

namespace SphericalTreeFailures
open Filter
open scoped Topology

noncomputable def interiorFraction (k : ℕ) : ℝ := 1 / (6 * (2 * k + 1) + 14)

theorem independenceNumberOfTree_pos (m k : ℕ) : 0 < independenceNumberOfTree m (2 * k + 1) := by
  have h := independenceNumber_identity m k
  have hp : 1 ≤ 2 ^ m := Nat.one_le_pow m 2 (by decide)
  have hb : (if m % 2 = 0 then 2 else 1 : ℕ) ≤ 2 := by split_ifs <;> omega
  nlinarith

theorem interiorFraction_location_bounds (k : ℕ) (hk : 16384 ≤ k) :
    0 < interiorFraction k ∧ interiorFraction k < locationFraction k (releaseParameter k hk) ∧
      locationFraction k (releaseParameter k hk) < 1 - interiorFraction k := by
  have hq := release_location_bounds k hk
  have hc : 0 < interiorFraction k := by unfold interiorFraction; positivity
  have hcsmall : interiorFraction k < 99 / 100 := by
    unfold interiorFraction
    apply (div_lt_iff₀ (by positivity)).mpr
    have hk0 : (0 : ℝ) ≤ k := by positivity
    nlinarith
  have hd : 0 < 3 * ((2 : ℝ) * k + 1) + 7 := by positivity
  have he : 1 / (3 * ((2 : ℝ) * k + 1) + 7) = 2 * interiorFraction k := by
    unfold interiorFraction
    field_simp
    ring
  rw [he] at hq
  exact ⟨hc, hcsmall.trans hq.1, by linarith [hq.2]⟩

theorem releaseRun_interior (k : ℕ) (hk : 16384 ≤ k) (a b : ℝ) :
    ∀ᶠ m in atTop, ∀ j ∈ releaseRun k hk a b m,
      interiorFraction k * independenceNumberOfTree m (2 * k + 1) ≤ (j : ℝ) ∧
      (j : ℝ) ≤ (1 - interiorFraction k) * independenceNumberOfTree m (2 * k + 1) := by
  obtain ⟨hc, hq0, hq1⟩ := interiorFraction_location_bounds k hk
  let q := locationFraction k (releaseParameter k hk)
  let ε := min (q - interiorFraction k) (1 - interiorFraction k - q)
  have hε : 0 < ε := lt_min (sub_pos.mpr hq0) (sub_pos.mpr hq1)
  filter_upwards [releaseRun_location_uniform k hk a b hε] with m hm
  intro j hj
  have h := abs_lt.mp (hm j hj)
  have hα : (0 : ℝ) < independenceNumberOfTree m (2 * k + 1) := by
    exact_mod_cast independenceNumberOfTree_pos m k
  have h0 : interiorFraction k ≤ (j : ℝ) / independenceNumberOfTree m (2 * k + 1) := by
    have he : ε ≤ q - interiorFraction k := min_le_left _ _
    dsimp [q] at he
    linarith [h.1]
  have h1 : (j : ℝ) / independenceNumberOfTree m (2 * k + 1) ≤ 1 - interiorFraction k := by
    have he : ε ≤ 1 - interiorFraction k - q := min_le_right _ _
    dsimp [q] at he
    linarith [h.2]
  exact ⟨(le_div_iff₀ hα).mp h0, (div_le_iff₀ hα).mp h1⟩

end SphericalTreeFailures
