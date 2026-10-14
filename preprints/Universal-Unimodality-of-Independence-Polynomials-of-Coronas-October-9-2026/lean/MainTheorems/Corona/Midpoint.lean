import MainTheorems.Corona.Windows
import Mathlib.Algebra.Order.Floor.Ring

namespace ResearchMain.Corona

noncomputable def midpointIndex (u v : ℝ) : ℕ := ⌊(u + v) / 2⌋₊

theorem midpoint_bounds {u v : ℝ} (hu : 0 ≤ u) (hv : 0 ≤ v) :
    (midpointIndex u v : ℝ) ≤ (u + v) / 2 ∧ (u + v) / 2 < midpointIndex u v + 1 :=
  ⟨Nat.floor_le (by linarith), Nat.lt_floor_add_one _⟩

theorem midpoint_distances {u v G : ℝ} (hu : 0 ≤ u) (hv : 0 ≤ v)
    (hG : 6 ≤ G) (hgap : G ≤ v - u) :
    G / 3 ≤ |(midpointIndex u v : ℝ) - u| ∧ G / 3 ≤ |(midpointIndex u v : ℝ) - v| := by
  have hk := midpoint_bounds hu hv
  have hleft : u ≤ (midpointIndex u v : ℝ) := by linarith
  have hright : (midpointIndex u v : ℝ) ≤ v := by linarith
  rw [abs_of_nonneg (sub_nonneg.mpr hleft), abs_of_nonpos (sub_nonpos.mpr hright)]
  constructor <;> linarith

theorem midpoint_between_windows {u v R G : ℝ} (hu : 0 ≤ u) (hv : 0 ≤ v)
    (hgap : G ≤ v - u) (hR : 2 * R + 2 < G) {j l : ℕ}
    (hj : |(j : ℝ) - u| ≤ R) (hl : |(l : ℝ) - v| ≤ R) :
    j < midpointIndex u v ∧ midpointIndex u v < l := by
  have hk := midpoint_bounds hu hv
  have hj' := (abs_le.mp hj).2
  have hl' := (abs_le.mp hl).1
  constructor
  · have h : (j : ℝ) < midpointIndex u v := by linarith
    exact_mod_cast h
  · have h : (midpointIndex u v : ℝ) < l := by linarith
    exact_mod_cast h

end ResearchMain.Corona
