import MainTheorems.Tuza.CompletePacking
import MainTheorems.Tuza.FactorCard

namespace ResearchMain.Tuza

theorem choose_two_real (n : ℕ) : 2 * (n.choose 2 : ℝ) = (n : ℝ) * ((n : ℝ) - 1) := by
  exact_mod_cast choose_two_integer n

theorem complete_count_real_bound (n : ℕ) :
    (n : ℝ) * ((n : ℝ) - 2) - 3 ≤ 6 * (completeCount n : ℝ) := by
  exact_mod_cast complete_count_bound n

theorem fan_count_real_lower (c q : ℕ) (hq : 0 < q) :
    ((q : ℝ) - 1) * min (c : ℝ) (q : ℝ) ≤ 2 * (fanCount c q : ℝ) := by
  have h : ((q - 1 : ℕ) : ℝ) * ((min c q : ℕ) : ℝ) ≤ 2 * (fanCount c q : ℝ) := by
    exact_mod_cast fanCount_lower c q
  rw [Nat.cast_sub hq, Nat.cast_one, Nat.cast_min] at h
  exact h

theorem adjacent_choose_difference (r s : ℕ) (hr : 0 < r) (hsr : s ≤ r) (hrs : r ≤ s + 1) :
    (r.choose 2 : ℝ) - (s.choose 2 : ℝ) ≤ (r : ℝ) - 1 := by
  have hcases : s = r ∨ s + 1 = r := by omega
  rcases hcases with h | h
  · rw [h]
    have hr' : (1 : ℝ) ≤ r := by exact_mod_cast hr
    linarith
  · have er := choose_two_real r
    have es := choose_two_real s
    have h' : (s : ℝ) + 1 = r := by exact_mod_cast h
    nlinarith

theorem balanced_fan_difference (r s t u : ℕ) (hr : 0 < r) (ht : 0 < t)
    (hsr : s ≤ r) (hrs : r ≤ s + 1) (hut : u ≤ t) (htu : t ≤ u + 1) :
    -((r : ℝ) + t - 2) ≤
      2 * ((fanCount r s : ℝ) + fanCount t u) -
        ((r.choose 2 : ℝ) + s.choose 2 + t.choose 2 + u.choose 2) := by
  rw [fanCount_saturated hsr, fanCount_saturated hut]
  have h₁ := adjacent_choose_difference r s hr hsr hrs
  have h₂ := adjacent_choose_difference t u ht hut htu
  linarith

end ResearchMain.Tuza
