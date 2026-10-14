import MainTheorems.PathCycleTuza.SkolemPairs

set_option maxRecDepth 4096

namespace ResearchMain.PathCycleTuza

def hookedOddLower (t i : ℕ) : ℕ :=
  if i % 2 = 0 then 2 * t + 2 - i / 2
  else if i = 1 then 5 * t + 4
  else if i < 2 * t + 1 then 6 * t + 5 - (i - 1) / 2
  else if i = 2 * t + 1 then 6 * t + 6
  else if i = 4 * t + 3 then 2 * t + 2
  else 5 * t + 4 - (i - (2 * t + 1)) / 2

theorem hookedOdd_positive (t i : ℕ) (ht : 1 ≤ t) (hi : 1 ≤ i) (hib : i ≤ 4 * t + 3) :
    1 ≤ hookedOddLower t i := by
  unfold hookedOddLower
  split_ifs <;> omega

theorem hookedOdd_bounded (t i : ℕ) (slot : Bool)
    (ht : 1 ≤ t) (hi : 1 ≤ i) (hib : i ≤ 4 * t + 3) :
    skolemEndpoint (hookedOddLower t) i slot ≤ 8 * t + 7 := by
  cases slot <;> simp only [skolemEndpoint, Bool.false_eq_true, ite_false, ite_true, add_zero]
  all_goals unfold hookedOddLower; split_ifs <;> omega

theorem hookedOdd_omits (t i : ℕ) (slot : Bool)
    (ht : 1 ≤ t) (hi : 1 ≤ i) (hib : i ≤ 4 * t + 3) :
    skolemEndpoint (hookedOddLower t) i slot ≠ 8 * t + 6 := by
  cases slot <;> simp only [skolemEndpoint, Bool.false_eq_true, ite_false, ite_true, add_zero]
  all_goals unfold hookedOddLower; split_ifs <;> omega

set_option maxHeartbeats 2000000 in
theorem hookedOdd_injective (t i j : ℕ) (u v : Bool)
    (ht : 1 ≤ t) (hi : 1 ≤ i) (hib : i ≤ 4 * t + 3) (hj : 1 ≤ j) (hjb : j ≤ 4 * t + 3)
    (h : skolemEndpoint (hookedOddLower t) i u = skolemEndpoint (hookedOddLower t) j v) :
    i = j ∧ u = v := by
  cases u <;> cases v
  all_goals first | refine ⟨?_, rfl⟩ | exfalso
  all_goals
    simp [skolemEndpoint] at h
    unfold hookedOddLower at h
    split_ifs at h <;> omega

end ResearchMain.PathCycleTuza
