import MainTheorems.PathCycleTuza.SkolemPairs

set_option maxRecDepth 4096

namespace ResearchMain.PathCycleTuza

def ordinaryOddLower (t i : ℕ) : ℕ :=
  if i % 2 = 0 then 2 * t + 1 - i / 2
  else if i = 4 * t + 1 then 2 * t + 1
  else if 2 * t + 1 ≤ i then 5 * t + 2 - (i - (2 * t - 1)) / 2
  else if i = 2 * t - 1 then 6 * t + 3
  else if i = 1 then 5 * t + 2
  else 6 * t + 2 - (i - 1) / 2

theorem ordinaryOdd_positive (t i : ℕ) (ht : 2 ≤ t) (hi : 1 ≤ i) (hib : i ≤ 4 * t + 1) :
    1 ≤ ordinaryOddLower t i := by
  unfold ordinaryOddLower
  split_ifs <;> omega

theorem ordinaryOdd_bounded (t i : ℕ) (slot : Bool)
    (ht : 2 ≤ t) (hi : 1 ≤ i) (hib : i ≤ 4 * t + 1) :
    skolemEndpoint (ordinaryOddLower t) i slot ≤ 8 * t + 2 := by
  cases slot <;> simp only [skolemEndpoint, Bool.false_eq_true, ite_false, ite_true, add_zero]
  all_goals unfold ordinaryOddLower; split_ifs <;> omega

set_option maxHeartbeats 2000000 in
theorem ordinaryOdd_injective (t i j : ℕ) (u v : Bool)
    (ht : 2 ≤ t) (hi : 1 ≤ i) (hib : i ≤ 4 * t + 1) (hj : 1 ≤ j) (hjb : j ≤ 4 * t + 1)
    (h : skolemEndpoint (ordinaryOddLower t) i u = skolemEndpoint (ordinaryOddLower t) j v) :
    i = j ∧ u = v := by
  cases u <;> cases v
  all_goals first | refine ⟨?_, rfl⟩ | exfalso
  all_goals
    simp [skolemEndpoint] at h
    unfold ordinaryOddLower at h
    split_ifs at h <;> omega

end ResearchMain.PathCycleTuza
