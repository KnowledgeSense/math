import MainTheorems.PathCycleTuza.SkolemPairs

set_option maxRecDepth 4096

namespace ResearchMain.PathCycleTuza

def hookedEvenLower (t i : ℕ) : ℕ :=
  if i % 2 = 0 then 2 * t + 2 - i / 2
  else if i = 1 then 7 * t + 4
  else if i ≤ 2 * t + 1 then 6 * t + 2 - (i - 1) / 2
  else if i = 2 * t + 3 then 6 * t + 2
  else if i = 4 * t + 1 then 2 * t + 2
  else 5 * t + 2 - (i - (2 * t + 3)) / 2

theorem hookedEven_positive (t i : ℕ) (ht : 2 ≤ t) (hi : 1 ≤ i) (hib : i ≤ 4 * t + 2) :
    1 ≤ hookedEvenLower t i := by
  unfold hookedEvenLower
  split_ifs <;> omega

theorem hookedEven_bounded (t i : ℕ) (slot : Bool)
    (ht : 2 ≤ t) (hi : 1 ≤ i) (hib : i ≤ 4 * t + 2) :
    skolemEndpoint (hookedEvenLower t) i slot ≤ 8 * t + 5 := by
  cases slot <;> simp only [skolemEndpoint, Bool.false_eq_true, ite_false, ite_true, add_zero]
  all_goals unfold hookedEvenLower; split_ifs <;> omega

theorem hookedEven_omits (t i : ℕ) (slot : Bool)
    (ht : 2 ≤ t) (hi : 1 ≤ i) (hib : i ≤ 4 * t + 2) :
    skolemEndpoint (hookedEvenLower t) i slot ≠ 8 * t + 4 := by
  cases slot <;> simp only [skolemEndpoint, Bool.false_eq_true, ite_false, ite_true, add_zero]
  all_goals unfold hookedEvenLower; split_ifs <;> omega

set_option maxHeartbeats 2000000 in
theorem hookedEven_injective (t i j : ℕ) (u v : Bool)
    (ht : 2 ≤ t) (hi : 1 ≤ i) (hib : i ≤ 4 * t + 2) (hj : 1 ≤ j) (hjb : j ≤ 4 * t + 2)
    (h : skolemEndpoint (hookedEvenLower t) i u = skolemEndpoint (hookedEvenLower t) j v) :
    i = j ∧ u = v := by
  cases u <;> cases v
  all_goals first | refine ⟨?_, rfl⟩ | exfalso
  all_goals
    simp [skolemEndpoint] at h
    unfold hookedEvenLower at h
    split_ifs at h <;> omega

end ResearchMain.PathCycleTuza
