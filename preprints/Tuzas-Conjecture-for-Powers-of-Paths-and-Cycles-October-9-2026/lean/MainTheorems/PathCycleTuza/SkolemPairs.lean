import Mathlib.Tactic

set_option maxRecDepth 4096

namespace ResearchMain.PathCycleTuza

def skolemEndpoint (lower : ℕ → ℕ) (i : ℕ) (slot : Bool) : ℕ :=
  lower i + if slot then i else 0

def ordinaryFourLower (t i : ℕ) : ℕ :=
  if i % 2 = 0 then 2 * t + 1 - i / 2
  else if i = 1 then 7 * t
  else if i = 4 * t - 1 then 2 * t + 1
  else if i = 2 * t - 1 then 4 * t + 2
  else if 2 * t + 1 ≤ i then 5 * t + 1 - (i - (2 * t + 1)) / 2
  else 5 * t + 2 + (2 * t - 3 - i) / 2

theorem ordinaryFour_positive (t i : ℕ) (ht : 2 ≤ t) (hi : 1 ≤ i) (hib : i ≤ 4 * t) :
    1 ≤ ordinaryFourLower t i := by
  unfold ordinaryFourLower
  split_ifs <;> omega

theorem ordinaryFour_bounded (t i : ℕ) (slot : Bool)
    (ht : 2 ≤ t) (hi : 1 ≤ i) (hib : i ≤ 4 * t) :
    skolemEndpoint (ordinaryFourLower t) i slot ≤ 8 * t := by
  cases slot <;> simp only [skolemEndpoint, Bool.false_eq_true, ite_false, ite_true, add_zero]
  all_goals unfold ordinaryFourLower; split_ifs <;> omega

set_option maxHeartbeats 2000000 in
theorem ordinaryFour_injective (t i j : ℕ) (u v : Bool)
    (ht : 2 ≤ t) (hi : 1 ≤ i) (hib : i ≤ 4 * t) (hj : 1 ≤ j) (hjb : j ≤ 4 * t)
    (h : skolemEndpoint (ordinaryFourLower t) i u = skolemEndpoint (ordinaryFourLower t) j v) :
    i = j ∧ u = v := by
  cases u <;> cases v
  all_goals first | refine ⟨?_, rfl⟩ | exfalso
  all_goals
    simp [skolemEndpoint] at h
    unfold ordinaryFourLower at h
    split_ifs at h <;> omega

end ResearchMain.PathCycleTuza
