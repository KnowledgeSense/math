import MainTheorems.PathCycleTuza.RunGeometry

namespace ResearchMain.PathCycleTuza.CircularRuns

variable {n k : ℕ} (D : CircularRuns n k)

def previous (i : Fin D.count) : Fin D.count := D.index (i.val + D.count - 1)

def next (i : Fin D.count) : Fin D.count := D.index (i.val + 1)

theorem previous_middle (i : Fin D.count) : D.previous (D.next i) = i := by
  apply Fin.ext
  have hc := D.count_four
  have hi := i.isLt
  change (((i.val + 1) % D.count + D.count - 1) % D.count) = i.val
  by_cases h : i.val + 1 < D.count
  · rw [Nat.mod_eq_of_lt h]
    rw [show i.val + 1 + D.count - 1 = i.val + D.count by omega,
      Nat.add_mod_right, Nat.mod_eq_of_lt hi]
  · have he : i.val + 1 = D.count := by omega
    rw [he, Nat.mod_self, Nat.zero_add, Nat.mod_eq_of_lt (by omega)]
    omega

theorem next_middle (i : Fin D.count) : D.next (D.next i) = D.index (i.val + 2) := by
  apply Fin.ext
  change (((i.val + 1) % D.count + 1) % D.count) = (i.val + 2) % D.count
  by_cases h : i.val + 1 < D.count
  · rw [Nat.mod_eq_of_lt h]
  · have he : i.val + 1 = D.count := by have := i.isLt; omega
    rw [he, Nat.mod_self, Nat.zero_add,
      show i.val + 2 = D.count + 1 by omega, Nat.add_mod_left]

theorem index_pair (i j : Fin D.count)
    (h : j.val = i.val + 2 ∨ j.val + D.count = i.val + 2) :
    D.next (D.next i) = j := by
  rw [D.next_middle]
  apply Fin.ext
  change (i.val + 2) % D.count = j.val
  rcases h with h | h
  · rw [← h, Nat.mod_eq_of_lt j.isLt]
  · rw [← h, Nat.add_mod_right, Nat.mod_eq_of_lt j.isLt]

theorem crossCapacity (i : Fin D.count) :
    k - D.length i ≤ D.length (D.previous i) ∧ k - D.length i ≤ D.length (D.next i) := by
  have h₀ := D.lower i
  have h₁ := D.lower (D.previous i)
  have h₂ := D.lower (D.next i)
  have hs : k ≤ 2 * Tuza.halfUp k := by unfold Tuza.halfUp; omega
  omega

end ResearchMain.PathCycleTuza.CircularRuns
