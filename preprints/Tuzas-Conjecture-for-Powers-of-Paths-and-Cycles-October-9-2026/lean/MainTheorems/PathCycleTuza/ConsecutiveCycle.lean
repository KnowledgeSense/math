import MainTheorems.PathCycleTuza.RunCover
import MainTheorems.PathCycleTuza.PathPacking

set_option maxHeartbeats 2000000

namespace ResearchMain.PathCycleTuza

open Tuza

def cycleConsecutiveVertex (n : ℕ) (i : Fin (n / 2)) (d : Fin 3) : Fin n :=
  (![⟨2 * i.val, by have := i.isLt; omega⟩,
    ⟨2 * i.val + 1, by have := i.isLt; omega⟩,
    ⟨if 2 * i.val + 2 < n then 2 * i.val + 2 else 0, by
      have := i.isLt; split_ifs <;> omega⟩] d)

def cycleConsecutiveTriangle (n : ℕ) (i : Fin (n / 2)) : Finset (Fin n) :=
  {cycleConsecutiveVertex n i 0, cycleConsecutiveVertex n i 1, cycleConsecutiveVertex n i 2}

theorem cycleConsecutive_distinct (n : ℕ) (hn : 6 ≤ n) (i : Fin (n / 2)) :
    cycleConsecutiveVertex n i 0 ≠ cycleConsecutiveVertex n i 1 ∧
      cycleConsecutiveVertex n i 0 ≠ cycleConsecutiveVertex n i 2 ∧
      cycleConsecutiveVertex n i 1 ≠ cycleConsecutiveVertex n i 2 := by
  have hi := i.isLt
  dsimp [cycleConsecutiveVertex]
  split_ifs <;> simp only [Fin.mk.injEq] <;> omega

theorem cycleConsecutive_edges (n : ℕ) (hn : 6 ≤ n) (i : Fin (n / 2)) :
    triangleEdges (cycleConsecutiveTriangle n i) =
      {s(cycleConsecutiveVertex n i 0, cycleConsecutiveVertex n i 1),
        s(cycleConsecutiveVertex n i 0, cycleConsecutiveVertex n i 2),
        s(cycleConsecutiveVertex n i 1, cycleConsecutiveVertex n i 2)} := by
  have h := cycleConsecutive_distinct n hn i
  exact triangleEdges_triple h.1 h.2.1 h.2.2

def consecutiveCyclePacking (n : ℕ) (hn : 6 ≤ n) : PackingFamily (cyclePower n 2) (Fin (n / 2)) where
  triangle := cycleConsecutiveTriangle n
  clique i := by
    apply (cyclePower n 2).is3Clique_iff.mpr
    refine ⟨_, _, _, ?_, ?_, ?_, rfl⟩
    all_goals
      have hi := i.isLt
      change _ ≠ _ ∧ (Nat.dist _ _ ≤ 2 ∨ n - Nat.dist _ _ ≤ 2)
      dsimp [cycleConsecutiveVertex]
      try split_ifs
      all_goals simp only [Fin.mk.injEq]; unfold Nat.dist; omega
  disjoint i j hij := by
    apply Finset.disjoint_left.mpr
    intro e hei hej
    have hi := i.isLt
    have hj := j.isLt
    have hne : i.val ≠ j.val := (not_congr Fin.ext_iff).mp hij
    rw [cycleConsecutive_edges n hn] at hei hej
    simp only [Finset.mem_insert, Finset.mem_singleton] at hei
    rcases hei with rfl | rfl | rfl
    all_goals
      simp only [Finset.mem_insert, Finset.mem_singleton, Sym2.eq_iff, Fin.ext_iff] at hej
      dsimp [cycleConsecutiveVertex] at hej
      split_ifs at hej <;> (try simp only [and_false, false_and, false_or, or_false] at hej) <;> omega

theorem consecutiveCycle_bound (n : ℕ) (hn : 6 ≤ n) : n / 2 ≤ packingNumber (cyclePower n 2) := by
  simpa only [Fintype.card_fin] using (consecutiveCyclePacking n hn).number_bound

theorem cycle_two_inequality (n : ℕ) : Inequality (cyclePower n 2) := by
  by_cases hn : n ≤ 5
  · rw [cyclePower_complete n 2 (by omega)]
    exact complete_inequality n
  · have hp := consecutiveCycle_bound n (by omega)
    by_cases he : n % 2 = 0
    · have hc := cycle_run_cover n 2 (by decide) (by omega)
      norm_num at hc
      unfold Inequality
      omega
    · have hc := cycle_run_cover_even_odd n 2 (by decide) (by omega) (by decide) (by omega)
      norm_num at hc
      unfold Inequality
      omega

end ResearchMain.PathCycleTuza
