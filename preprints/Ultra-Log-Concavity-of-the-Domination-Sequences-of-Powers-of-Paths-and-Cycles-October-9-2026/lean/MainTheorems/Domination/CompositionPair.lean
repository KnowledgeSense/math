import MainTheorems.Domination.CompositionMoments

namespace ResearchMain.Domination

open Classical

def twoBounds (a b : ℕ) : Fin 2 → ℕ := ![a, b]

theorem compositionCount_pair_below (a b N : ℕ) (hN : 1 ≤ N)
    (ha : N ≤ a) (hb : N ≤ b) :
    compositionCount (twoBounds a b) N = N - 1 := by
  unfold compositionCount
  calc
    ((boundedParts (twoBounds a b)).filter (fun p => ∑ i, p i = N)).card =
        (Finset.Icc 1 (N - 1)).card := by
      symm
      apply Finset.card_bij (fun x _ => ![x, N - x])
      · intro x hx
        obtain ⟨hxlo, hxhi⟩ := Finset.mem_Icc.mp hx
        apply Finset.mem_filter.mpr
        constructor
        · apply (mem_boundedParts _ _).mpr
          intro i
          fin_cases i
          · change 1 ≤ x ∧ x ≤ a
            omega
          · change 1 ≤ N - x ∧ N - x ≤ b
            omega
        · rw [Fin.sum_univ_two]
          change x + (N - x) = N
          omega
      · intro x _ y _ heq
        simpa using congrFun heq 0
      · intro p hp
        obtain ⟨hparts, hsum⟩ := Finset.mem_filter.mp hp
        have h0 := (mem_boundedParts _ p).mp hparts 0
        have h1 := (mem_boundedParts _ p).mp hparts 1
        simp only [Fin.sum_univ_two] at hsum
        refine ⟨p 0, Finset.mem_Icc.mpr ⟨h0.1, by omega⟩, ?_⟩
        funext i
        fin_cases i
        · rfl
        · change N - p 0 = p 1
          omega
    _ = N - 1 := by simp

theorem compositionCountZ_pair_below (a b N : ℕ) (hN : 1 ≤ N)
    (ha : N ≤ a) (hb : N ≤ b) :
    compositionCountZ (twoBounds a b) N = (N : ℤ) - 1 := by
  rw [compositionCountZ_nat, compositionCount_pair_below a b N hN ha hb]
  exact Nat.cast_sub hN

theorem compositionCountZ_pair_zero (a b : ℕ) (ha : 1 ≤ a) (hb : 1 ≤ b) :
    compositionCountZ (twoBounds a b) 0 = 0 := by
  apply compositionCountZ_zero
  · intro i
    fin_cases i
    · exact ha
    · exact hb
  · left
    norm_num

end ResearchMain.Domination
