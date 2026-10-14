import MainTheorems.Domination.PairConditioning

namespace ResearchMain.Domination

open Classical

theorem boundedSum_pair (a b : ℕ) (f : (Fin 2 → ℕ) → ℤ) :
    (∑ p ∈ boundedParts (twoBounds a b), f p) =
      ∑ x ∈ Finset.Icc 1 a, ∑ y ∈ Finset.Icc 1 b, f ![x, y] := by
  rw [← Finset.sum_product (Finset.Icc 1 a) (Finset.Icc 1 b)
    (fun p : ℕ × ℕ => f ![p.1, p.2])]
  symm
  apply Finset.sum_bij (fun p _ => ![p.1, p.2])
  · intro p hp
    obtain ⟨hx, hy⟩ := Finset.mem_product.mp hp
    apply (mem_boundedParts _ _).mpr
    intro i
    fin_cases i
    · exact Finset.mem_Icc.mp hx
    · exact Finset.mem_Icc.mp hy
  · intro p _ q _ heq
    apply Prod.ext
    · simpa using congrFun heq 0
    · simpa using congrFun heq 1
  · intro p hp
    have hb := (mem_boundedParts _ p).mp hp
    refine ⟨(p 0, p 1), ?_, ?_⟩
    · exact Finset.mem_product.mpr ⟨Finset.mem_Icc.mpr (hb 0), Finset.mem_Icc.mpr (hb 1)⟩
    · funext i
      fin_cases i <;> rfl
  · intro p _
    rfl

theorem pairDenominator_expanded {r : ℕ} (a b : ℕ) (bounds : Fin r → ℕ) (N : ℤ) :
    pairDenominator a b bounds N =
      ∑ x ∈ Finset.Icc 1 a, ∑ y ∈ Finset.Icc 1 b, compositionCountZ bounds (N - x - y) := by
  rw [pairDenominator_eq, compositionCountZ_concat, boundedSum_pair]
  apply Finset.sum_congr rfl
  intro x _
  apply Finset.sum_congr rfl
  intro y _
  rw [Fin.sum_univ_two]
  change compositionCountZ bounds (N - ((x + y : ℕ) : ℤ)) =
    compositionCountZ bounds (N - x - y)
  congr 1
  push_cast
  ring

theorem compositionCountZ_twoAppends {r : ℕ} (bounds : Fin r → ℕ) (a b : ℕ) (N : ℤ) :
    compositionCountZ (Fin.lastCases a (Fin.lastCases b bounds)) N =
      ∑ x ∈ Finset.Icc 1 a, ∑ y ∈ Finset.Icc 1 b, compositionCountZ bounds (N - x - y) := by
  rw [compositionCountZ_append]
  apply Finset.sum_congr rfl
  intro x _
  exact compositionCountZ_append bounds b (N - x)

theorem pairDenominator_twoAppends {r : ℕ} (a b : ℕ) (bounds : Fin r → ℕ) (N : ℤ) :
    pairDenominator a b bounds N =
      compositionCountZ (Fin.lastCases a (Fin.lastCases b bounds)) N := by
  rw [pairDenominator_expanded, compositionCountZ_twoAppends]

theorem compositionCountZ_appends_comm {r : ℕ} (bounds : Fin r → ℕ)
    (a b : ℕ) (N : ℤ) :
    compositionCountZ (Fin.lastCases a (Fin.lastCases b bounds)) N =
      compositionCountZ (Fin.lastCases b (Fin.lastCases a bounds)) N := by
  rw [compositionCountZ_twoAppends, compositionCountZ_twoAppends, Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro x _
  apply Finset.sum_congr rfl
  intro y _
  congr 1
  ring

end ResearchMain.Domination
