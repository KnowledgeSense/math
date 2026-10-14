import MainTheorems.Tuza.CoChain
import Mathlib.Data.Fin.Tuple.Basic

namespace ResearchMain.Tuza

def rowTuples : (a : ℕ) → ℕ → List (Fin a → ℕ)
  | 0, _ => [Fin.elim0]
  | a + 1, b => (List.range (b + 1)).flatMap fun k =>
      (rowTuples a k).map (Fin.cons k)

theorem mem_rowTuples {a b : ℕ} (f : Fin a → ℕ)
    (hbound : ∀ i, f i ≤ b) (hanti : Antitone f) : f ∈ rowTuples a b := by
  induction a generalizing b with
  | zero =>
    have he : f = Fin.elim0 := by funext i; exact Fin.elim0 i
    simp [rowTuples, he]
  | succ a ih =>
    apply List.mem_flatMap.mpr
    refine ⟨f 0, List.mem_range.mpr (Nat.lt_succ_of_le (hbound 0)), ?_⟩
    apply List.mem_map.mpr
    refine ⟨Fin.tail f, ih (Fin.tail f) ?_ ?_, ?_⟩
    · intro i
      exact hanti (Fin.zero_le _)
    · intro i j hij
      exact hanti (Fin.succ_le_succ_iff.mpr hij)
    · exact Fin.cons_self_tail f

end ResearchMain.Tuza
