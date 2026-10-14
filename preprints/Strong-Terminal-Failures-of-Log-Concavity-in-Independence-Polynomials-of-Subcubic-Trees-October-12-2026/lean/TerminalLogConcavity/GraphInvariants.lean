import TerminalLogConcavity.GraphCounting
import Mathlib.Combinatorics.SimpleGraph.Clique

namespace TerminalLogConcavity
open Finset
variable {V : Type*} [DecidableEq V] (G : SimpleGraph V)

/-- Agreement with Mathlib's usual graph-theoretic independence predicate. -/
theorem independent_iff_isIndepSet (s : Finset V) :
    Independent G s ↔ G.IsIndepSet (s : Set V) := by
  rw [SimpleGraph.isIndepSet_iff]
  constructor
  · exact fun h _ hu _ hv _ => h _ hu _ hv
  · intro h u hu v hv
    by_cases he : u = v
    · subst v
      exact G.irrefl
    · exact h hu hv he

/-- The finite maximum used in the counting proof is the standard independence number. -/
theorem independenceNumber_univ [Fintype V] : independenceNumber G univ = G.indepNum := by
  apply le_antisymm
  · obtain ⟨s, _, hi, he⟩ := exists_maximum_independentSet G univ
    rw [← he]
    exact ((independent_iff_isIndepSet G s).mp hi).card_le_indepNum
  · obtain ⟨s, hs⟩ := G.exists_isNIndepSet_indepNum
    rw [← hs.card_eq]
    exact independent_card_le G univ (subset_univ _) ((independent_iff_isIndepSet G s).mpr hs.isIndepSet)

end TerminalLogConcavity
