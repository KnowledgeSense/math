import MeanMaximumForests.ForestRepresentation
import Mathlib.Combinatorics.SimpleGraph.Clique

namespace MeanMaximumForests
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

/-- Mean cardinality of a uniformly chosen independent set of a finite graph. -/
noncomputable def graphMean [Fintype V] : ℝ := meanIndependentSetSize G univ

/-- The full finite-graph statement furnished by a verified invariant cone. -/
theorem graphMean_lower_bound [Fintype V] {c : ℝ} {C : Bool → Set ConeVector}
    (hc : InvariantConditions c C) (hG : G.IsAcyclic) :
    c * G.indepNum ≤ graphMean G := by
  rw [graphMean, ← independenceNumber_univ G]
  exact finite_forest_mean_bound G hc hG univ

end MeanMaximumForests
