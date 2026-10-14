import Dowling.FlatRealization

noncomputable section
namespace Dowling
open scoped Classical
variable {G : Type*} [Group G] [Finite G] {n : ℕ}

theorem matroid_mem_closure (X : Set (Fin n)) (S : Set (Edge G n))
    (hS : S ⊆ ground G n X) (e : Edge G n) :
    e ∈ (matroid G n X).closure S ↔
      (∀ x ∈ solutions G n S, Satisfies G n x e) ∧ e ∈ ground G n X := by
  rw [matroid, Matroid.restrict_closure_eq _ hS (Set.subset_univ _),
    Set.mem_inter_iff, fullMatroid_mem_closure]

/-- Every admissible potential partition gives an actual flat of the retained-joint matroid. -/
theorem flatEdges_isFlat (X : Set (Fin n)) (p : GainPartition G n) (hp : Admissible X p) :
    (matroid G n X).IsFlat (flatEdges X p) := by
  apply Matroid.isFlat_iff_closure_eq.mpr
  ext e
  rw [matroid_mem_closure X _ (flatEdges_subset_ground X p) e, flatEdges_solutions X p hp]
  exact and_comm

theorem flat_eq_flatEdges (X : Set (Fin n)) (F : Set (Edge G n))
    (hF : (matroid G n X).IsFlat F) : F = flatEdges X (partitionOf F) := by
  ext e
  conv_lhs => rw [← hF.closure]
  rw [matroid_mem_closure X F hF.subset_ground e]
  change _ ↔ (e ∈ ground G n X ∧ ∀ x ∈ (partitionOf F).solutionSet, Satisfies G n x e)
  rw [partitionOf_solutionSet]
  exact and_comm

/-- Complete flat classification, with the zero-block admissibility proved in both directions. -/
theorem matroid_isFlat_iff (X : Set (Fin n)) (F : Set (Edge G n)) :
    (matroid G n X).IsFlat F ↔ ∃ p : GainPartition G n, Admissible X p ∧ F = flatEdges X p := by
  constructor
  · intro hF
    exact ⟨partitionOf F, admissible_of_solutions X F hF.subset_ground _ (partitionOf_solutionSet F),
      flat_eq_flatEdges X F hF⟩
  · rintro ⟨p,hp,rfl⟩
    exact flatEdges_isFlat X p hp

theorem flatEdges_eRk (X : Set (Fin n)) (p : GainPartition G n) (hp : Admissible X p) :
    (matroid G n X).eRk (flatEdges X p) = ((n-p.roots.card : ℕ) : ℕ∞) := by
  rw [matroid_eRk X _ (flatEdges_subset_ground X p),
    constraintRank_eq _ p (flatEdges_solutions X p hp).symm]

omit [Finite G] in
theorem flatEdges_injective (X : Set (Fin n)) (p q : GainPartition G n)
    (hp : Admissible X p) (hq : Admissible X q) (he : flatEdges X p = flatEdges X q) : p = q := by
  apply GainPartition.solutionSet_injective
  rw [← flatEdges_solutions X p hp, ← flatEdges_solutions X q hq, he]

end Dowling
