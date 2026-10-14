import Dowling.FlatOrderIso

noncomputable section
namespace Dowling
open scoped Classical
variable {G : Type*} [Group G] [Fintype G] {n : ℕ}

omit [Fintype G] in
theorem discrete_admissible (X : Set (Fin n)) :
    Admissible X (GainPartition.discrete : GainPartition G n) := by
  intro i hi
  change some (i,(1:G)) = none at hi
  cases hi

def bottomConfiguration (X : Set (Fin n)) : Configuration G X :=
  ⟨GainPartition.discrete,discrete_admissible X⟩

instance (X : Set (Fin n)) : OrderBot (Configuration G X) where
  bot := bottomConfiguration X
  bot_le p := by
    change p.val.solutionSet ⊆ GainPartition.discrete.solutionSet
    rw [GainPartition.discrete_solutionSet]
    exact Set.subset_univ _

def topConfiguration (X : Set (Fin n)) : Configuration G X :=
  ⟨partitionOf (ground G n X), admissible_of_solutions X _ Set.Subset.rfl _ (partitionOf_solutionSet _)⟩

instance (X : Set (Fin n)) : OrderTop (Configuration G X) where
  top := topConfiguration X
  le_top p := by
    change (partitionOf (ground G n X)).solutionSet ⊆ p.val.solutionSet
    rw [partitionOf_solutionSet, ← flatEdges_solutions X p.val p.property]
    exact solutions_antitone (flatEdges_subset_ground X p.val)

instance (X : Set (Fin n)) : LocallyFiniteOrder (Configuration G X) := Fintype.toLocallyFiniteOrder

omit [Fintype G] in
theorem flatEdges_discrete (X : Set (Fin n)) :
    flatEdges X (GainPartition.discrete : GainPartition G n) = ∅ := by
  apply Set.eq_empty_iff_forall_notMem.mpr
  intro e he
  cases e with
  | inl i =>
    have h := ((flatEdges_joint X GainPartition.discrete i).mp he).2
    change some (i,(1:G)) = none at h
    cases h
  | inr e =>
    rcases (flatEdges_link X GainPartition.discrete e).mp he with ⟨hi,_⟩ | ⟨r,a,b,hi,hj,_⟩
    · change some (e.tail,(1:G)) = none at hi
      cases hi
    · change some (e.tail,(1:G)) = some (r,a) at hi
      change some (e.head,(1:G)) = some (r,b) at hj
      have h1 := congrArg Prod.fst (Option.some.inj hi)
      have h2 := congrArg Prod.fst (Option.some.inj hj)
      exact e.ordered.ne (h1.trans h2.symm)

theorem matroid_empty_isFlat (X : Set (Fin n)) : (matroid G n X).IsFlat ∅ := by
  rw [← flatEdges_discrete X]
  exact flatEdges_isFlat X _ (discrete_admissible X)

theorem configurationOrderIso_bot (X : Set (Fin n)) :
    configurationOrderIso X ⊥ = MatroidInverseZ.bottomFlat (matroid G n X) := by
  apply Subtype.ext
  change flatEdges X GainPartition.discrete = (matroid G n X).closure ∅
  rw [flatEdges_discrete, (matroid_empty_isFlat X).closure]

theorem configurationOrderIso_top (X : Set (Fin n)) :
    configurationOrderIso X ⊤ = MatroidInverseZ.topFlat (matroid G n X) := by
  apply Subtype.ext
  exact (flat_eq_flatEdges X _ (matroid G n X).ground_isFlat).symm

theorem configurationRank_bot (X : Set (Fin n)) : configurationRank X (⊥ : Configuration G X) = 0 := by
  rw [← configurationOrderIso_rank, configurationOrderIso_bot]
  change ((matroid G n X).eRk ((matroid G n X).closure ∅)).toNat = 0
  rw [Matroid.eRk_closure_eq, Matroid.eRk_empty]
  rfl

end Dowling
