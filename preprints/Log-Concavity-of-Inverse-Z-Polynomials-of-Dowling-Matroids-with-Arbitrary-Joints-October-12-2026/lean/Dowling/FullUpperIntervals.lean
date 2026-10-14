import Dowling.PartitionCompositionRank
import Dowling.InvariantBounds

noncomputable section
namespace Dowling
open scoped Classical
variable {G : Type*} [Group G] [Fintype G] {n : ℕ}

def fullUpperEmbedding (p : GainPartition G n) :
    Configuration G (Set.univ : Set (Fin p.roots.card)) ↪o
      Configuration G (Set.univ : Set (Fin n)) where
  toFun q := ⟨p.compose q.val,admissible_univ _⟩
  inj' := by
    intro q r h
    apply Subtype.ext
    apply le_antisymm
    · apply (p.compose_le_compose_iff _ _).mp
      exact (congrArg Subtype.val h).le
    · apply (p.compose_le_compose_iff _ _).mp
      exact (congrArg Subtype.val h).ge
  map_rel_iff' := p.compose_le_compose_iff _ _

omit [Fintype G] in
theorem fullUpperEmbedding_range (p : GainPartition G n)
    (y : Configuration G (Set.univ : Set (Fin n))) (hy : p ≤ y.val) :
    ∃ x, fullUpperEmbedding p x = y := by
  refine ⟨⟨p.compress y.val hy,admissible_univ _⟩,?_⟩
  exact Subtype.ext (p.compose_compress y.val hy)

omit [Fintype G] in
theorem fullUpperEmbedding_interval (p : GainPartition G n) :
    ∀ a b y, fullUpperEmbedding p a ≤ y → y ≤ fullUpperEmbedding p b →
      ∃ x, fullUpperEmbedding p x = y := by
  intro a _ y hay _
  apply fullUpperEmbedding_range
  exact (show p ≤ (fullUpperEmbedding p a).val from p.compose_solution_subset a.val).trans hay

theorem fullUpperEmbedding_rank (p : GainPartition G n)
    (a b : Configuration G (Set.univ : Set (Fin p.roots.card))) :
    configurationRank Set.univ (fullUpperEmbedding p b) -
      configurationRank Set.univ (fullUpperEmbedding p a) =
      configurationRank Set.univ b - configurationRank Set.univ a :=
  p.compose_rank_difference a.val b.val

omit [Fintype G] in
theorem fullUpperEmbedding_bot (p : GainPartition G n) :
    fullUpperEmbedding p ⊥ = ⟨p,admissible_univ p⟩ := by
  apply Subtype.ext
  apply GainPartition.solutionSet_injective
  ext x
  change x ∈ (p.compose GainPartition.discrete).solutionSet ↔ x ∈ p.solutionSet
  rw [p.mem_compose_solutionSet,GainPartition.discrete_solutionSet]
  simp only [Set.mem_univ, and_true]

theorem fullUpperEmbedding_top (p : GainPartition G n) : fullUpperEmbedding p ⊤ = ⊤ := by
  apply le_antisymm le_top
  have hp : p ≤ (⊤ : Configuration G (Set.univ : Set (Fin n))).val := by
    let q : Configuration G (Set.univ : Set (Fin n)) := ⟨p,admissible_univ p⟩
    have h : q ≤ ⊤ := le_top
    exact h
  obtain ⟨q,hq⟩ := fullUpperEmbedding_range p ⊤ hp
  rw [← hq]
  exact (fullUpperEmbedding p).monotone le_top

/-- The contraction above each genuine full-Dowling flat is the full Dowling
interval on its balanced components. -/
theorem full_upper_kl (p : Configuration G (Set.univ : Set (Fin n))) :
    MatroidInverseZ.kl (configurationRank Set.univ) (⊤ : Configuration G Set.univ) p =
      fullP G p.val.roots.card := by
  have h := MatroidInverseZ.kl_interval_transport (fullUpperEmbedding p.val)
    (fullUpperEmbedding_interval p.val) (configurationRank Set.univ) (configurationRank Set.univ)
    (fullUpperEmbedding_rank p.val) ⊥ ⊤
  rw [fullUpperEmbedding_bot,fullUpperEmbedding_top] at h
  exact h

theorem full_upper_inverseZ (p : Configuration G (Set.univ : Set (Fin n))) :
    MatroidInverseZ.inverseZ (configurationRank Set.univ) p (⊤ : Configuration G Set.univ) =
      fullY G p.val.roots.card := by
  have h := MatroidInverseZ.inverseZ_interval_transport (fullUpperEmbedding p.val)
    (fullUpperEmbedding_interval p.val) (configurationRank Set.univ) (configurationRank Set.univ)
    (fullUpperEmbedding_rank p.val) ⊥ ⊤
  rw [fullUpperEmbedding_bot,fullUpperEmbedding_top] at h
  exact h

end Dowling
