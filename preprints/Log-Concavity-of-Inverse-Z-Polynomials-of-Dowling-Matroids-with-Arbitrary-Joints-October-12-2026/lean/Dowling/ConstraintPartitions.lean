import Dowling.GainPartitionImpose
import Dowling.GroundFinite

noncomputable section
namespace Dowling
open scoped Classical
variable {G : Type*} [Group G] {n : ℕ}

@[simp] theorem solutions_empty : solutions G n ∅ = Set.univ := by
  ext x
  simp [solutions]

theorem solutions_insert (S : Set (Edge G n)) (e : Edge G n) :
    solutions G n (insert e S) = {x ∈ solutions G n S | Satisfies G n x e} := by
  ext x
  simp only [solutions, Set.mem_ofPred_eq, Set.mem_insert_iff]
  constructor
  · intro h
    exact ⟨fun f hf => h f (Or.inr hf), h e (Or.inl rfl)⟩
  · rintro ⟨hS,he⟩ f (rfl | hf)
    · exact he
    · exact hS f hf

/-- Every actual finite system of gain equations has the proved free-block normal form. -/
theorem exists_partition_finset (S : Finset (Edge G n)) :
    ∃ p : GainPartition G n, p.solutionSet = solutions G n (S : Set (Edge G n)) := by
  induction S using Finset.induction_on with
  | empty => exact ⟨GainPartition.discrete, by rw [Finset.coe_empty, solutions_empty,
      GainPartition.discrete_solutionSet]⟩
  | @insert e S he ih =>
    obtain ⟨p,hp⟩ := ih
    obtain ⟨q,hq,_⟩ := p.exists_impose_edge e
    refine ⟨q, ?_⟩
    rw [Finset.coe_insert, solutions_insert, ← hp]
    exact hq

theorem exists_partition [Finite G] (S : Set (Edge G n)) :
    ∃ p : GainPartition G n, p.solutionSet = solutions G n S := by
  obtain ⟨p,hp⟩ := exists_partition_finset S.toFinite.toFinset
  exact ⟨p, by simpa using hp⟩

end Dowling
