import Dowling.ConstraintRank

noncomputable section
namespace Dowling
open scoped Classical
variable {G : Type*} [Group G] [Finite G] {n : ℕ}

theorem constraintRank_anti_solutions {S T : Set (Edge G n)}
    (h : solutions G n S ⊆ solutions G n T) : constraintRank T ≤ constraintRank S := by
  have hc := (partitionOf T).roots_card_mono (partitionOf S) (by
    rw [partitionOf_solutionSet, partitionOf_solutionSet]
    exact h)
  exact Nat.sub_le_sub_left hc n

theorem constraintRank_eq_of_solutions_eq {S T : Set (Edge G n)}
    (h : solutions G n S = solutions G n T) : constraintRank S = constraintRank T :=
  le_antisymm (constraintRank_anti_solutions h.symm.subset) (constraintRank_anti_solutions h.subset)

theorem solutions_eq_of_rank_eq {S T : Set (Edge G n)} (hst : S ⊆ T)
    (hr : constraintRank S = constraintRank T) : solutions G n T = solutions G n S := by
  let := Fintype.ofFinite G
  have hp := (partitionOf S).roots_card_le
  have hq := (partitionOf T).roots_card_le
  have he : (partitionOf S).roots.card = (partitionOf T).roots.card := by
    unfold constraintRank at hr
    omega
  apply Set.eq_of_subset_of_ncard_le (solutions_antitone hst)
  change Nat.card (solutions G n S) ≤ Nat.card (solutions G n T)
  rw [← partitionOf_solutionSet S, ← partitionOf_solutionSet T,
    GainPartition.solution_card_roots, GainPartition.solution_card_roots, he]

theorem constraintRank_insert_eq_iff (S : Set (Edge G n)) (e : Edge G n) :
    constraintRank (insert e S) = constraintRank S ↔
      ∀ x ∈ solutions G n S, Satisfies G n x e := by
  constructor
  · intro hr x hx
    have he := solutions_eq_of_rank_eq (Set.subset_insert e S) hr.symm
    have hx' : x ∈ solutions G n (insert e S) := he.symm ▸ hx
    exact hx' e (Set.mem_insert e S)
  · intro h
    apply constraintRank_eq_of_solutions_eq
    rw [solutions_insert]
    ext x
    exact ⟨And.left, fun hx => ⟨hx,h x hx⟩⟩

/-- If every added edge equation is already implied, no rank is added. -/
theorem constraintRank_le_of_implied (S T : Set (Edge G n))
    (h : ∀ e ∈ T, constraintRank (insert e S) = constraintRank S) :
    constraintRank T ≤ constraintRank S := by
  apply constraintRank_anti_solutions
  intro x hx e he
  exact (constraintRank_insert_eq_iff S e).mp (h e he) x hx

end Dowling
