import Dowling.GainPartitionCard
import Mathlib.Data.Set.Card

noncomputable section
namespace Dowling
open scoped Classical
variable {G : Type*} [Group G] [Finite G] {n : ℕ}

def partitionOf (S : Set (Edge G n)) : GainPartition G n := (exists_partition S).choose

theorem partitionOf_solutionSet (S : Set (Edge G n)) :
    (partitionOf S).solutionSet = solutions G n S := (exists_partition S).choose_spec

/-- The number of independent gain equations, before restricting the retained joints. -/
def constraintRank (S : Set (Edge G n)) : ℕ := n - (partitionOf S).roots.card

theorem constraintRank_eq (S : Set (Edge G n)) (p : GainPartition G n)
    (hp : p.solutionSet = solutions G n S) : constraintRank S = n - p.roots.card := by
  unfold constraintRank
  rw [GainPartition.roots_card_eq (partitionOf S) p ((partitionOf_solutionSet S).trans hp.symm)]

theorem constraintRank_le (S : Set (Edge G n)) : constraintRank S ≤ n := Nat.sub_le _ _

theorem constraintRank_mono {S T : Set (Edge G n)} (h : S ⊆ T) :
    constraintRank S ≤ constraintRank T := by
  have hc := (partitionOf S).roots_card_mono (partitionOf T) (by
    rw [partitionOf_solutionSet, partitionOf_solutionSet]
    exact solutions_antitone h)
  exact Nat.sub_le_sub_left hc n

@[simp] theorem constraintRank_empty : constraintRank (∅ : Set (Edge G n)) = 0 := by
  rw [constraintRank_eq _ GainPartition.discrete (by
    rw [GainPartition.discrete_solutionSet, solutions_empty])]
  have hr : (GainPartition.discrete : GainPartition G n).roots = Finset.univ := by
    ext i
    simp only [GainPartition.roots, Finset.mem_filter, Finset.mem_univ, true_and]
    change (some (i,(1:G)) = some (i,1)) ↔ True
    simp
  rw [hr]
  simp

theorem constraintRank_insert (S : Set (Edge G n)) (e : Edge G n) :
    constraintRank (insert e S) = constraintRank S ∨
      constraintRank (insert e S) = constraintRank S + 1 := by
  obtain ⟨q,hq,hcard⟩ := (partitionOf S).exists_impose_edge e
  have hqs : q.solutionSet = solutions G n (insert e S) := by
    rw [solutions_insert, ← partitionOf_solutionSet S]
    exact hq
  rw [constraintRank_eq _ q hqs]
  unfold constraintRank
  rcases hcard with rfl | hcard
  · exact Or.inl rfl
  · right
    have hp := (partitionOf S).roots_card_le
    omega

theorem constraintRank_insert_le (S : Set (Edge G n)) (e : Edge G n) :
    constraintRank (insert e S) ≤ constraintRank S + 1 := by
  rcases constraintRank_insert S e with h | h <;> omega

end Dowling
