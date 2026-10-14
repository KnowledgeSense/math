import Dowling.ZeroPartition

noncomputable section
namespace Dowling.GainPartition
open scoped Classical
variable {G : Type*} [Group G] {n : ℕ}

instance : OrderBot (GainPartition G n) where
  bot := discrete
  bot_le p := by
    change p.solutionSet ⊆ discrete.solutionSet
    rw [discrete_solutionSet]
    exact Set.subset_univ _

theorem assignment_zero (p : GainPartition G n) : p.assignment (fun _ => none) = fun _ => none := by
  funext i
  cases hi : p.code i <;> simp [assignment,hi]

theorem zeroPartition_solutionSet : (zeroPartition : GainPartition G n).solutionSet = {fun _ => none} := by
  ext x
  constructor
  · intro hx
    apply funext
    intro i
    exact (((zeroPartition : GainPartition G n).mem_solutionSet x).mp hx).1 i rfl
  · rintro rfl
    exact ⟨fun _ => none,assignment_zero zeroPartition⟩

instance : OrderTop (GainPartition G n) where
  top := zeroPartition
  le_top p := by
    change zeroPartition.solutionSet ⊆ p.solutionSet
    rw [zeroPartition_solutionSet]
    intro x hx
    rcases hx with rfl
    exact ⟨fun _ => none,p.assignment_zero⟩

instance [Finite G] : LocallyFiniteOrder (GainPartition G n) := Fintype.toLocallyFiniteOrder

end Dowling.GainPartition
