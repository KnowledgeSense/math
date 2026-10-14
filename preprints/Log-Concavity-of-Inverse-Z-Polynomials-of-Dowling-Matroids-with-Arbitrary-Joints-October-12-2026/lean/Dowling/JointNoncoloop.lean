import Dowling.JointFlat

noncomputable section
namespace Dowling
open scoped Classical
variable {G : Type*} [Group G] [Fintype G] {n : ℕ}

theorem joint_not_coloop_of_remaining_zero (X : Set (Fin n)) (i : Fin n) (hiX : i∈X)
    (hz : Admissible (X\{i}) (zeroPartition : GainPartition G n)) :
    ¬ (matroid G n X).IsColoop (Sum.inl i) := by
  have hS : ground G n (X\{i}) ⊆ ground G n X := by
    intro e he
    cases e with
    | inl j => exact he.1
    | inr e => trivial
  have he : Sum.inl i ∈ (matroid G n X).closure (ground G n (X\{i})) := by
    apply (matroid_mem_closure X _ hS _).mpr
    refine ⟨?_,hiX⟩
    intro x hx
    rw [← flatEdges_zeroPartition (X\{i}),flatEdges_solutions _ _ hz] at hx
    exact (((zeroPartition : GainPartition G n).mem_solutionSet x).mp hx).1 i rfl
  intro hc
  have h := hc.mem_of_mem_closure he
  exact h.2 (Set.mem_singleton i)

/-- Every retained joint is a noncoloop for a nontrivial gain group on at least
two vertices, even when no other joint is retained. -/
theorem joint_not_coloop_nontrivial [Nontrivial G] (X : Set (Fin n))
    (i : Fin n) (hiX : i∈X) (hn : 2≤n) : ¬ (matroid G n X).IsColoop (Sum.inl i) :=
  joint_not_coloop_of_remaining_zero X i hiX (zeroPartition_admissible_nontrivial _ hn)

/-- A second actual marked vertex supplies the order-one noncoloop condition. -/
theorem joint_not_coloop_other_mark (X : Set (Fin n)) (i : Fin n) (hiX : i∈X)
    (hj : ∃ j∈X, j≠i) : ¬ (matroid G n X).IsColoop (Sum.inl i) := by
  apply joint_not_coloop_of_remaining_zero X i hiX
  apply zeroPartition_admissible_marked
  obtain ⟨j,hjX,hji⟩ := hj
  exact ⟨j,hjX,hji⟩

end Dowling
