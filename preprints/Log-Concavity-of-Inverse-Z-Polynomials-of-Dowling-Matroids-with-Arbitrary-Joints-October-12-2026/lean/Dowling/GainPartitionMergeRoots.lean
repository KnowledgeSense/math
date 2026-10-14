import Dowling.GainPartitionMerge

noncomputable section
namespace Dowling.GainPartition
open scoped Classical
variable {G : Type*} [Group G] {n : ℕ}

theorem mergeBlocks_isRoot (p : GainPartition G n) (r s : Fin n) (h : G)
    (hr : p.IsRoot r) (hrs : r < s) (j : Fin n) :
    (p.mergeBlocks r s h hr hrs).IsRoot j ↔ p.IsRoot j ∧ j ≠ s := by
  have hpr : p.code r = some (r,1) := hr
  by_cases hjr : j = r
  · subst j
    simp [IsRoot, mergeBlocks, hpr, hrs.ne]
  · cases hj : p.code j with
    | none => simp [IsRoot, mergeBlocks, hj]
    | some v =>
      rcases v with ⟨u,g⟩
      by_cases hu : u = s
      · subst u
        simp [IsRoot, mergeBlocks, hj, Prod.mk.injEq, Ne.symm hjr]
        exact fun hsj _ => hsj.symm
      · simp only [IsRoot, mergeBlocks, hj, hu, ite_false, Option.some.injEq, Prod.mk.injEq]
        constructor
        · rintro ⟨rfl,rfl⟩
          exact ⟨⟨rfl,rfl⟩,hu⟩
        · exact fun h => h.1

theorem mergeBlocks_roots (p : GainPartition G n) (r s : Fin n) (h : G)
    (hr : p.IsRoot r) (hrs : r < s) :
    (p.mergeBlocks r s h hr hrs).roots = p.roots.erase s := by
  ext j
  simp only [roots, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_erase,
    mergeBlocks_isRoot, and_comm]

theorem mergeBlocks_roots_card (p : GainPartition G n) (r s : Fin n) (h : G)
    (hr : p.IsRoot r) (hs : p.IsRoot s) (hrs : r < s) :
    (p.mergeBlocks r s h hr hrs).roots.card + 1 = p.roots.card := by
  rw [mergeBlocks_roots]
  exact Finset.card_erase_add_one (by simpa [roots] using hs)

end Dowling.GainPartition
