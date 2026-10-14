import Mathlib.Combinatorics.Matroid.Rank.ENat
import Mathlib.Tactic

/-! The actual finite paving-matroid hypothesis and its first flat consequences.
No polynomial identity is included in the object definition. -/
namespace Paving

variable {α : Type*} [Fintype α]

noncomputable def rank (M : Matroid α) : ℕ := M.eRank.toNat

/-- A finite matroid is paving precisely when every circuit has at least its rank. -/
def IsPaving (M : Matroid α) : Prop := ∀ C : Set α, M.IsCircuit C → rank M ≤ C.ncard

theorem IsPaving.indep_of_card_lt {M : Matroid α} (hM : IsPaving M)
    {S : Set α} (hSE : S ⊆ M.E) (hS : S.ncard < rank M) : M.Indep S := by
  rw [M.indep_iff_forall_subset_not_isCircuit hSE]
  intro C hCS hC
  have hcard := Set.ncard_le_ncard hCS
  have hr := hM C hC
  omega

theorem IsPaving.small_set_isFlat {M : Matroid α} (hM : IsPaving M)
    {S : Set α} (hSE : S ⊆ M.E) (hS : S.ncard + 1 < rank M) : M.IsFlat S := by
  rw [M.isFlat_iff_closure_eq]
  apply Set.Subset.antisymm _ (M.subset_closure S hSE)
  intro e he
  by_contra heS
  obtain ⟨C, hCS, hC, _⟩ := M.exists_isCircuit_of_mem_closure he heS
  have hcard := Set.ncard_le_ncard hCS
  have hi : (insert e S).ncard = S.ncard + 1 := Set.ncard_insert_of_notMem heS
  have hr := hM C hC
  omega

theorem IsPaving.small_set_rank {M : Matroid α} (hM : IsPaving M)
    {S : Set α} (hSE : S ⊆ M.E) (hS : S.ncard < rank M) :
    (M.eRk S).toNat = S.ncard := by
  rw [(hM.indep_of_card_lt hSE hS).eRk_eq_encard]
  rfl

end Paving
