import Paving.FlatRanks
import Paving.InverseZSymmetry
import ThagomizerTuran.MatroidDefinitions
import Mathlib.Combinatorics.Matroid.Loop

namespace Paving
variable {α : Type*} [Fintype α]

noncomputable instance actualFlatOrderBot (M : Matroid α) : OrderBot (MatroidInverseZ.Flat M) where
  bot := MatroidInverseZ.bottomFlat M
  bot_le F := by
    change M.closure ∅ ⊆ F.1
    rw [← F.2.closure]
    exact M.closure_subset_closure (Set.empty_subset _)

instance actualFlatOrderTop (M : Matroid α) : OrderTop (MatroidInverseZ.Flat M) where
  top := MatroidInverseZ.topFlat M
  le_top F := F.2.subset_ground

theorem actualFlatRank_strictMono (M : Matroid α) : StrictMono (MatroidInverseZ.flatRank M) := by
  intro F G hFG
  exact flat_subsetRank_strict F.2 G.2 hFG

omit [Fintype α] in
@[simp] theorem actualFlatRank_bot (M : Matroid α) : MatroidInverseZ.flatRank M ⊥ = 0 := by
  change (M.eRk (M.closure ∅)).toNat = 0
  simp

omit [Fintype α] in
@[simp] theorem actualFlatRank_top (M : Matroid α) : MatroidInverseZ.flatRank M ⊤ = rank M := by
  change (M.eRk M.E).toNat = rank M
  rw [M.eRk_ground]
  rfl

omit [Fintype α] in
@[simp] theorem actualFlat_bot_val (M : Matroid α) [M.Loopless] :
    (⊥ : MatroidInverseZ.Flat M).val = ∅ := by
  change M.closure ∅ = ∅
  rw [M.closure_empty, M.loops_eq_empty]

/-- Rank reversal of the genuine finite-matroid invariant, with no paving
coefficient formula assumed. -/
theorem actual_inverseZ_coeff_symm (M : Matroid α) (k : ℕ) (hk : k ≤ rank M) :
    (MatroidInverseZ.matroidInverseZ M).coeff k =
      (MatroidInverseZ.matroidInverseZ M).coeff (rank M-k) := by
  classical
  have h := MatroidInverseZ.inverseZ_coeff_symm (MatroidInverseZ.flatRank M)
    (actualFlatRank_strictMono M).monotone ⊥ ⊤ k (by simpa using hk)
  simp only [actualFlatRank_bot, actualFlatRank_top, Nat.sub_zero] at h
  change (MatroidInverseZ.inverseZ (MatroidInverseZ.flatRank M) ⊥ ⊤).coeff k =
    (MatroidInverseZ.inverseZ (MatroidInverseZ.flatRank M) ⊥ ⊤).coeff (rank M-k)
  exact h

end Paving
