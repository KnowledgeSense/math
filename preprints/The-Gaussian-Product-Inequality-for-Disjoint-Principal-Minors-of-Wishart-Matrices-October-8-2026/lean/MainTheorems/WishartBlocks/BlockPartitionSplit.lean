import MainTheorems.WishartBlocks.PrincipalProductIntegrability
import MainTheorems.WishartBlocks.ShapeRange

namespace ResearchMain.WishartBlocks

open Matrix MeasureTheory ProbabilityTheory
open scoped BigOperators

def blockSigmaHeadEquiv {d : ℕ} (size : Fin (d + 1) → ℕ) :
    (Σ j : Fin (d + 1), Fin (size j)) ≃
      Fin (size 0) ⊕ (Σ j : Fin d, Fin (size j.succ)) where
  toFun := fun x => Fin.cases (fun i => Sum.inl i)
    (fun j i => Sum.inr ⟨j, i⟩) x.1 x.2
  invFun := Sum.elim (fun i => ⟨0, i⟩) (fun x => ⟨x.1.succ, x.2⟩)
  left_inv := by
    intro x
    rcases x with ⟨j, i⟩
    cases j using Fin.cases <;> rfl
  right_inv := by intro x; cases x <;> rfl

namespace BlockPartition

theorem total_size {p d : ℕ} (P : BlockPartition p d) : (∑ j, P.size j) = p := by
  have h := Fintype.card_congr P.index
  simpa only [Fintype.card_sigma, Fintype.card_fin] using h

def tail {p d : ℕ} (P : BlockPartition p (d + 1)) :
    BlockPartition (∑ j : Fin d, P.size j.succ) d :=
  standard (fun j => P.size j.succ) (fun j => P.size_pos j.succ)

def headReindex {p d : ℕ} (P : BlockPartition p (d + 1)) :
    Fin p ≃ Fin (P.size 0 + ∑ j : Fin d, P.size j.succ) :=
  P.index.symm.trans ((blockSigmaHeadEquiv P.size).trans
    ((Equiv.sumCongr (Equiv.refl _) finSigmaFinEquiv).trans finSumFinEquiv))

theorem headReindex_head {p d : ℕ} (P : BlockPartition p (d + 1)) (i : Fin (P.size 0)) :
    P.headReindex (P.inclusion 0 i) = finSumFinEquiv (Sum.inl i) := by
  simp only [headReindex, inclusion, Equiv.trans_apply, Equiv.symm_apply_apply]
  rfl

theorem headReindex_tail {p d : ℕ} (P : BlockPartition p (d + 1))
    (j : Fin d) (i : Fin (P.size j.succ)) :
    P.headReindex (P.inclusion j.succ i) =
      finSumFinEquiv (Sum.inr (P.tail.inclusion j i)) := by
  simp only [headReindex, inclusion, Equiv.trans_apply, Equiv.symm_apply_apply]
  rfl

theorem reindex_head_block {p d : ℕ} (P : BlockPartition p (d + 1))
    (W : Matrix (Fin p) (Fin p) ℝ) :
    (principalPair (k := P.size 0) (m := ∑ j : Fin d, P.size j.succ)
      (W.submatrix P.headReindex.symm P.headReindex.symm)).1 = P.block W 0 := by
  ext i j
  change W (P.headReindex.symm (finSumFinEquiv (Sum.inl i)))
    (P.headReindex.symm (finSumFinEquiv (Sum.inl j))) = W (P.inclusion 0 i) (P.inclusion 0 j)
  rw [← P.headReindex_head i, ← P.headReindex_head j, Equiv.symm_apply_apply, Equiv.symm_apply_apply]

theorem reindex_tail_block {p d : ℕ} (P : BlockPartition p (d + 1))
    (W : Matrix (Fin p) (Fin p) ℝ) (j : Fin d) :
    P.tail.block ((principalPair (k := P.size 0) (m := ∑ j : Fin d, P.size j.succ)
      (W.submatrix P.headReindex.symm P.headReindex.symm)).2) j = P.block W j.succ := by
  ext i l
  change W (P.headReindex.symm (finSumFinEquiv (Sum.inr (P.tail.inclusion j i))))
    (P.headReindex.symm (finSumFinEquiv (Sum.inr (P.tail.inclusion j l)))) =
      W (P.inclusion j.succ i) (P.inclusion j.succ l)
  rw [← P.headReindex_tail j i, ← P.headReindex_tail j l,
    Equiv.symm_apply_apply, Equiv.symm_apply_apply]

theorem determinantProduct_head_tail {p d : ℕ} (P : BlockPartition p (d + 1))
    (ν : Fin (d + 1) → ℝ) (W : Matrix (Fin p) (Fin p) ℝ) :
    P.determinantProduct ν W = (P.block W 0).det ^ ν 0 *
      P.tail.determinantProduct (fun j => ν j.succ)
        ((principalPair (k := P.size 0) (m := ∑ j : Fin d, P.size j.succ)
          (W.submatrix P.headReindex.symm P.headReindex.symm)).2) := by
  unfold determinantProduct determinantPower
  rw [Fin.prod_univ_succ]
  simp_rw [P.reindex_tail_block]
  rfl

theorem other_block_dimension {p n : ℕ} (P : BlockPartition p (n + 2)) (j : Fin (n + 2)) :
    P.size j + 1 ≤ p := by
  classical
  let i₀ : Fin (n + 2) := ⟨0, by omega⟩
  let i₁ : Fin (n + 2) := ⟨1, by omega⟩
  have hi : ∃ i : Fin (n + 2), i ≠ j := by
    by_cases hj : j = i₀
    · refine ⟨i₁, ?_⟩
      rw [hj]
      intro h
      have h' : (1 : ℕ) = 0 := congrArg Fin.val h
      norm_num at h'
    · exact ⟨i₀, Ne.symm hj⟩
  obtain ⟨i, hij⟩ := hi
  have hs : P.size j + P.size i ≤ ∑ a, P.size a := by
    have h := Finset.sum_le_sum_of_subset_of_nonneg (s := {j, i}) (t := Finset.univ)
      (by simp) (fun a _ _ => Nat.zero_le (P.size a))
    simpa only [Finset.sum_pair (Ne.symm hij)] using h
  rw [P.total_size] at hs
  have hp := P.size_pos i
  omega

theorem zero_block {p : ℕ} (P : BlockPartition p 0) {α : ℝ}
    (hα : (p : ℝ) - 1 < α) (S : Matrix (Fin p) (Fin p) ℝ) (ν : Fin 0 → ℝ) :
    P.ProductInequality α S ν := by
  let : IsProbabilityMeasure (bartlettLaw α S) := bartlett_law_probability hα S
  simp [ProductInequality, determinantProduct]

end BlockPartition
end ResearchMain.WishartBlocks
