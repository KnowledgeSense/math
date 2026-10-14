import HankelAutomaticity.FirstReduction
import HankelAutomaticity.BorderedDeterminant

noncomputable section
namespace HankelAutomaticity
open Matrix

 def splitFirst (r : ℕ) : Unit ⊕ Fin r ≃ Fin (r+1) where
  toFun := fun j => match j with
    | Sum.inl _ => 0
    | Sum.inr j => j.succ
  invFun := fun j => if h : j.val=0 then Sum.inl () else Sum.inr ⟨j.val-1, by omega⟩
  left_inv := by
    intro j
    rcases j with j | j
    · simp
    · simp
  right_inv := by
    intro j
    dsimp only
    split_ifs with h
    · exact Fin.ext h.symm
    · apply Fin.ext
      simp
      omega

 def separateFirst (M r : ℕ) : (Fin M ⊕ Unit) ⊕ Fin r ≃ Fin M ⊕ Fin (r+1) :=
  (Equiv.sumAssoc _ _ _).trans (Equiv.sumCongr (Equiv.refl _) (splitFirst r))

 def secondReduced (L r : ℕ) (x z : ℚ) :
    Matrix ((Fin (2^L) ⊕ Unit) ⊕ Fin r) ((Fin (2^L) ⊕ Unit) ⊕ Fin r) ℚ :=
  fromBlocks
    (bordered (Matrix.of fun i j => (digitSum (i.val+j.val) : ℚ)+z) 1 (x-2))
    (fromRows (Matrix.of fun i j => (x-2)*(if 2^L ≤ i.val+j.val+1 then 1 else 0)) 0)
    (fromCols (Matrix.of fun i j => (x-2)*(if 2^L ≤ i.val+j.val+1 then 1 else 0)) 0)
    (Matrix.of fun i j => -2*(x-2)*(if 2^L ≤ i.val+j.val+2 then 1 else 0))

 theorem second_reduction (L r : ℕ) (hr : r+1≤2^L) (x z : ℚ) :
    (secondReduced L r x z).det=(firstReduced L (r+1) x z).det := by
  let M := (firstReduced L (r+1) x z).submatrix (separateFirst (2^L) r)
    (separateFirst (2^L) r)
  let A := M.toBlocks₁₁
  let B := M.toBlocks₁₂
  let C := M.toBlocks₂₁
  let D := M.toBlocks₂₂
  let T : Matrix (Fin r) (Fin (2^L) ⊕ Unit) ℚ :=
    Matrix.of fun _ j => match j with | Sum.inl _ => 0 | Sum.inr _ => -1
  have hmul {b : Type} (P : Matrix (Fin (2^L) ⊕ Unit) b ℚ)
      (i : Fin r) (j : b) : (T*P) i j= -P (Sum.inr ()) j := by
    simp [T, Matrix.mul_apply, Fintype.sum_sum_type]
  have hmul' {b : Type} (P : Matrix b (Fin (2^L) ⊕ Unit) ℚ)
      (i : b) (j : Fin r) : (P*T.transpose) i j= -P i (Sum.inr ()) := by
    simp [T, Matrix.mul_apply, Fintype.sum_sum_type, Matrix.transpose_apply]
  have he : secondReduced L r x z=fromBlocks A (B+A*T.transpose)
      (C+T*A) (D+T*B+C*T.transpose+T*A*T.transpose) := by
    unfold secondReduced
    apply Matrix.fromBlocks_inj.mpr
    refine ⟨?_, ?_, ?_, ?_⟩
    · ext i j
      rcases i with i | i <;> rcases j with j | j
      all_goals
        simp [A, M, firstReduced, bordered, Matrix.fromBlocks, Matrix.submatrix,
          separateFirst, splitFirst, Equiv.sumAssoc, Matrix.toBlocks₁₁]
    · ext i j
      erw [Matrix.add_apply, hmul']
      rcases i with i | i
      all_goals
        simp [A, B, M, firstReduced, Matrix.fromBlocks, Matrix.submatrix,
          separateFirst, splitFirst, Equiv.sumAssoc, Matrix.toBlocks₁₁, Matrix.toBlocks₁₂, fromRows, Sum.elim, add_assoc]
      all_goals
        try split_ifs <;> simp_all
      all_goals omega
    · ext i j
      erw [Matrix.add_apply, hmul]
      rcases j with j | j
      all_goals
        simp [A, C, M, firstReduced, Matrix.fromBlocks, Matrix.submatrix,
          separateFirst, splitFirst, Equiv.sumAssoc, Matrix.toBlocks₁₁, Matrix.toBlocks₂₁, fromCols, Sum.elim, add_assoc]
      all_goals
        try split_ifs <;> simp_all
      all_goals omega
    · ext i j
      simp only [Matrix.add_apply]
      erw [hmul, hmul', hmul', hmul]
      simp [A, B, C, D, M, firstReduced, Matrix.fromBlocks, Matrix.submatrix,
        separateFirst, splitFirst, Equiv.sumAssoc, Matrix.toBlocks₁₁, Matrix.toBlocks₁₂,
          Matrix.toBlocks₂₁, Matrix.toBlocks₂₂]
      have hi := i.isLt
      have hj := j.isLt
      have h0 : ¬2^L ≤ i.val+1 := by omega
      have h1 : ¬2^L ≤ j.val+1 := by omega
      simp [h0, h1, show i.val+1+(j.val+1)=i.val+j.val+2 by omega]
      split_ifs <;> ring
  rw [he, det_block_shear]
  change (fromBlocks M.toBlocks₁₁ M.toBlocks₁₂ M.toBlocks₂₁ M.toBlocks₂₂).det=_
  rw [fromBlocks_toBlocks, det_submatrix_equiv_self]

end HankelAutomaticity
