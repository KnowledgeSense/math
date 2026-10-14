import HankelAutomaticity.SecondReduction
import HankelAutomaticity.AntiTriangle

noncomputable section
namespace HankelAutomaticity
open Matrix

 def ordinaryBiased (t : ℕ) (z : ℚ) : Matrix (Fin t) (Fin t) ℚ :=
  Matrix.of fun i j => (digitSum (i.val+j.val) : ℚ)+z

 def pairedReindex (L t r : ℕ) (h : t+r=2^L) :
    (Fin t ⊕ Unit) ⊕ (Fin r ⊕ Fin r) ≃ (Fin (2^L) ⊕ Unit) ⊕ Fin r :=
  (Equiv.sumSumSumComm _ _ _ _).trans <|
    (Equiv.sumAssoc _ _ _).symm.trans <|
      Equiv.sumCongr
        (Equiv.sumCongr (finSumFinEquiv.trans (finCongr h)) (Equiv.refl _)) (Equiv.refl _)

 theorem lower_second_reduction (L t r : ℕ) (h : t+r=2^L) (hr : 2*r<2^L)
    (x z : ℚ) :
    (secondReduced L r x z).det = (-1 : ℚ)^r*(x-2)^(2*r)*
      (bordered (ordinaryBiased t z) 1 (x-2)).det := by
  let E : Matrix (Fin t ⊕ Unit) (Fin r) ℚ :=
    fromRows (Matrix.of fun i j => (digitSum (i.val+t+j.val) : ℚ)+z)
      (Matrix.of fun _ _ => 1)
  let G : Matrix (Fin r) (Fin r) ℚ :=
    Matrix.of fun i j => (digitSum (t+i.val+(t+j.val)) : ℚ)+z
  let U : Matrix (Fin r) (Fin r) ℚ := (x-2) • antiTriangle r
  have he : (secondReduced L r x z).submatrix (pairedReindex L t r h)
      (pairedReindex L t r h)=
      fromBlocks (bordered (ordinaryBiased t z) 1 (x-2)) (fromCols E 0)
        (fromRows E.transpose 0) (fromBlocks G U U 0) := by
    ext i j
    rcases i with (i | i) | (i | i) <;> rcases j with (j | j) | (j | j)
    all_goals
      simp [secondReduced, ordinaryBiased, bordered, Matrix.fromBlocks,
        Matrix.submatrix, pairedReindex, Equiv.sumSumSumComm, Equiv.sumAssoc,
        finSumFinEquiv, finCongr, E, G, U, antiTriangle, fromRows, fromCols,
        Sum.elim, Matrix.transpose_apply, add_comm, add_left_comm, add_assoc]
    all_goals
      first | omega | rfl | (split_ifs <;> first | omega | ring)
  have hd := congrArg Matrix.det he
  rw [det_submatrix_equiv_self, det_paired_corner] at hd
  rw [hd]
  dsimp [U]
  rw [Matrix.det_smul, Fintype.card_fin]
  have hs := det_antiTriangle_sq (R:=ℚ) r
  calc
    _ = (-1 : ℚ)^r*(x-2)^(2*r)*
        (bordered (ordinaryBiased t z) 1 (x-2)).det * (antiTriangle (R:=ℚ) r).det^2 := by
      rw [show 2*r=r*2 by omega, pow_mul]
      ring
    _ = _ := by rw [hs, mul_one]

end HankelAutomaticity
