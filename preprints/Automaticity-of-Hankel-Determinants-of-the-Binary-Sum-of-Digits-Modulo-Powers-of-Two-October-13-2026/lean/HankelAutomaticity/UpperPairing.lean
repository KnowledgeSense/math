import HankelAutomaticity.LowerReduction

noncomputable section
set_option maxHeartbeats 2000000
namespace HankelAutomaticity
open Matrix

 def upperCore (a b : ℕ) (x z : ℚ) :
    Matrix ((Fin (a+b+1) ⊕ Unit) ⊕ Fin b) ((Fin (a+b+1) ⊕ Unit) ⊕ Fin b) ℚ :=
  fromBlocks (bordered (ordinaryBiased (a+b+1) z) 1 (x-2))
    (fromRows (Matrix.of fun i j => (x-2)*(if a+b+1 ≤ i.val+j.val+1 then 1 else 0)) 0)
    (fromCols (Matrix.of fun i j => (x-2)*(if a+b+1 ≤ i.val+j.val+1 then 1 else 0)) 0)
    ((-2*(x-2)) • antiTriangle b)

 def upperReindex (L a b : ℕ) (h : a+b+1+a=2^L) :
    ((Fin (a+b+1) ⊕ Unit) ⊕ Fin b) ⊕ (Fin a ⊕ Fin a) ≃
      (Fin (2^L) ⊕ Unit) ⊕ Fin (a+b) :=
  (Equiv.sumSumSumComm _ _ _ _).trans <|
    (Equiv.sumCongr
      ((Equiv.sumAssoc _ _ _).trans <|
        (Equiv.sumCongr (Equiv.refl _) (Equiv.sumComm _ _)).trans
          (Equiv.sumAssoc _ _ _).symm)
      (Equiv.sumComm _ _)).trans <|
    Equiv.sumCongr
      (Equiv.sumCongr (finSumFinEquiv.trans (finCongr h)) (Equiv.refl _)) finSumFinEquiv

 theorem upper_paired_reduction (L a b : ℕ) (h : a+b+1+a=2^L) (x z : ℚ) :
    (secondReduced L (a+b) x z).det = (-1 : ℚ)^a*(x-2)^(2*a)*(upperCore a b x z).det := by
  let E : Matrix ((Fin (a+b+1) ⊕ Unit) ⊕ Fin b) (Fin a) ℚ :=
    fromRows
      (fromRows (Matrix.of fun i j => (digitSum (i.val+(a+b+1)+j.val) : ℚ)+z)
        (Matrix.of fun _ _ => 1)) (Matrix.of fun _ _ => x-2)
  let G : Matrix (Fin a) (Fin a) ℚ :=
    Matrix.of fun i j => (digitSum ((a+b+1)+i.val+((a+b+1)+j.val)) : ℚ)+z
  let U : Matrix (Fin a) (Fin a) ℚ := (x-2) • antiTriangle a
  have he : (secondReduced L (a+b) x z).submatrix (upperReindex L a b h)
      (upperReindex L a b h)=
      fromBlocks (upperCore a b x z) (fromCols E 0) (fromRows E.transpose 0)
        (fromBlocks G U U 0) := by
    ext i j
    rcases i with ((i | i) | i) | (i | i) <;>
      rcases j with ((j | j) | j) | (j | j)
    all_goals
      simp [secondReduced, upperCore, ordinaryBiased, bordered, Matrix.fromBlocks,
        Matrix.submatrix, upperReindex, Equiv.sumSumSumComm, Equiv.sumAssoc,
        Equiv.sumComm, finSumFinEquiv, finCongr, E, G, U, antiTriangle, fromRows, fromCols,
        Sum.elim, Matrix.transpose_apply, add_comm, add_left_comm, add_assoc]
    all_goals
      first | omega | rfl | (split_ifs <;> first | omega | ring)
  have hd := congrArg Matrix.det he
  rw [det_submatrix_equiv_self, det_paired_corner] at hd
  rw [hd]
  dsimp [U]
  rw [Matrix.det_smul, Fintype.card_fin]
  have hs := det_antiTriangle_sq (R:=ℚ) a
  calc
    _ = (-1 : ℚ)^a*(x-2)^(2*a)*(upperCore a b x z).det * (antiTriangle (R:=ℚ) a).det^2 := by
      rw [show 2*a=a*2 by omega, pow_mul]
      ring
    _ = _ := by rw [hs, mul_one]

end HankelAutomaticity
