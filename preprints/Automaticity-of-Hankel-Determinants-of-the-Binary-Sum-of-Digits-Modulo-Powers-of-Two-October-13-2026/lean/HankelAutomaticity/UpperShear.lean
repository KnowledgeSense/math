import HankelAutomaticity.UpperPairing
import HankelAutomaticity.TailShear

noncomputable section
namespace HankelAutomaticity
open Matrix

 def shiftedBiased (a b : ℕ) (x z : ℚ) : Matrix (Fin (a+b+1)) (Fin (a+b+1)) ℚ :=
  Matrix.of fun i j => (digitSum (i.val+j.val) : ℚ)+z+
    ((x-2)/2)*(if a+b+1+a  ≤  i.val+j.val then 1 else 0)

 theorem upper_core_reduction (a b : ℕ) (x z : ℚ) :
    (upperCore a b x z).det =
      (bordered (shiftedBiased a b x z) 1 (x-2)).det *
        (-2*(x-2))^b * (antiTriangle (R:=ℚ) b).det := by
  let A := bordered (ordinaryBiased (a+b+1) z) 1 (x-2)
  let B : Matrix (Fin (a+b+1) ⊕ Unit) (Fin b) ℚ :=
    fromRows (Matrix.of fun i j => (x-2)*(if a+b+1  ≤  i.val+j.val+1 then 1 else 0)) 0
  let C : Matrix (Fin b) (Fin (a+b+1) ⊕ Unit) ℚ :=
    fromCols (Matrix.of fun i j => (x-2)*(if a+b+1  ≤  i.val+j.val+1 then 1 else 0)) 0
  let D : Matrix (Fin b) (Fin b) ℚ := (-2*(x-2)) • antiTriangle b
  let T := tailShear a b
  have hcross : T*D= -B := by
    ext i j
    rcases i with i | i
    · rcases index_low_or_tail i with hi | ⟨i, rfl⟩
      · rw [tailShear_mul_low D _ hi]
        have hj := j.isLt
        simp [B, fromRows, Sum.elim, show ¬a+b ≤ i.val+j.val by omega]
      · rw [tailShear_mul_high]
        simp [B, D, antiTriangle, fromRows, Sum.elim, tailIndex]
        split_ifs <;> first | omega | ring
    · rw [tailShear_mul_unit]
      simp [B, fromRows, Sum.elim]
  have hD : D.transpose=D := by
    ext i j
    simp [D, antiTriangle, add_comm]
  have hB : B.transpose=C := by
    ext i j
    rcases j with j | j <;> simp [B, C, fromRows, fromCols, Sum.elim, add_comm]
  have hcross' : D*T.transpose= -C := by
    have h := congrArg Matrix.transpose hcross
    rwa [Matrix.transpose_mul, Matrix.transpose_neg, hD, hB] at h
  have htop : A+T*C=bordered (shiftedBiased a b x z) 1 (x-2) := by
    ext i j
    rw [Matrix.add_apply]
    rcases i with i | i
    · rcases index_low_or_tail i with hi | ⟨i, rfl⟩
      · rw [tailShear_mul_low C _ hi]
        rcases j with j | j
        · have hj := j.isLt
          simp [A, bordered, ordinaryBiased, shiftedBiased, Matrix.fromBlocks,
            show ¬a+b+1+a ≤ i.val+j.val by omega]
        · simp [A, bordered, Matrix.fromBlocks]
      · rw [tailShear_mul_high]
        rcases j with j | j
        · simp [A, C, bordered, ordinaryBiased, shiftedBiased, Matrix.fromBlocks,
            fromCols, tailIndex]
          split_ifs <;> first | omega | ring
        · simp [A, C, bordered, Matrix.fromBlocks, fromCols]
    · rw [tailShear_mul_unit]
      rcases j with j | j <;> simp [A, bordered, Matrix.fromBlocks]
  have hs := det_upper_block_shear A B C D T
  have hc : A+T*C+B*T.transpose+T*D*T.transpose=A+T*C := by
    rw [hcross, Matrix.neg_mul]
    abel
  rw [hc, htop, hcross, hcross', add_neg_cancel, add_neg_cancel,
    det_fromBlocks_zero₂₁] at hs
  change _=(upperCore a b x z).det at hs
  rw [← hs]
  dsimp [D]
  rw [det_smul, Fintype.card_fin]
  ring

 theorem shiftedBiased_eq_hankel {L a b : ℕ} (hL : 0<L)
    (h : a+b+1+a=2^L) (x z : ℚ) :
    shiftedBiased a b x z=hankelMatrix (L-1) (a+b+1) (x/2)+
      (Matrix.of fun _ _ => z) := by
  ext i j
  have hij : i.val+j.val<2^(L+1) := by
    have hi := i.isLt
    have hj := j.isLt
    rw [pow_succ]
    omega
  simp only [shiftedBiased, Matrix.of_apply, Matrix.add_apply, hankelMatrix,
    weightedMoment_lower_top hL (x/2) hij]
  rw [← h]
  ring

end HankelAutomaticity
