import R34.SchurTensor
import R34.SchurSeries

noncomputable section

namespace R34

open MvPolynomial
open scoped BigOperators

def uniformTransfer : ColorMatrix := interaction 2*colorDiag

theorem uniformTransfer_characteristic :
    uniformTransfer*uniformTransfer =
      (C (2 : ℝ)*U) • uniformTransfer-(C (3 : ℝ)*V) • (1 : ColorMatrix) := by
  have h3 : (C (3 : ℝ) : Poly) = C 2*C 2-1 := by
    rw [← C_mul, ← C_1, ← C_sub]
    norm_num
  have h3' : (C (3 : ℝ) : Poly) = 3 := by rw [h3]; simp; ring
  apply Matrix.ext
  intro i j
  cases i <;> cases j <;>
    simp [uniformTransfer, interaction, colorDiag, edgeWeight, color,
      Matrix.mul_apply, Matrix.smul_apply, smul_eq_mul, U, V, h3']
  all_goals ring

theorem uniformTransfer_recurrence (n : ℕ) :
    uniformTransfer^(n+2) =
      (C (2 : ℝ)*U) • uniformTransfer^(n+1)-(C (3 : ℝ)*V) • uniformTransfer^n := by
  calc
    uniformTransfer^(n+2) = uniformTransfer^n*(uniformTransfer*uniformTransfer) := by
      rw [pow_add, pow_two]
    _ = uniformTransfer^n*((C (2 : ℝ)*U) • uniformTransfer-(C (3 : ℝ)*V) • (1 : ColorMatrix)) := by
      rw [uniformTransfer_characteristic]
    _ = (C (2 : ℝ)*U) • uniformTransfer^(n+1)-(C (3 : ℝ)*V) • uniformTransfer^n := by
      simp [Matrix.mul_sub, Matrix.mul_smul, pow_succ]

theorem uniform_chainMatrix (n : ℕ) :
    chainMatrix (List.replicate n (2 : ℝ)) = colorDiag*uniformTransfer^n := by
  simp [chainMatrix, List.map_replicate, List.prod_replicate, uniformTransfer]

theorem matrixTotal_sub (A B : ColorMatrix) : matrixTotal (A-B)=matrixTotal A-matrixTotal B := by
  simp [matrixTotal, Finset.sum_sub_distrib]

theorem uniform_chain_recurrence (n : ℕ) :
    listChain (List.replicate (n+2) (2 : ℝ)) =
      C (2 : ℝ)*U*listChain (List.replicate (n+1) (2 : ℝ))-
      C (3 : ℝ)*V*listChain (List.replicate n (2 : ℝ)) := by
  simp only [listChain, uniform_chainMatrix]
  rw [uniformTransfer_recurrence]
  simp only [Matrix.mul_sub, Matrix.mul_smul, matrixTotal_sub, matrixTotal_smul]

theorem uniform_chain_two : listChain [2]=C (2 : ℝ)*h 2 := by
  simp [listChain, chainMatrix, matrixTotal, colorDiag, interaction,
    Matrix.mul_apply, color, edgeWeight]
  rw [h_succ 1, h_one]
  unfold U
  ring

def uniformSequence : ℕ → Poly
  | 0 => 1
  | n+1 => listChain (List.replicate n 2)

theorem uniform_chain_schurPositive (n : ℕ) :
    SchurPositive (listChain (List.replicate n (2 : ℝ))) := by
  apply schurPositive_of_uniform_recurrence uniformSequence
  · simp [uniformSequence]
  · simpa [uniformSequence] using uniform_chain_two
  · intro k
    exact uniform_chain_recurrence k

end R34



