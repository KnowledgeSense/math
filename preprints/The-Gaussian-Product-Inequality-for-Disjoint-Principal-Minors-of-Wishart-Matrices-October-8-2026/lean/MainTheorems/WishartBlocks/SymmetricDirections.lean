import MainTheorems.WishartBlocks.DeterminantDerivatives
import Mathlib.Analysis.Matrix.Order
import Mathlib.LinearAlgebra.Matrix.Trace

namespace ResearchMain.WishartBlocks

noncomputable def symmetricDirection {n : ℕ} (i j : Fin n) : Matrix (Fin n) (Fin n) ℝ :=
  (1 / 2 : ℝ) • (Matrix.single i j 1 + Matrix.single j i 1)

theorem symmetricDirection_transpose {n : ℕ} (i j : Fin n) :
    (symmetricDirection i j).transpose = symmetricDirection i j := by
  simp [symmetricDirection, add_comm]

theorem symmetricDirection_diagonal {n : ℕ} (i : Fin n) :
    symmetricDirection i i = Matrix.single i i 1 := by
  unfold symmetricDirection
  module

theorem trace_symmetricDirection {n : ℕ} (G : Matrix (Fin n) (Fin n) ℝ)
    (hG : G.transpose = G) (i j : Fin n) :
    (G * symmetricDirection i j).trace = G i j := by
  have hs : G j i = G i j := congrArg (fun M => M i j) hG
  simp only [symmetricDirection, mul_smul_comm, mul_add, Matrix.trace_smul,
    Matrix.trace_add, Matrix.trace_mul_single, smul_eq_mul]
  simp only [MulOpposite.op_one, one_smul]
  rw [hs]
  ring

theorem trace_single_quadratic {n : ℕ} (G : Matrix (Fin n) (Fin n) ℝ)
    (i j k l : Fin n) :
    (G * Matrix.single k l 1 * G * Matrix.single i j 1).trace = G j k * G l i := by
  rw [Matrix.trace_mul_single]
  simp [Matrix.mul_apply, Matrix.single, ite_and]

theorem trace_symmetricDirection_quadratic {n : ℕ}
    (G : Matrix (Fin n) (Fin n) ℝ) (hG : G.transpose = G) (i j k l : Fin n) :
    (G * symmetricDirection k l * G * symmetricDirection i j).trace =
      (G i k * G j l + G i l * G j k) / 2 := by
  have hs : ∀ a b, G b a = G a b := fun a b => congrArg (fun M => M a b) hG
  simp only [symmetricDirection, mul_smul_comm, smul_mul_assoc, mul_add, add_mul,
    Matrix.trace_smul, Matrix.trace_add, smul_eq_mul, trace_single_quadratic]
  rw [hs i l, hs j l, hs i k, hs j k]
  ring

theorem determinant_power_symmetric_hessian {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℝ) (hA : A.PosDef) (b : ℝ) (i j k l : Fin n) :
    HasDerivAt
      (fun t : ℝ => (A + t • symmetricDirection k l).det ^ b *
        (b * ((A + t • symmetricDirection k l)⁻¹ * symmetricDirection i j).trace))
      (A.det ^ b * (b ^ 2 * A⁻¹ i j * A⁻¹ k l -
        b / 2 * (A⁻¹ i k * A⁻¹ j l + A⁻¹ i l * A⁻¹ j k))) 0 := by
  have hG : (A⁻¹).transpose = A⁻¹ := by
    simpa only [Matrix.conjTranspose_eq_transpose_of_trivial] using
      hA.posSemidef.inv.isHermitian.eq
  have h := determinant_power_hessian_directional A (symmetricDirection i j)
    (symmetricDirection k l) hA.det_pos b
  rw [trace_symmetricDirection A⁻¹ hG i j, trace_symmetricDirection A⁻¹ hG k l,
    trace_symmetricDirection_quadratic A⁻¹ hG i j k l] at h
  convert h using 1
  ring

end ResearchMain.WishartBlocks
