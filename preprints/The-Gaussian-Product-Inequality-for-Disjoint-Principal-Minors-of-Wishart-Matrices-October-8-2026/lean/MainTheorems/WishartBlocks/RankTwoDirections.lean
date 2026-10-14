import MainTheorems.WishartBlocks.SymmetricDirections
import MainTheorems.WishartBlocks.DeterminantProductDerivatives

namespace ResearchMain.WishartBlocks

open Matrix
open scoped BigOperators

noncomputable def rankTwoDirection {ι : Type*} (u v : ι → ℝ) : Matrix ι ι ℝ :=
  (1 / 2 : ℝ) • (Matrix.vecMulVec u v + Matrix.vecMulVec v u)

theorem trace_matrix_outer {ι : Type*} [Fintype ι] (G : Matrix ι ι ℝ) (u v : ι → ℝ) :
    (G * Matrix.vecMulVec u v).trace = v ⬝ᵥ (G *ᵥ u) := by
  rw [Matrix.mul_vecMulVec, Matrix.trace_vecMulVec, dotProduct_comm]

theorem trace_matrix_two_outers {ι : Type*} [Fintype ι] (G : Matrix ι ι ℝ)
    (u v x y : ι → ℝ) :
    (G * Matrix.vecMulVec u v * G * Matrix.vecMulVec x y).trace =
      (v ⬝ᵥ (G *ᵥ x)) * (y ⬝ᵥ (G *ᵥ u)) := by
  rw [trace_matrix_outer, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec,
    Matrix.vecMulVec_mulVec, op_smul_eq_smul, Matrix.mulVec_smul, dotProduct_smul]
  simp only [smul_eq_mul]

theorem symmetric_matrix_quadratic_comm {ι : Type*} [Fintype ι] (G : Matrix ι ι ℝ)
    (hG : G.transpose = G) (u v : ι → ℝ) :
    v ⬝ᵥ (G *ᵥ u) = u ⬝ᵥ (G *ᵥ v) := by
  rw [Matrix.dotProduct_mulVec, dotProduct_comm, ← Matrix.mulVec_transpose, hG]

theorem trace_rankTwoDirection {ι : Type*} [Fintype ι] (G : Matrix ι ι ℝ)
    (hG : G.transpose = G) (u v : ι → ℝ) :
    (G * rankTwoDirection u v).trace = u ⬝ᵥ (G *ᵥ v) := by
  simp only [rankTwoDirection, Matrix.mul_smul, Matrix.mul_add, Matrix.trace_smul,
    Matrix.trace_add, trace_matrix_outer, smul_eq_mul]
  rw [symmetric_matrix_quadratic_comm G hG u v]
  ring

theorem trace_rankTwoDirection_square {ι : Type*} [Fintype ι] (G : Matrix ι ι ℝ)
    (hG : G.transpose = G) (u v : ι → ℝ) :
    (G * rankTwoDirection u v * G * rankTwoDirection u v).trace =
      ((u ⬝ᵥ (G *ᵥ v)) ^ 2 + (u ⬝ᵥ (G *ᵥ u)) * (v ⬝ᵥ (G *ᵥ v))) / 2 := by
  simp only [rankTwoDirection, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_add,
    Matrix.add_mul, Matrix.trace_smul, Matrix.trace_add, trace_matrix_two_outers, smul_eq_mul]
  rw [symmetric_matrix_quadratic_comm G hG u v]
  ring

theorem determinant_product_rankTwo_hessian {d : ℕ} {r : Fin d → ℕ}
    (A : ∀ j, Matrix (Fin (r j)) (Fin (r j)) ℝ)
    (u v : ∀ j, Fin (r j) → ℝ) (b : Fin d → ℝ) (hA : ∀ j, (A j).PosDef) :
    HasDerivAt
      (fun t : ℝ => determinantProductDirectional
        (fun j => A j + t • rankTwoDirection (u j) (v j))
        (fun j => rankTwoDirection (u j) (v j)) b)
      (determinantProductValue A b *
        ((∑ j, b j * ((u j) ⬝ᵥ ((A j)⁻¹ *ᵥ v j))) ^ 2 -
          ∑ j, b j / 2 *
            (((u j) ⬝ᵥ ((A j)⁻¹ *ᵥ v j)) ^ 2 +
              ((u j) ⬝ᵥ ((A j)⁻¹ *ᵥ u j)) * ((v j) ⬝ᵥ ((A j)⁻¹ *ᵥ v j))))) 0 := by
  have hG : ∀ j, ((A j)⁻¹).transpose = (A j)⁻¹ := by
    intro j
    simpa only [Matrix.conjTranspose_eq_transpose_of_trivial] using
      (hA j).posSemidef.inv.isHermitian.eq
  have h := determinant_product_hessian_directional A
    (fun j => rankTwoDirection (u j) (v j))
    (fun j => rankTwoDirection (u j) (v j)) b (fun j => (hA j).det_pos)
  simp_rw [trace_rankTwoDirection _ (hG _), trace_rankTwoDirection_square _ (hG _)] at h
  have hSum :
      (∑ j, b j * ((((u j) ⬝ᵥ ((A j)⁻¹ *ᵥ v j)) ^ 2 +
        ((u j) ⬝ᵥ ((A j)⁻¹ *ᵥ u j)) * ((v j) ⬝ᵥ ((A j)⁻¹ *ᵥ v j))) / 2)) =
      ∑ j, b j / 2 * (((u j) ⬝ᵥ ((A j)⁻¹ *ᵥ v j)) ^ 2 +
        ((u j) ⬝ᵥ ((A j)⁻¹ *ᵥ u j)) * ((v j) ⬝ᵥ ((A j)⁻¹ *ᵥ v j))) := by
    apply Finset.sum_congr rfl
    intro j _
    ring
  rw [hSum] at h
  simpa only [pow_two] using h

end ResearchMain.WishartBlocks
