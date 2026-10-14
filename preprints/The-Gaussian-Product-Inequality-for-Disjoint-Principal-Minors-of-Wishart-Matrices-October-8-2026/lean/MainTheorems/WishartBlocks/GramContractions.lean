import MainTheorems.WishartBlocks.RankTwoDirections

namespace ResearchMain.WishartBlocks

open Matrix
open scoped BigOperators

noncomputable def gramSum {ι κ : Type*} [Fintype κ] (U : κ → ι → ℝ) : Matrix ι ι ℝ :=
  ∑ i, Matrix.vecMulVec (U i) (U i)

theorem gramSum_positiveSemidefinite {ι κ : Type*} [Fintype ι] [Fintype κ]
    (U : κ → ι → ℝ) : (gramSum U).PosSemidef := by
  apply Matrix.posSemidef_sum
  intro i _
  simpa only [star_trivial] using Matrix.posSemidef_vecMulVec_self_star (U i)

theorem gramSum_columns {ι κ : Type*} [Fintype κ] (R : Matrix ι κ ℝ) :
    gramSum (fun k i => R i k) = R * R.transpose := by
  ext i j
  simp only [gramSum, Matrix.sum_apply, Matrix.vecMulVec_apply, Matrix.mul_apply,
    Matrix.transpose_apply]

theorem trace_gramSum {ι κ : Type*} [Fintype ι] [Fintype κ]
    (G : Matrix ι ι ℝ) (U : κ → ι → ℝ) :
    (G * gramSum U).trace = ∑ i, U i ⬝ᵥ (G *ᵥ U i) := by
  simp only [gramSum, Matrix.mul_sum, Matrix.trace_sum, trace_matrix_outer]

theorem quadratic_gramSum {ι κ : Type*} [Fintype ι] [Fintype κ]
    (G : Matrix ι ι ℝ) (hG : G.transpose = G) (U : κ → ι → ℝ) (v : ι → ℝ) :
    v ⬝ᵥ ((G * gramSum U * G) *ᵥ v) = ∑ i, (U i ⬝ᵥ (G *ᵥ v)) ^ 2 := by
  rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, gramSum,
    Matrix.sum_mulVec, Matrix.mulVec_sum, dotProduct_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [Matrix.vecMulVec_mulVec, op_smul_eq_smul, Matrix.mulVec_smul, dotProduct_smul]
  rw [symmetric_matrix_quadratic_comm G hG v (U i)]
  ring

theorem gramSum_submatrix {ι κ ρ : Type*} [Fintype κ]
    (U : κ → ι → ℝ) (e : ρ → ι) :
    (gramSum U).submatrix e e = gramSum (fun i j => U i (e j)) := by
  ext i j
  simp only [gramSum, Matrix.submatrix_apply, Matrix.sum_apply, Matrix.vecMulVec_apply]

theorem rankTwo_hessian_sum {ι κ : Type*} [Fintype ι] [Fintype κ]
    (G : Matrix ι ι ℝ) (hG : G.transpose = G) (U : κ → ι → ℝ) (v : ι → ℝ) :
    (∑ i, (G * rankTwoDirection (U i) v * G * rankTwoDirection (U i) v).trace) =
      ((v ⬝ᵥ ((G * gramSum U * G) *ᵥ v)) +
        (G * gramSum U).trace * (v ⬝ᵥ (G *ᵥ v))) / 2 := by
  simp_rw [trace_rankTwoDirection_square G hG]
  rw [← Finset.sum_div, Finset.sum_add_distrib, ← Finset.sum_mul,
    ← quadratic_gramSum G hG U v, trace_gramSum]

end ResearchMain.WishartBlocks
