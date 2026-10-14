import MainTheorems.WishartBlocks.RankOneLaplaceOperator

namespace ResearchMain.WishartBlocks

open Matrix
open scoped BigOperators InnerProductSpace

noncomputable def laplaceMatrixTest {p : ℕ} (T W : Matrix (Fin p) (Fin p) ℝ) : ℝ :=
  Real.exp (-(T * W).trace)

noncomputable def laplaceMatrixTestDirectional {p : ℕ}
    (T W H : Matrix (Fin p) (Fin p) ℝ) : ℝ :=
  -(T * H).trace * laplaceMatrixTest T W

noncomputable def laplaceMatrixTestHessian {p : ℕ}
    (T W H J : Matrix (Fin p) (Fin p) ℝ) : ℝ :=
  (T * H).trace * (T * J).trace * laplaceMatrixTest T W

theorem laplaceMatrixTest_directional {p : ℕ}
    (T W H : Matrix (Fin p) (Fin p) ℝ) :
    HasDerivAt (fun t : ℝ => laplaceMatrixTest T (W + t • H))
      (laplaceMatrixTestDirectional T W H) 0 := by
  have h := ((hasDerivAt_const (0 : ℝ) (-(T * W).trace)).add
    ((hasDerivAt_id' (0 : ℝ)).const_mul (-(T * H).trace))).exp
  convert h using 1
  · funext t
    simp only [laplaceMatrixTest, Matrix.mul_add, Matrix.mul_smul,
      Matrix.trace_add, Matrix.trace_smul, smul_eq_mul, Pi.add_apply]
    congr 1
    ring_nf
  · dsimp only [Pi.add_apply, laplaceMatrixTestDirectional, laplaceMatrixTest]
    ring_nf

theorem laplaceMatrixTest_hessian {p : ℕ}
    (T W H J : Matrix (Fin p) (Fin p) ℝ) :
    HasDerivAt (fun t : ℝ => laplaceMatrixTestDirectional T (W + t • J) H)
      (laplaceMatrixTestHessian T W H J) 0 := by
  have h := (laplaceMatrixTest_directional T W J).const_mul (-(T * H).trace)
  convert h using 1
  · rfl
  · dsimp only [laplaceMatrixTestHessian, laplaceMatrixTestDirectional]
    ring_nf

theorem trace_outer_quadratic_sandwich {p : ℕ} (T W : Matrix (Fin p) (Fin p) ℝ)
    (hT : T.transpose = T) (v : Fin p → ℝ) :
    (Matrix.vecMulVec (T *ᵥ v) (T *ᵥ v) * W).trace =
      v ⬝ᵥ ((T * W * T) *ᵥ v) := by
  rw [Matrix.trace_mul_comm, trace_matrix_outer, symmetric_mulVec_dotProduct T hT]
  simp only [← Matrix.mulVec_mulVec]

theorem laplaceMatrixTest_operator_contraction {p : ℕ} {κ : Type*} [Fintype κ]
    (q : ℝ) (T : Matrix (Fin p) (Fin p) ℝ) (hT : T.transpose = T)
    (U : κ → Fin p → ℝ) (v : EuclideanSpace ℝ (Fin p)) :
    q * laplaceMatrixTestDirectional T (gramSum U)
        (Matrix.vecMulVec (fun i => v i) (fun i => v i)) +
      2 * ∑ i, laplaceMatrixTestHessian T (gramSum U)
        (rankTwoDirection (U i) (fun j => v j))
        (rankTwoDirection (U i) (fun j => v j)) =
      rankOneLaplaceOperatorValue q T (gramSum U) v := by
  simp only [laplaceMatrixTestDirectional, laplaceMatrixTestHessian]
  rw [trace_vectorGram]
  simp_rw [trace_rankTwoDirection T hT]
  have hs : (∑ i, (U i ⬝ᵥ (T *ᵥ fun j => v j)) *
      (U i ⬝ᵥ (T *ᵥ fun j => v j)) * laplaceMatrixTest T (gramSum U)) =
      (Matrix.vecMulVec (T *ᵥ fun j => v j) (T *ᵥ fun j => v j) * gramSum U).trace *
        laplaceMatrixTest T (gramSum U) := by
    rw [← Finset.sum_mul]
    simp only [← pow_two]
    rw [← quadratic_gramSum T hT, trace_outer_quadratic_sandwich T (gramSum U) hT]
  rw [hs]
  dsimp only [rankOneLaplaceOperatorValue, laplaceMatrixTest]
  ring_nf

end ResearchMain.WishartBlocks
