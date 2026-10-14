import MainTheorems.WishartBlocks.GramContractions
import MainTheorems.WishartBlocks.BlockOperator

namespace ResearchMain.WishartBlocks

open Matrix
open scoped BigOperators MatrixOrder

theorem blockDiagonal_mulVec_apply {d : ℕ} {r : Fin d → ℕ}
    (A : ∀ j, Matrix (Fin (r j)) (Fin (r j)) ℝ)
    (v : (Σ j, Fin (r j)) → ℝ) (j : Fin d) (i : Fin (r j)) :
    (Matrix.blockDiagonal' A *ᵥ v) ⟨j, i⟩ = (A j *ᵥ (fun k => v ⟨j, k⟩)) i := by
  classical
  simp only [Matrix.mulVec, dotProduct, Fintype.sum_sigma]
  rw [Fintype.sum_eq_single j]
  · simp only [Matrix.blockDiagonal'_apply_eq]
  · intro k hk
    apply Finset.sum_eq_zero
    intro l _
    rw [Matrix.blockDiagonal'_apply_ne A i l hk.symm, zero_mul]

theorem dotProduct_blockDiagonal_mulVec {d : ℕ} {r : Fin d → ℕ}
    (A : ∀ j, Matrix (Fin (r j)) (Fin (r j)) ℝ)
    (u v : (Σ j, Fin (r j)) → ℝ) :
    u ⬝ᵥ (Matrix.blockDiagonal' A *ᵥ v) =
      ∑ j, (fun i => u ⟨j, i⟩) ⬝ᵥ (A j *ᵥ fun i => v ⟨j, i⟩) := by
  simp only [dotProduct, Fintype.sum_sigma, blockDiagonal_mulVec_apply]

theorem blockGradient_quadratic {d : ℕ} {r : Fin d → ℕ}
    (A : ∀ j, Matrix (Fin (r j)) (Fin (r j)) ℝ) (b : Fin d → ℝ)
    (u v : (Σ j, Fin (r j)) → ℝ) :
    u ⬝ᵥ (blockGradient A b *ᵥ v) =
      ∑ j, b j * ((fun i => u ⟨j, i⟩) ⬝ᵥ ((A j)⁻¹ *ᵥ fun i => v ⟨j, i⟩)) := by
  rw [blockGradient, dotProduct_blockDiagonal_mulVec]
  simp only [Matrix.smul_mulVec, dotProduct_smul, smul_eq_mul]

theorem blockGradient_symmetric {d : ℕ} {r : Fin d → ℕ}
    (A : ∀ j, Matrix (Fin (r j)) (Fin (r j)) ℝ) (b : Fin d → ℝ)
    (hA : ∀ j, (A j).PosDef) :
    (blockGradient A b).transpose = blockGradient A b := by
  unfold blockGradient
  rw [Matrix.blockDiagonal'_transpose]
  apply congrArg Matrix.blockDiagonal'
  funext j
  rw [Matrix.transpose_smul]
  congr 1
  simpa only [Matrix.conjTranspose_eq_transpose_of_trivial] using
    (hA j).posSemidef.inv.isHermitian.eq

noncomputable def determinantProductHessianValue {d : ℕ} {r : Fin d → ℕ}
    (A H J : ∀ j, Matrix (Fin (r j)) (Fin (r j)) ℝ) (b : Fin d → ℝ) : ℝ :=
  determinantProductValue A b *
    ((∑ j, b j * ((A j)⁻¹ * H j).trace) *
      (∑ j, b j * ((A j)⁻¹ * J j).trace) -
        ∑ j, b j * ((A j)⁻¹ * J j * (A j)⁻¹ * H j).trace)

theorem determinantProductHessianValue_derivative {d : ℕ} {r : Fin d → ℕ}
    (A H J : ∀ j, Matrix (Fin (r j)) (Fin (r j)) ℝ) (b : Fin d → ℝ)
    (hA : ∀ j, (A j).PosDef) :
    HasDerivAt (fun t : ℝ => determinantProductDirectional
      (fun j => A j + t • J j) H b) (determinantProductHessianValue A H J b) 0 :=
  determinant_product_hessian_directional A H J b (fun j => (hA j).det_pos)

theorem determinantProductHessianValue_rankTwo {d : ℕ} {r : Fin d → ℕ}
    (A : ∀ j, Matrix (Fin (r j)) (Fin (r j)) ℝ)
    (b : Fin d → ℝ) (hA : ∀ j, (A j).PosDef)
    (u v : (Σ j, Fin (r j)) → ℝ) :
    determinantProductHessianValue A
      (fun j => rankTwoDirection (fun k => u ⟨j, k⟩) (fun k => v ⟨j, k⟩))
      (fun j => rankTwoDirection (fun k => u ⟨j, k⟩) (fun k => v ⟨j, k⟩)) b =
    determinantProductValue A b *
      ((u ⬝ᵥ (blockGradient A b *ᵥ v)) ^ 2 -
        ∑ j, b j * ((A j)⁻¹ *
          rankTwoDirection (fun k => u ⟨j, k⟩) (fun k => v ⟨j, k⟩) * (A j)⁻¹ *
          rankTwoDirection (fun k => u ⟨j, k⟩) (fun k => v ⟨j, k⟩)).trace) := by
  have hG : ∀ j, ((A j)⁻¹).transpose = (A j)⁻¹ := by
    intro j
    simpa only [Matrix.conjTranspose_eq_transpose_of_trivial] using
      (hA j).posSemidef.inv.isHermitian.eq
  unfold determinantProductHessianValue
  simp_rw [trace_rankTwoDirection _ (hG _)]
  rw [blockGradient_quadratic, pow_two]

theorem differentialOperatorMatrix_quadratic {d : ℕ} {r : Fin d → ℕ}
    (A : ∀ j, Matrix (Fin (r j)) (Fin (r j)) ℝ)
    (W : Matrix (Σ j, Fin (r j)) (Σ j, Fin (r j)) ℝ)
    (b : Fin d → ℝ) (q : ℝ) (v : (Σ j, Fin (r j)) → ℝ) :
    v ⬝ᵥ (differentialOperatorMatrix A W b q *ᵥ v) =
      q * (v ⬝ᵥ (blockGradient A b *ᵥ v)) +
      2 * (v ⬝ᵥ ((blockGradient A b * W * blockGradient A b) *ᵥ v)) -
      ∑ j, b j *
        (((fun i => v (⟨j, i⟩ : Σ j, Fin (r j))) ⬝ᵥ
          (((A j)⁻¹ * principalBlock W j * (A j)⁻¹) *ᵥ fun i => v ⟨j, i⟩)) +
          ((A j)⁻¹ * principalBlock W j).trace *
            ((fun i => v ⟨j, i⟩) ⬝ᵥ ((A j)⁻¹ *ᵥ fun i => v ⟨j, i⟩))) := by
  unfold differentialOperatorMatrix
  rw [Matrix.add_mulVec, dotProduct_add, Matrix.smul_mulVec, dotProduct_smul,
    dotProduct_blockDiagonal_mulVec, blockGradient_quadratic]
  simp only [Matrix.smul_mulVec, Matrix.sub_mulVec, dotProduct_smul, dotProduct_sub,
    smul_eq_mul]
  rw [Finset.mul_sum]
  have he : ∀ j, b j *
      ((q - ((A j)⁻¹ * principalBlock W j).trace) *
        ((fun i => v ⟨j, i⟩) ⬝ᵥ ((A j)⁻¹ *ᵥ fun i => v ⟨j, i⟩)) -
          ((fun i => v ⟨j, i⟩) ⬝ᵥ
            (((A j)⁻¹ * principalBlock W j * (A j)⁻¹) *ᵥ fun i => v ⟨j, i⟩))) =
      q * (b j * ((fun i => v ⟨j, i⟩) ⬝ᵥ ((A j)⁻¹ *ᵥ fun i => v ⟨j, i⟩))) -
        b j * (((fun i => v ⟨j, i⟩) ⬝ᵥ
          (((A j)⁻¹ * principalBlock W j * (A j)⁻¹) *ᵥ fun i => v ⟨j, i⟩)) +
            ((A j)⁻¹ * principalBlock W j).trace *
              ((fun i => v ⟨j, i⟩) ⬝ᵥ ((A j)⁻¹ *ᵥ fun i => v ⟨j, i⟩))) := by
    intro j
    ring
  simp_rw [he]
  rw [Finset.sum_sub_distrib]
  ring

theorem determinant_product_operator_contraction {d : ℕ} {r : Fin d → ℕ}
    {κ : Type*} [Fintype κ]
    (A : ∀ j, Matrix (Fin (r j)) (Fin (r j)) ℝ)
    (b : Fin d → ℝ) (q : ℝ) (hA : ∀ j, (A j).PosDef)
    (U : κ → (Σ j, Fin (r j)) → ℝ) (v : (Σ j, Fin (r j)) → ℝ) :
    q * determinantProductDirectional A
        (fun j => Matrix.vecMulVec (fun k => v ⟨j, k⟩) (fun k => v ⟨j, k⟩)) b +
      2 * ∑ i, determinantProductHessianValue A
        (fun j => rankTwoDirection (fun k => U i ⟨j, k⟩) (fun k => v ⟨j, k⟩))
        (fun j => rankTwoDirection (fun k => U i ⟨j, k⟩) (fun k => v ⟨j, k⟩)) b =
      determinantProductValue A b *
        (v ⬝ᵥ (differentialOperatorMatrix A (gramSum U) b q *ᵥ v)) := by
  classical
  have hG : ∀ j, ((A j)⁻¹).transpose = (A j)⁻¹ := by
    intro j
    simpa only [Matrix.conjTranspose_eq_transpose_of_trivial] using
      (hA j).posSemidef.inv.isHermitian.eq
  simp_rw [determinantProductHessianValue_rankTwo A b hA]
  unfold determinantProductDirectional
  simp_rw [trace_matrix_outer]
  rw [← blockGradient_quadratic, ← Finset.mul_sum, Finset.sum_sub_distrib,
    ← quadratic_gramSum _ (blockGradient_symmetric A b hA), Finset.sum_comm]
  have hs : (∑ j, ∑ i, b j *
      ((A j)⁻¹ * rankTwoDirection (fun k => U i ⟨j, k⟩) (fun k => v ⟨j, k⟩) *
        (A j)⁻¹ * rankTwoDirection (fun k => U i ⟨j, k⟩) (fun k => v ⟨j, k⟩)).trace) =
      (∑ j, b j *
        (((fun k => v ⟨j, k⟩) ⬝ᵥ
          (((A j)⁻¹ * principalBlock (gramSum U) j * (A j)⁻¹) *ᵥ fun k => v ⟨j, k⟩)) +
          ((A j)⁻¹ * principalBlock (gramSum U) j).trace *
            ((fun k => v ⟨j, k⟩) ⬝ᵥ ((A j)⁻¹ *ᵥ fun k => v ⟨j, k⟩)))) / 2 := by
    rw [Finset.sum_div]
    apply Finset.sum_congr rfl
    intro j _
    rw [← Finset.mul_sum, rankTwo_hessian_sum _ (hG j)]
    simp only [principalBlock, gramSum_submatrix]
    ring
  rw [hs, differentialOperatorMatrix_quadratic]
  ring

theorem determinant_product_operator_nonneg {d : ℕ} {r : Fin d → ℕ}
    {κ : Type*} [Fintype κ]
    (A : ∀ j, Matrix (Fin (r j)) (Fin (r j)) ℝ)
    (b : Fin d → ℝ) (q : ℝ) (hA : ∀ j, (A j).PosDef)
    (U : κ → (Σ j, Fin (r j)) → ℝ) (v : (Σ j, Fin (r j)) → ℝ)
    (hWA : ∀ j, principalBlock (gramSum U) j ≤ A j)
    (hb : ∀ j, 0 ≤ b j) (hq : ∀ j, (r j : ℝ) + 1 ≤ q) :
    0 ≤ q * determinantProductDirectional A
        (fun j => Matrix.vecMulVec (fun k => v ⟨j, k⟩) (fun k => v ⟨j, k⟩)) b +
      2 * ∑ i, determinantProductHessianValue A
        (fun j => rankTwoDirection (fun k => U i ⟨j, k⟩) (fun k => v ⟨j, k⟩))
        (fun j => rankTwoDirection (fun k => U i ⟨j, k⟩) (fun k => v ⟨j, k⟩)) b := by
  rw [determinant_product_operator_contraction A b q hA]
  have hF : 0 ≤ determinantProductValue A b := by
    apply Finset.prod_nonneg
    intro j _
    exact (Real.rpow_pos_of_pos (hA j).det_pos _).le
  have hR := differentialOperatorMatrix_positiveSemidefinite A (gramSum U) b q hA
    (gramSum_positiveSemidefinite U) hWA hb hq
  apply mul_nonneg hF
  simpa only [star_trivial] using hR.dotProduct_mulVec_nonneg v

end ResearchMain.WishartBlocks
