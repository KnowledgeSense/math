import MainTheorems.WishartBlocks.OperatorPositivity
import Mathlib.Data.Matrix.Block

namespace ResearchMain.WishartBlocks

open scoped MatrixOrder

theorem blockDiagonal_positiveSemidefinite {d : ℕ} {r : Fin d → ℕ}
    (A : ∀ j, Matrix (Fin (r j)) (Fin (r j)) ℝ) (hA : ∀ j, (A j).PosSemidef) :
    (Matrix.blockDiagonal' A).PosSemidef := by
  let R := Matrix.blockDiagonal' fun j => CFC.sqrt (A j)
  have hR : ∀ j, (CFC.sqrt (A j)).PosSemidef := fun j =>
    Matrix.nonneg_iff_posSemidef.mp (CFC.sqrt_nonneg (A j))
  have hG : R * R.conjTranspose = Matrix.blockDiagonal' A := by
    change (Matrix.blockDiagonal' fun j => CFC.sqrt (A j)) *
      (Matrix.blockDiagonal' fun j => CFC.sqrt (A j)).conjTranspose = _
    rw [Matrix.blockDiagonal'_conjTranspose, ← Matrix.blockDiagonal'_mul]
    apply congrArg Matrix.blockDiagonal'
    funext j
    rw [(hR j).isHermitian.eq, CFC.sqrt_mul_sqrt_self (A j) (hA j).nonneg]
  simpa only [hG] using Matrix.posSemidef_self_mul_conjTranspose R

def principalBlock {d : ℕ} {r : Fin d → ℕ}
    (W : Matrix (Σ j, Fin (r j)) (Σ j, Fin (r j)) ℝ) (j : Fin d) :
    Matrix (Fin (r j)) (Fin (r j)) ℝ :=
  W.submatrix (fun i => ⟨j, i⟩) (fun i => ⟨j, i⟩)

noncomputable def blockGradient {d : ℕ} {r : Fin d → ℕ}
    (A : ∀ j, Matrix (Fin (r j)) (Fin (r j)) ℝ) (b : Fin d → ℝ) :
    Matrix (Σ j, Fin (r j)) (Σ j, Fin (r j)) ℝ :=
  Matrix.blockDiagonal' fun j => b j • (A j)⁻¹

noncomputable def differentialOperatorMatrix {d : ℕ} {r : Fin d → ℕ}
    (A : ∀ j, Matrix (Fin (r j)) (Fin (r j)) ℝ)
    (W : Matrix (Σ j, Fin (r j)) (Σ j, Fin (r j)) ℝ)
    (b : Fin d → ℝ) (q : ℝ) : Matrix (Σ j, Fin (r j)) (Σ j, Fin (r j)) ℝ :=
  Matrix.blockDiagonal' (fun j => b j •
    ((q - ((A j)⁻¹ * principalBlock W j).trace) • (A j)⁻¹ -
      (A j)⁻¹ * principalBlock W j * (A j)⁻¹)) +
    (2 : ℝ) • (blockGradient A b * W * blockGradient A b)

theorem differentialOperatorMatrix_positiveSemidefinite {d : ℕ} {r : Fin d → ℕ}
    (A : ∀ j, Matrix (Fin (r j)) (Fin (r j)) ℝ)
    (W : Matrix (Σ j, Fin (r j)) (Σ j, Fin (r j)) ℝ)
    (b : Fin d → ℝ) (q : ℝ)
    (hA : ∀ j, (A j).PosDef) (hW : W.PosSemidef)
    (hWA : ∀ j, principalBlock W j ≤ A j)
    (hb : ∀ j, 0 ≤ b j) (hq : ∀ j, (r j : ℝ) + 1 ≤ q) :
    (differentialOperatorMatrix A W b q).PosSemidef := by
  have hD : (blockGradient A b).PosSemidef :=
    blockDiagonal_positiveSemidefinite _ fun j => (hA j).posSemidef.inv.smul (hb j)
  have hDW : (blockGradient A b * W * blockGradient A b).PosSemidef := by
    simpa only [hD.isHermitian.eq] using hW.mul_mul_conjTranspose_same (blockGradient A b)
  apply Matrix.PosSemidef.add
  · apply blockDiagonal_positiveSemidefinite
    intro j
    exact determinant_block_operator_positiveSemidefinite (hA j)
      (hW.submatrix (fun i => ⟨j, i⟩)) (hWA j) (hq j) (hb j)
  · exact hDW.smul (by norm_num : (0 : ℝ) ≤ 2)

end ResearchMain.WishartBlocks
