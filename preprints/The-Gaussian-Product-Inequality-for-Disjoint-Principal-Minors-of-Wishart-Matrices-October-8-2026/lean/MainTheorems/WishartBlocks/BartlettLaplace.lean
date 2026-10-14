import MainTheorems.WishartBlocks.BartlettColumnLaplace
import Mathlib.Logic.Equiv.Fin.Basic

namespace ResearchMain.WishartBlocks

open MeasureTheory ProbabilityTheory Matrix
open scoped BigOperators InnerProductSpace

def tailIndex {p : ℕ} (k : ℕ) (i : Fin (p - k)) : Fin p :=
  ⟨k + i.val, by omega⟩

def tailMatrix {p : ℕ} (T : Matrix (Fin p) (Fin p) ℝ) (k : ℕ) :
    Matrix (Fin (p - k)) (Fin (p - k)) ℝ := T.submatrix (tailIndex k) (tailIndex k)

def columnTailEquiv {p : ℕ} (j : Fin p) :
    Fin 1 ⊕ Fin (p - (j.val + 1)) ≃ Fin (p - j.val) :=
  finSumFinEquiv.trans (finCongr (by have hj := j.isLt; omega))

theorem tailIndex_columnTailEquiv {p : ℕ} (j : Fin p)
    (i : Fin 1 ⊕ Fin (p - (j.val + 1))) :
    tailIndex j.val (columnTailEquiv j i) = columnInputIndex j i := by
  apply Fin.ext
  cases i with
  | inl i =>
      simp [tailIndex, columnTailEquiv, columnInputIndex]
  | inr i => simp [tailIndex, columnTailEquiv, columnInputIndex, belowColumnIndex,
      Nat.add_assoc]

theorem submatrix_one_add_smul {ι κ : Type*} [DecidableEq ι] [DecidableEq κ]
    (e : κ → ι) (he : Function.Injective e) (T : Matrix ι ι ℝ) (c : ℝ) :
    (1 + c • T).submatrix e e = 1 + c • T.submatrix e e := by
  ext i j
  simp [Matrix.submatrix_apply, Matrix.one_apply, he.eq_iff]

theorem tailMatrix_column_det {p : ℕ} (T : Matrix (Fin p) (Fin p) ℝ) (j : Fin p) :
    (1 + (2 : ℝ) • T.submatrix (columnInputIndex j) (columnInputIndex j)).det =
      (1 + (2 : ℝ) • tailMatrix T j.val).det := by
  have h : (1 + (2 : ℝ) • tailMatrix T j.val).submatrix
      (columnTailEquiv j) (columnTailEquiv j) =
      1 + (2 : ℝ) • T.submatrix (columnInputIndex j) (columnInputIndex j) := by
    rw [submatrix_one_add_smul _ (columnTailEquiv j).injective]
    congr 1
    ext i k
    simp [tailMatrix, Matrix.submatrix_apply, tailIndex_columnTailEquiv]
  rw [← h, Matrix.det_submatrix_equiv_self]

theorem trailingColumnMatrix_tail {p : ℕ} (T : Matrix (Fin p) (Fin p) ℝ) (j : Fin p) :
    trailingColumnMatrix T j = tailMatrix T (j.val + 1) := by
  ext i k
  rfl

noncomputable def tailPrecisionDet {p : ℕ} (T : Matrix (Fin p) (Fin p) ℝ) (k : ℕ) : ℝ :=
  (1 + (2 : ℝ) • tailMatrix T k).det

theorem tailPrecisionDet_pos {p : ℕ} {T : Matrix (Fin p) (Fin p) ℝ}
    (hT : T.PosSemidef) (k : ℕ) : 0 < tailPrecisionDet T k := by
  have hTail := hT.submatrix (tailIndex k)
  unfold tailPrecisionDet
  change 0 < (1 + (2 : ℝ) • T.submatrix (tailIndex k) (tailIndex k)).det
  rw [matrix_one_add_smul_det hTail.1]
  apply Finset.prod_pos
  intro i _
  have hEig := hTail.eigenvalues_nonneg i
  positivity

theorem tailPrecisionDet_zero {p : ℕ} (T : Matrix (Fin p) (Fin p) ℝ) :
    tailPrecisionDet T 0 = (1 + (2 : ℝ) • T).det := by
  have h : tailMatrix T 0 = T := by
    ext i j
    apply congrArg₂ T <;> apply Fin.ext <;> simp [tailIndex]
  rw [tailPrecisionDet, h]

theorem tailPrecisionDet_end {p : ℕ} (T : Matrix (Fin p) (Fin p) ℝ) :
    tailPrecisionDet T p = 1 := by
  simp [tailPrecisionDet, tailMatrix]

theorem rpow_product_telescope (D s : ℕ → ℝ) (hD : ∀ k, 0 < D k) (p : ℕ) :
    (∏ j ∈ Finset.range p, D j ^ (-s j) * D (j + 1) ^ s (j + 1)) =
      D 0 ^ (-s 0) * D p ^ s p := by
  induction p with
  | zero =>
      rw [Finset.prod_range_zero, Real.rpow_neg (hD 0).le]
      simp [(Real.rpow_pos_of_pos (hD 0) (s 0)).ne']
  | succ p ih =>
      rw [Finset.prod_range_succ, ih, Real.rpow_neg (hD p).le]
      have hn := (Real.rpow_pos_of_pos (hD p) (s p)).ne'
      field_simp [hn]

theorem bartlett_gram_laplace {p : ℕ} {α : ℝ}
    (hα : (p : ℝ) - 1 < α) {T : Matrix (Fin p) (Fin p) ℝ}
    (hT : T.PosSemidef) :
    ∫ x, Real.exp (-Matrix.trace (T * (bartlettMatrix x * (bartlettMatrix x).transpose)))
        ∂(bartlettMeasure p α) = (1 + (2 : ℝ) • T).det ^ (-α / 2) := by
  rw [bartlett_gram_laplace_product hα]
  simp_rw [bartlett_column_laplace hα hT, tailMatrix_column_det,
    trailingColumnMatrix_tail]
  let s : ℕ → ℝ := fun k => (α - (k : ℝ)) / 2
  have hs (j : Fin p) : (α - (j.val : ℝ)) / 2 - (1 / 2 : ℝ) = s (j.val + 1) := by
    dsimp [s]
    push_cast
    ring
  simp_rw [hs, neg_div]
  change (∏ j : Fin p, tailPrecisionDet T j.val ^ (-s j.val) *
      tailPrecisionDet T (j.val + 1) ^ s (j.val + 1)) = _
  rw [← Finset.prod_range (fun k : ℕ =>
    tailPrecisionDet T k ^ (-s k) * tailPrecisionDet T (k + 1) ^ s (k + 1)),
    rpow_product_telescope _ _ (tailPrecisionDet_pos hT),
    tailPrecisionDet_zero, tailPrecisionDet_end]
  simp [s]

end ResearchMain.WishartBlocks
