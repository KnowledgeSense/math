import MainTheorems.WishartBlocks.SpectralLaw.SymmetricCoordinates
import MainTheorems.WishartBlocks.EigenvalueLattice
import Mathlib.LinearAlgebra.Matrix.ToLin

namespace ResearchMain.WishartBlocks.Weyl

open scoped BigOperators

noncomputable def skewMatrix {n : ℕ} (z : LowerIndex n → ℝ) :
    Matrix (Fin n) (Fin n) ℝ := fun i j =>
  if h : j < i then z ⟨toLex (i, j), h.le⟩
  else if h : i < j then -z ⟨toLex (j, i), h.le⟩ else 0

theorem skewMatrix_transpose {n : ℕ} (z : LowerIndex n → ℝ) :
    (skewMatrix z).transpose = -skewMatrix z := by
  ext i j
  rcases lt_trichotomy i j with h | h | h
  · simp [skewMatrix, h, not_lt_of_gt h]
  · subst j
    simp [skewMatrix]
  · simp [skewMatrix, h, not_lt_of_gt h]

@[simp] theorem skewMatrix_zero (n : ℕ) :
    skewMatrix (0 : LowerIndex n → ℝ) = 0 := by
  ext i j
  simp [skewMatrix]

noncomputable def skewLinearMap (n : ℕ) :
    (LowerIndex n → ℝ) →ₗ[ℝ] Matrix (Fin n) (Fin n) ℝ where
  toFun := skewMatrix
  map_add' z w := by
    ext i j
    simp only [skewMatrix, Matrix.add_apply, Pi.add_apply]
    split_ifs <;> ring
  map_smul' c z := by
    ext i j
    simp only [skewMatrix, Matrix.smul_apply, Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
    split_ifs <;> ring

noncomputable def diagonalCoordinates {n : ℕ} (z : LowerIndex n → ℝ) : Fin n → ℝ :=
  fun i => z ⟨toLex (i, i), le_refl i⟩

noncomputable def diagonalLinearMap (n : ℕ) :
    (LowerIndex n → ℝ) →ₗ[ℝ] Matrix (Fin n) (Fin n) ℝ where
  toFun z := Matrix.diagonal (diagonalCoordinates z)
  map_add' z w := by
    ext i j
    by_cases hij : i = j <;> simp [diagonalCoordinates, hij]
  map_smul' c z := by
    ext i j
    by_cases hij : i = j <;>
      simp [diagonalCoordinates, hij, RingHom.id_apply]

noncomputable def lowerLinearMap (n : ℕ) :
    Matrix (Fin n) (Fin n) ℝ →ₗ[ℝ] (LowerIndex n → ℝ) where
  toFun := symmetricCoordinates
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

noncomputable def tangentMatrix {n : ℕ} (lam : Fin n → ℝ) (z : LowerIndex n → ℝ) :
    Matrix (Fin n) (Fin n) ℝ :=
  Matrix.diagonal (diagonalCoordinates z) +
    skewMatrix z * Matrix.diagonal lam - Matrix.diagonal lam * skewMatrix z

noncomputable def spectralDerivative {n : ℕ} (lam : Fin n → ℝ) :
    (LowerIndex n → ℝ) →L[ℝ] (LowerIndex n → ℝ) :=
  ContinuousLinearMap.pi fun e =>
    (if e.val.1 = e.val.2 then 1 else lam e.val.2 - lam e.val.1) •
      ContinuousLinearMap.proj e

theorem tangentMatrix_lower_entry {n : ℕ} (lam : Fin n → ℝ)
    (z : LowerIndex n → ℝ) (e : LowerIndex n) :
    tangentMatrix lam z e.val.1 e.val.2 =
      (if e.val.1 = e.val.2 then 1 else lam e.val.2 - lam e.val.1) * z e := by
  simp only [tangentMatrix, Matrix.add_apply, Matrix.sub_apply,
    Matrix.mul_diagonal, Matrix.diagonal_mul]
  by_cases he : e.val.1 = e.val.2
  · have hdiag : (⟨toLex (e.val.2, e.val.2), le_refl _⟩ : LowerIndex n) = e :=
      Subtype.ext (Prod.ext he.symm rfl)
    simp [skewMatrix, diagonalCoordinates, he, hdiag]
  · have hlt : e.val.2 < e.val.1 := lt_of_le_of_ne e.property (Ne.symm he)
    simp [skewMatrix, he, hlt]
    ring

theorem tangentMatrix_coordinates {n : ℕ} (lam : Fin n → ℝ)
    (z : LowerIndex n → ℝ) :
    symmetricCoordinates (tangentMatrix lam z) = spectralDerivative lam z := by
  funext e
  exact tangentMatrix_lower_entry lam z e

theorem spectralDerivative_toMatrix {n : ℕ} (lam : Fin n → ℝ) :
    LinearMap.toMatrix' (spectralDerivative lam).toLinearMap =
      Matrix.diagonal (fun e : LowerIndex n =>
        if e.val.1 = e.val.2 then 1 else lam e.val.2 - lam e.val.1) := by
  ext e f
  rw [LinearMap.toMatrix'_apply]
  by_cases hef : e = f
  · subst f
    by_cases hdiag : e.val.1 = e.val.2 <;> simp [spectralDerivative, hdiag]
  · by_cases hdiag : e.val.1 = e.val.2 <;> simp [spectralDerivative, hdiag, hef]

theorem spectralDerivative_det {n : ℕ} (lam : Fin n → ℝ) :
    (LinearMap.toMatrix' (spectralDerivative lam).toLinearMap).det =
      ∏ e : LowerIndex n,
        if e.val.1 = e.val.2 then 1 else lam e.val.2 - lam e.val.1 := by
  rw [spectralDerivative_toMatrix, Matrix.det_diagonal]

theorem lower_gapProduct_eq {n : ℕ} (lam : Fin n → ℝ) :
    (∏ e : LowerIndex n,
      if e.val.1 = e.val.2 then 1 else lam e.val.1 - lam e.val.2) = gapProduct lam := by
  classical
  have hfilter : (∏ e : LowerIndex n,
      if e.val.1 = e.val.2 then 1 else lam e.val.1 - lam e.val.2) =
      ∏ e ∈ (Finset.univ : Finset (LowerIndex n)).filter (fun e => e.val.2 < e.val.1),
        (lam e.val.1 - lam e.val.2) := by
    rw [Finset.prod_filter]
    apply Finset.prod_congr rfl
    intro e _
    by_cases he : e.val.1 = e.val.2
    · simp [he]
    · have hlt := lt_of_le_of_ne e.property (Ne.symm he)
      simp [he, hlt]
  rw [hfilter]
  unfold gapProduct
  apply Finset.prod_bij (fun e _ => (e.val.2, e.val.1))
  · intro e he
    simpa only [Finset.mem_filter, Finset.mem_univ, true_and] using
      (Finset.mem_filter.mp he).2
  · intro e he f hf hef
    apply Subtype.ext
    exact Prod.ext (congrArg Prod.snd hef) (congrArg Prod.fst hef)
  · intro ij hij
    have hlt := (Finset.mem_filter.mp hij).2
    refine ⟨⟨toLex (ij.2, ij.1), hlt.le⟩, ?_, ?_⟩
    · simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      change ij.1 < ij.2
      exact hlt
    · rfl
  · intro e he
    rfl

theorem spectralDerivative_abs_det {n : ℕ} {lam : Fin n → ℝ} (hlam : StrictMono lam) :
    |(LinearMap.toMatrix' (spectralDerivative lam).toLinearMap).det| = gapProduct lam := by
  rw [spectralDerivative_det, Finset.abs_prod, ← lower_gapProduct_eq]
  apply Finset.prod_congr rfl
  intro e _
  by_cases he : e.val.1 = e.val.2
  · simp [he]
  · have hlt := hlam (lt_of_le_of_ne e.property (Ne.symm he))
    simp only [he, ite_false, abs_of_neg (sub_neg.mpr hlt), neg_sub]

theorem spectralDerivative_det_ne_zero {n : ℕ} {lam : Fin n → ℝ}
    (hlam : Function.Injective lam) :
    (LinearMap.toMatrix' (spectralDerivative lam).toLinearMap).det ≠ 0 := by
  rw [spectralDerivative_det]
  apply Finset.prod_ne_zero_iff.mpr
  intro e _
  split_ifs with he
  · exact one_ne_zero
  · exact sub_ne_zero.mpr (fun h => he (hlam h).symm)

end ResearchMain.WishartBlocks.Weyl
