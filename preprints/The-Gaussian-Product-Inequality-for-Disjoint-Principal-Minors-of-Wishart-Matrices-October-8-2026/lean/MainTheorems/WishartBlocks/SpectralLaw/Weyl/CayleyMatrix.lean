import MainTheorems.WishartBlocks.SpectralLaw.Weyl.CayleyCoverage
import Mathlib.LinearAlgebra.Matrix.ToLinearEquiv
import Mathlib.LinearAlgebra.Matrix.DotProduct

namespace ResearchMain.WishartBlocks.Weyl

open scoped Matrix

theorem skew_dotProduct_mulVec_self {n : ℕ}
    {K : Matrix (Fin n) (Fin n) ℝ} (hK : K.transpose = -K) (v : Fin n → ℝ) :
    v ⬝ᵥ (K *ᵥ v) = 0 := by
  have h := Matrix.dotProduct_transpose_mulVec K v v
  rw [hK, Matrix.neg_mulVec, dotProduct_neg] at h
  linarith

theorem one_sub_skew_det_ne_zero {n : ℕ}
    {K : Matrix (Fin n) (Fin n) ℝ} (hK : K.transpose = -K) :
    (1 - K).det ≠ 0 := by
  intro hdet
  obtain ⟨v, hv, hzero⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr hdet
  have hquad := skew_dotProduct_mulVec_self hK v
  have h := congrArg (fun w : Fin n → ℝ => v ⬝ᵥ w) hzero
  rw [Matrix.sub_mulVec, Matrix.one_mulVec, dotProduct_sub,
    dotProduct_zero, hquad, sub_zero] at h
  exact hv (dotProduct_self_eq_zero.mp h)

noncomputable def cayleyMatrix {n : ℕ} (K : Matrix (Fin n) (Fin n) ℝ) :
    Matrix (Fin n) (Fin n) ℝ := (1 - K)⁻¹ * (1 + K)

theorem cayleyMatrix_mem {n : ℕ}
    {K : Matrix (Fin n) (Fin n) ℝ} (hK : K.transpose = -K) :
    cayleyMatrix K ∈ Matrix.orthogonalGroup (Fin n) ℝ := by
  have hminus : IsUnit (1 - K).det := isUnit_iff_ne_zero.mpr (one_sub_skew_det_ne_zero hK)
  have htranspose : (1 - K).transpose = 1 + K := by simp [hK, sub_eq_add_neg]
  have htranspose' : (1 + K).transpose = 1 - K := by simp [hK, sub_eq_add_neg]
  have hplus : IsUnit (1 + K).det := by
    rw [← htranspose, Matrix.det_transpose]
    exact hminus
  have hcomm : (1 + K) * (1 - K) = (1 - K) * (1 + K) := by noncomm_ring
  rw [Matrix.mem_orthogonalGroup_iff, cayleyMatrix, Matrix.transpose_mul,
    Matrix.transpose_nonsing_inv, htranspose, htranspose']
  calc
    (1 - K)⁻¹ * (1 + K) * ((1 - K) * (1 + K)⁻¹) =
      ((1 - K)⁻¹ * ((1 + K) * (1 - K))) * (1 + K)⁻¹ := by
        simp only [Matrix.mul_assoc]
    _ = ((1 - K)⁻¹ * ((1 - K) * (1 + K))) * (1 + K)⁻¹ := by rw [hcomm]
    _ = 1 := by
      rw [← Matrix.mul_assoc (1 - K)⁻¹, Matrix.nonsing_inv_mul _ hminus,
        Matrix.one_mul, Matrix.mul_nonsing_inv _ hplus]

noncomputable def cayleyOrthogonalMatrix {n : ℕ} (z : LowerIndex n → ℝ) :
    Matrix.orthogonalGroup (Fin n) ℝ :=
  ⟨cayleyMatrix (skewMatrix z), cayleyMatrix_mem (skewMatrix_transpose z)⟩

@[simp] theorem cayleyMatrix_zero (n : ℕ) :
    cayleyMatrix (0 : Matrix (Fin n) (Fin n) ℝ) = 1 := by
  simp [cayleyMatrix]

@[simp] theorem cayleyOrthogonalMatrix_zero (n : ℕ) :
    cayleyOrthogonalMatrix (0 : LowerIndex n → ℝ) = 1 := by
  apply Subtype.ext
  simp [cayleyOrthogonalMatrix]

end ResearchMain.WishartBlocks.Weyl
