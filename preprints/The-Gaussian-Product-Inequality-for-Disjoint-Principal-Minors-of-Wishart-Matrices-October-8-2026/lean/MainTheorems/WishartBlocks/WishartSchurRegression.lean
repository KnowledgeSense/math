import MainTheorems.WishartBlocks.WishartRegressionLaw
import Mathlib.LinearAlgebra.Matrix.PosDef

namespace ResearchMain.WishartBlocks

open MeasureTheory ProbabilityTheory Matrix
open scoped MatrixOrder

def principalCross {k m : ℕ} (S₀ : Matrix (Fin (k + m)) (Fin (k + m)) ℝ) :
    Matrix (Fin k) (Fin m) ℝ :=
  S₀.submatrix (fun i => finSumFinEquiv (Sum.inl i)) (fun j => finSumFinEquiv (Sum.inr j))

noncomputable def regressionCoefficient {k m : ℕ}
    (S₀ : Matrix (Fin (k + m)) (Fin (k + m)) ℝ) : Matrix (Fin k) (Fin m) ℝ :=
  ((principalPair S₀).1)⁻¹ * principalCross S₀

noncomputable def schurCovariance {k m : ℕ}
    (S₀ : Matrix (Fin (k + m)) (Fin (k + m)) ℝ) : Matrix (Fin m) (Fin m) ℝ :=
  (principalPair S₀).2 - (principalCross S₀).transpose *
    ((principalPair S₀).1)⁻¹ * principalCross S₀

theorem positive_covariance_blocks {k m : ℕ}
    {S₀ : Matrix (Fin (k + m)) (Fin (k + m)) ℝ} (hS₀ : S₀.PosSemidef) :
    S₀.submatrix finSumFinEquiv finSumFinEquiv =
      Matrix.fromBlocks (principalPair S₀).1 (principalCross S₀)
        (principalCross S₀).transpose (principalPair S₀).2 := by
  have hΓ := hS₀.submatrix (finSumFinEquiv (m := k) (n := m))
  have hs : (S₀.submatrix finSumFinEquiv finSumFinEquiv).transpose =
      S₀.submatrix finSumFinEquiv finSumFinEquiv := by
    simpa only [Matrix.conjTranspose_eq_transpose_of_trivial] using hΓ.1.eq
  ext i j
  cases i with
  | inl i => cases j <;> rfl
  | inr i =>
    cases j with
    | inl j => exact congrFun (congrFun hs (Sum.inl j)) (Sum.inr i)
    | inr j => rfl

theorem schurCovariance_positiveDefinite {k m : ℕ}
    {S₀ : Matrix (Fin (k + m)) (Fin (k + m)) ℝ} (hS₀ : S₀.PosDef) :
    (schurCovariance S₀).PosDef := by
  let A := (principalPair (k := k) (m := m) S₀).1
  let B := principalCross S₀
  let D := (principalPair (k := k) (m := m) S₀).2
  have he : Function.Injective (fun i : Fin k => finSumFinEquiv (Sum.inl i : Fin k ⊕ Fin m)) :=
    finSumFinEquiv.injective.comp Sum.inl_injective
  have hA : A.PosDef := hS₀.submatrix he
  have hAdet : IsUnit A.det := isUnit_iff_ne_zero.mpr hA.det_pos.ne'
  let : Invertible A := A.invertibleOfIsUnitDet hAdet
  have hΓ : (Matrix.fromBlocks A B B.transpose D).PosDef := by
    rw [← positive_covariance_blocks hS₀.posSemidef]
    exact hS₀.submatrix finSumFinEquiv.injective
  have hS : (schurCovariance S₀).PosSemidef := by
    apply (Matrix.PosDef.fromBlocks₁₁ B D hA).mp
    simpa only [Matrix.conjTranspose_eq_transpose_of_trivial] using hΓ.posSemidef
  have hd : (Matrix.fromBlocks A B B.transpose D).det = A.det * (schurCovariance S₀).det := by
    rw [Matrix.det_fromBlocks₁₁, Matrix.invOf_eq_nonsing_inv]
    rfl
  apply hS.posDef_iff_det_ne_zero.mpr
  intro hz
  have hg := hΓ.det_pos.ne'
  apply hg
  rw [hd, hz, mul_zero]

theorem covariance_regression_factorization {k m : ℕ}
    {S₀ : Matrix (Fin (k + m)) (Fin (k + m)) ℝ} (hS₀ : S₀.PosDef) :
    regressionFiniteCovariance (principalPair S₀).1 (schurCovariance S₀)
      (regressionCoefficient S₀) = S₀ := by
  let A := (principalPair (k := k) (m := m) S₀).1
  let B := principalCross S₀
  let K := regressionCoefficient S₀
  have he : Function.Injective (fun i : Fin k => finSumFinEquiv (Sum.inl i : Fin k ⊕ Fin m)) :=
    finSumFinEquiv.injective.comp Sum.inl_injective
  have hA : A.PosDef := hS₀.submatrix he
  have hAdet : IsUnit A.det := isUnit_iff_ne_zero.mpr hA.det_pos.ne'
  have hAK : A * K = B := by
    dsimp only [K, regressionCoefficient]
    rw [← Matrix.mul_assoc,
      Matrix.mul_nonsing_inv _ hAdet, Matrix.one_mul]
  have hAt : A.transpose = A := by
    simpa only [Matrix.conjTranspose_eq_transpose_of_trivial] using hA.1.eq
  have hKA : K.transpose * A = B.transpose := by
    rw [← hAK, Matrix.transpose_mul, hAt]
  have hlast : schurCovariance S₀ + K.transpose * A * K = (principalPair S₀).2 := by
    rw [hKA]
    change (principalPair S₀).2 - B.transpose * A⁻¹ * B + B.transpose * (A⁻¹ * B) = _
    rw [Matrix.mul_assoc, sub_add_cancel]
  have hR : regressionCovariance A (schurCovariance S₀) K =
      S₀.submatrix finSumFinEquiv finSumFinEquiv := by
    rw [regressionCovariance, hlast, hAK, hKA, positive_covariance_blocks hS₀.posSemidef]
  change (regressionCovariance A (schurCovariance S₀) K).submatrix
    finSumFinEquiv.symm finSumFinEquiv.symm = S₀
  rw [hR]
  ext i j
  simp

theorem wishart_block_regression_general {k m : ℕ} {α : ℝ}
    (hα : ((k + m : ℕ) : ℝ) - 1 < α)
    {S₀ : Matrix (Fin (k + m)) (Fin (k + m)) ℝ} (hS₀ : S₀.PosDef) :
    (bartlettLaw α S₀).map (principalPair (k := k) (m := m)) =
      (regressionInputLaw (k := k) α (schurCovariance S₀)).map
        (regressionPairValue (principalPair S₀).1 (schurCovariance S₀) (regressionCoefficient S₀)) := by
  have hA := (principalPair_positiveSemidefinite (k := k) (m := m) hS₀.posSemidef).1
  have h := wishart_block_regression hα hA (schurCovariance_positiveDefinite hS₀)
    (regressionCoefficient S₀)
  rw [covariance_regression_factorization hS₀] at h
  exact h.symm

end ResearchMain.WishartBlocks
