import OscillatoryRecurrence.Orthogonality
import Mathlib.LinearAlgebra.Matrix.SchurComplement

noncomputable section
open scoped BigOperators Matrix
open Polynomial
namespace OscillatoryRecurrence

 theorem squaredNorm_expansion (η : ℝ) (n : ℕ) :
    squaredNorm η n = moment η (n+n) +
      ∑ j : Fin n, lowerCoefficients η n j * moment η (n+j.val) := by
  simp only [squaredNorm, orthogonalPolynomial, map_add, map_sum,
    momentFunctional_X_pow, momentFunctional_monomial]

/-- The successive Hankel ratio is the bilinear squared norm. -/
 theorem hankel_successor (m : ℤ) (hm : m ≠ 0) (n : ℕ) :
    hankel ((m:ℝ)*Real.pi) (n+1) =
      hankel ((m:ℝ)*Real.pi) n * squaredNorm ((m:ℝ)*Real.pi) n := by
  let η : ℝ := (m:ℝ)*Real.pi
  let A := momentMatrix η n
  let B : Matrix (Fin n) (Fin 1) ℂ := fun a _ => moment η (a.val+n)
  let C : Matrix (Fin 1) (Fin n) ℂ := fun _ b => moment η (n+b.val)
  let D : Matrix (Fin 1) (Fin 1) ℂ := fun _ _ => moment η (n+n)
  have hu : IsUnit A := (Matrix.isUnit_iff_isUnit_det _).mpr
    (isUnit_iff_ne_zero.mpr (hankel_ne_zero m hm n))
  let : Invertible A := hu.invertible
  have hb : (momentMatrix η (n+1)).submatrix finSumFinEquiv finSumFinEquiv =
      Matrix.fromBlocks A B C D := by
    ext i j
    rcases i with i | i <;> rcases j with j | j
    · rfl
    · have hi : j = 0 := Subsingleton.elim _ _
      subst j
      rfl
    · have hi : i = 0 := Subsingleton.elim _ _
      subst i
      rfl
    · have hi : i = 0 := Subsingleton.elim _ _
      have hj : j = 0 := Subsingleton.elim _ _
      subst i; subst j
      rfl
  have hdet := Matrix.det_submatrix_equiv_self finSumFinEquiv (momentMatrix η (n+1))
  rw [hb, Matrix.det_fromBlocks₁₁, Matrix.det_fin_one,
    Matrix.invOf_eq_nonsing_inv] at hdet
  change (momentMatrix η (n+1)).det = A.det * squaredNorm η n
  rw [← hdet]
  congr 1
  rw [squaredNorm_expansion]
  change moment η (n+n) - (∑ j : Fin n,
    (∑ i : Fin n, moment η (n+i.val)*A⁻¹ i j)*moment η (j.val+n)) =
    moment η (n+n) + ∑ i : Fin n,
      (∑ j : Fin n, A⁻¹ i j * (-moment η (j.val+n)))*moment η (n+i.val)
  simp only [Finset.sum_mul, mul_neg, Finset.sum_neg_distrib, neg_mul]
  have hs : (∑ j : Fin n, ∑ i : Fin n,
      moment η (n+i.val)*A⁻¹ i j*moment η (j.val+n)) =
      ∑ i : Fin n, ∑ j : Fin n,
        A⁻¹ i j*moment η (j.val+n)*moment η (n+i.val) := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i hi
    apply Finset.sum_congr rfl
    intro j hj
    ring
  rw [hs, sub_eq_add_neg]

 theorem squaredNorm_hankel_ratio (m : ℤ) (hm : m ≠ 0) (n : ℕ) :
    squaredNorm ((m:ℝ)*Real.pi) n =
      hankel ((m:ℝ)*Real.pi) (n+1) / hankel ((m:ℝ)*Real.pi) n := by
  apply (eq_div_iff (hankel_ne_zero m hm n)).mpr
  simpa only [mul_comm] using (hankel_successor m hm n).symm

end OscillatoryRecurrence
