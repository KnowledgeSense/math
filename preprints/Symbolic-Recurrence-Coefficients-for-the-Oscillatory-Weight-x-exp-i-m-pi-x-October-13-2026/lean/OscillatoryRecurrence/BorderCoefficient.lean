import OscillatoryRecurrence.Orthogonality

noncomputable section
open scoped BigOperators Matrix
open Polynomial
namespace OscillatoryRecurrence

 theorem orthogonalPolynomial_lower_coeff (η : ℝ) (n : ℕ) (j : Fin n) :
    (orthogonalPolynomial η n).coeff j.val = lowerCoefficients η n j := by
  simp only [orthogonalPolynomial, Polynomial.coeff_add, Polynomial.finsetSum_coeff,
    Polynomial.coeff_X_pow, Polynomial.coeff_monomial]
  have hn : ¬j.val=n := ne_of_lt j.is_lt
  simp only [hn, ite_false, zero_add]
  have he : ∀ i : Fin n, i.val=j.val ↔ i=j := fun _ => Fin.ext_iff.symm
  simp_rw [he]
  simp

 theorem border_updateCol (η : ℝ) (n : ℕ) :
    ((momentMatrix η (n+1)).updateCol (Fin.last n)
      (fun a => moment η (a.val+(n+1)))).det = borderedHankel η (n+1) := by
  unfold borderedHankel
  rw [ite_eq_right (Nat.succ_ne_zero n)]
  congr 1
  ext a b
  simp only [Matrix.updateCol_apply, momentMatrix, borderColumn]
  have he : b = Fin.last n ↔ b.val+1=n+1 := by
    rw [Fin.ext_iff]
    simp only [Fin.val_last]
    omega
  simp only [he]
  split_ifs <;> rfl

 theorem subleading_border_ratio (m : ℤ) (hm : m ≠ 0) (n : ℕ) :
    (orthogonalPolynomial ((m:ℝ)*Real.pi) (n+1)).coeff n =
      -borderedHankel ((m:ℝ)*Real.pi) (n+1) /
        hankel ((m:ℝ)*Real.pi) (n+1) := by
  let η : ℝ := (m:ℝ)*Real.pi
  have hunit : IsUnit (momentMatrix η (n+1)).det :=
    isUnit_iff_ne_zero.mpr (hankel_ne_zero m hm (n+1))
  have hc := congrFun (Matrix.det_smul_inv_mulVec_eq_cramer
    (momentMatrix η (n+1)) (fun a : Fin (n+1) => moment η (a.val+(n+1)))
    hunit) (Fin.last n)
  rw [Matrix.cramer_apply, border_updateCol] at hc
  change (orthogonalPolynomial η (n+1)).coeff (Fin.last n).val = _
  rw [orthogonalPolynomial_lower_coeff]
  apply (eq_div_iff (hankel_ne_zero m hm (n+1))).mpr
  change (lowerCoefficients η (n+1) (Fin.last n))*hankel η (n+1) =
    -borderedHankel η (n+1)
  change (hankel η (n+1))*
    ((momentMatrix η (n+1))⁻¹.mulVec (fun a => moment η (a.val+(n+1))) (Fin.last n)) =
    borderedHankel η (n+1) at hc
  unfold lowerCoefficients
  change ((momentMatrix η (n+1))⁻¹.mulVec
    (-(fun a : Fin (n+1) => moment η (a.val+(n+1))))) (Fin.last n)*_ = _
  rw [Matrix.mulVec_neg]
  simp only [Pi.neg_apply]
  rw [neg_mul, mul_comm, hc]

end OscillatoryRecurrence
