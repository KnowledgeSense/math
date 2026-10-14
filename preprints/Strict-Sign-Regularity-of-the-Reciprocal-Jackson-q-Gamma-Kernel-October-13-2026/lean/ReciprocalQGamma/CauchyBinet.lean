import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Tactic

noncomputable section
open scoped BigOperators
namespace ReciprocalQGamma

/-- A rectangular determinant expansion before collecting intermediate index sets. -/
theorem det_product_expansion {r m : ℕ} (A : Matrix (Fin r) (Fin m) ℝ)
    (B : Matrix (Fin m) (Fin r) ℝ) :
    (A * B).det = ∑ f : Fin r → Fin m,
      (A.submatrix id f).det * ∏ i, B (f i) i := by
  simp only [Matrix.det_apply', Matrix.mul_apply, Finset.prod_univ_sum, Finset.mul_sum,
    Fintype.piFinset_univ]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro f _
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro σ _
  simp only [Matrix.submatrix_apply, id_eq, Finset.prod_mul_distrib]
  ring

/-- Unordered Cauchy–Binet; the factorial counts all intermediate orderings. -/
theorem cauchyBinet_unordered {r m : ℕ} (A : Matrix (Fin r) (Fin m) ℝ)
    (B : Matrix (Fin m) (Fin r) ℝ) :
    (r.factorial : ℝ) * (A * B).det =
      ∑ f : Fin r → Fin m, (A.submatrix id f).det * (B.submatrix f id).det := by
  rw [det_product_expansion]
  symm
  simp only [Matrix.det_apply' (B.submatrix _ _), Matrix.submatrix_apply, id_eq,
    Finset.mul_sum]
  rw [Finset.sum_comm]
  have hterm : ∀ σ : Equiv.Perm (Fin r),
      (∑ f : Fin r → Fin m, (A.submatrix id f).det *
        ((Equiv.Perm.sign σ : ℤ) : ℝ) * ∏ i, B (f (σ i)) i) =
      ∑ f : Fin r → Fin m, (A.submatrix id f).det * ∏ i, B (f i) i := by
    intro σ
    let e : (Fin r → Fin m) ≃ (Fin r → Fin m) := Equiv.arrowCongr σ (Equiv.refl _)
    rw [← e.sum_comp (fun f => (A.submatrix id f).det *
      ((Equiv.Perm.sign σ : ℤ) : ℝ) * ∏ i, B (f (σ i)) i)]
    apply Finset.sum_congr rfl
    intro f _
    have he : e f = fun i => f (σ⁻¹ i) := rfl
    rw [he]
    simp only [Equiv.Perm.coe_inv, Equiv.symm_apply_apply]
    have hd := Matrix.det_permute' σ⁻¹ (A.submatrix id f)
    change (A.submatrix id (fun i => f (σ⁻¹ i))).det = _ at hd
    simp only [Equiv.Perm.coe_inv] at hd
    rw [hd, Equiv.Perm.sign_inv]
    have hs : (((Equiv.Perm.sign σ : ℤ) : ℝ)) * ((Equiv.Perm.sign σ : ℤ) : ℝ) = 1 := by
      have h := congrArg (fun u : ℤˣ => ((u : ℤ) : ℝ)) (Int.units_mul_self (Equiv.Perm.sign σ))
      simpa only [Units.val_mul, Int.cast_mul, Units.val_one, Int.cast_one] using h
    calc
      _ = (((Equiv.Perm.sign σ : ℤ) : ℝ) * ((Equiv.Perm.sign σ : ℤ) : ℝ)) *
        ((A.submatrix id f).det * ∏ i, B (f i) i) := by ring
      _ = _ := by rw [hs, one_mul]
  simp_rw [← mul_assoc, hterm]
  simp [Fintype.card_perm, Finset.mul_sum, mul_assoc]

end ReciprocalQGamma
