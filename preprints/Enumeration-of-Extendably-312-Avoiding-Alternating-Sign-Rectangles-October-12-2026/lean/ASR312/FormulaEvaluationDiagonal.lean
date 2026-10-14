import ASR312.FormulaEvaluationFirstRoot
import ASR312.FormulaEvaluationSecondRoot
import ASR312.EnumerationSeriesClosed

noncomputable section
open PowerSeries
namespace ASR312

theorem B_diagonal_shift (a d : ℕ) (m : ℤ) :
    B (((d+a:ℕ):ℤ)-m)=B ((a:ℤ)-m)*(1+X)^d := by
  have h := B_add ((a:ℤ)-m) (d:ℤ)
  rw [B_nat] at h
  convert h using 1
  congr 1
  push_cast
  ring

theorem formulaSeries_diagonal (a b d : ℕ) :
    formulaSeries (d+a) (d+b)=
      firstRootNumerator a b*((1+X)*(1+2*X))^d+
      secondRootNumerator a*(1+X)^d := by
  rw [formulaSeries_closed,B_diagonal_shift a d 2,B_diagonal_shift a d 1]
  simp only [map_ofNat,pow_add,mul_pow]
  unfold firstRootNumerator secondRootNumerator
  ring

theorem F_diagonal_coefficient (a b d : ℕ) :
    (F (d+a) (d+b) d : ℚ)=coeff d
      (P*(((1-X : PowerSeries ℚ)⁻¹)^a+R^b*((1-X*R : PowerSeries ℚ)⁻¹)^a)) := by
  rw [← formulaSeries_coeff,formulaSeries_diagonal,map_add,first_root_diagonal,second_root_diagonal,
    U_eq_inv_one_sub_X_pow]
  rw [← map_add]
  congr 1
  ring

/-- The full three-parameter formula for actual alternating-sign rectangles
admitting an avoiding square extension, on every admissible dimension. -/
theorem full_enumeration (r k d : ℕ) (hdr : d ≤ r) (hdk : d ≤ k) :
    (S r k d : ℤ)=F r k d := by
  have hs := S_coefficient_closed_form r k d hdr hdk
  have hf := F_diagonal_coefficient (r-d) (k-d) d
  rw [Nat.add_sub_of_le hdr,Nat.add_sub_of_le hdk] at hf
  have he : (S r k d : ℚ)=(F r k d : ℚ) := hs.trans hf.symm
  exact_mod_cast he

theorem fullEnumeration : FullEnumeration := full_enumeration

end ASR312
