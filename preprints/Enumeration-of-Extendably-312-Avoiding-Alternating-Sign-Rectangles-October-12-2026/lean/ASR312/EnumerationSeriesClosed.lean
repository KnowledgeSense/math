import ASR312.EnumerationSeriesBalanced

namespace ASR312

open PowerSeries

theorem U_subst_XR (a : ℕ) : (U a).subst (X*R) = ((1-X*R : PowerSeries ℚ)⁻¹)^a := by
  have hsub : HasSubst (X*R) := HasSubst.X'.mul_left
  have hh := congrArg (substAlgHom hsub) (U_mul_one_sub_X_pow a)
  simp only [map_mul,map_pow,map_sub,map_one,coe_substAlgHom,subst_X hsub] at hh
  have hinv := PowerSeries.mul_inv_cancel (1-X*R : PowerSeries ℚ) (by simp)
  calc
    (U a).subst (X*R) = (U a).subst (X*R) * ((1-X*R)^a * ((1-X*R)⁻¹)^a) := by
      rw [← mul_pow,hinv,one_pow,mul_one]
    _ = ((1-X*R)⁻¹)^a := by rw [← mul_assoc,hh,one_mul]

/-- The complete diagonal-excess generating series of the original extendable
rectangle counts, obtained from all three literal-object recurrence faces. -/
theorem T_closed_form (a b : ℕ) :
    T a b = P*(U a+R^b*((1-X*R : PowerSeries ℚ)⁻¹)^a) := by
  rw [T_width_solution,T_balanced_series,U_subst_XR]
  ring

theorem T_closed_form_inverses (a b : ℕ) :
    T a b = P*(((1-X : PowerSeries ℚ)⁻¹)^a+R^b*((1-X*R : PowerSeries ℚ)⁻¹)^a) := by
  rw [T_closed_form,U_eq_inv_one_sub_X_pow]

theorem S_coefficient_closed_form (r k d : ℕ) (hdr : d ≤ r) (hdk : d ≤ k) :
    (S r k d : ℚ) = coeff d
      (P*(((1-X : PowerSeries ℚ)⁻¹)^(r-d)+R^(k-d)*((1-X*R : PowerSeries ℚ)⁻¹)^(r-d))) := by
  have hh := congrArg (coeff d) (T_closed_form_inverses (r-d) (k-d))
  rw [coeff_T,Nat.add_sub_of_le hdr,Nat.add_sub_of_le hdk] at hh
  exact hh

end ASR312
