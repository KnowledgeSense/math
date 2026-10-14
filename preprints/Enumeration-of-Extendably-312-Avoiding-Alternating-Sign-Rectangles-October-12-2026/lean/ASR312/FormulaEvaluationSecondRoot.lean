import ASR312.FormulaEvaluationShift
import ASR312.SeriesDiagonal
import ASR312.EnumerationSeriesDefinitions

noncomputable section
open PowerSeries
namespace ASR312

def secondRoot : PowerSeries ℚ := X*(1-X)⁻¹

@[simp] theorem secondRoot_constantCoeff : constantCoeff secondRoot=0 := by
  simp [secondRoot]

theorem one_add_secondRoot : 1+secondRoot=(1-X : PowerSeries ℚ)⁻¹ := by
  have hi := PowerSeries.inv_mul_cancel (1-X : PowerSeries ℚ) (by simp)
  unfold secondRoot
  linear_combination -hi

theorem secondRoot_equation : secondRoot=X*((1+X : PowerSeries ℚ).subst secondRoot) := by
  have hs : HasSubst secondRoot := HasSubst.of_constantCoeff_zero' secondRoot_constantCoeff
  have he : (1+X : PowerSeries ℚ).subst secondRoot=1+secondRoot := by
    rw [← coe_substAlgHom (R:=ℚ) hs,map_add,map_one,substAlgHom_X]
  rw [he,one_add_secondRoot]
  rfl

theorem B_subst_secondRoot_shift (a m : ℕ) :
    (B ((a:ℤ)-m)).subst secondRoot=((1-X : PowerSeries ℚ)⁻¹)^a*(1-X)^m := by
  have hs : HasSubst secondRoot := HasSubst.of_constantCoeff_zero' secondRoot_constantCoeff
  have hh := B_subst_shift_cleared a m secondRoot hs
  rw [one_add_secondRoot] at hh
  have hi := PowerSeries.inv_mul_cancel (1-X : PowerSeries ℚ) (by simp)
  calc
    _ = (B ((a:ℤ)-m)).subst secondRoot * (((1-X)⁻¹)^m*(1-X)^m) := by
      rw [← mul_pow,hi,one_pow,mul_one]
    _ = _ := by rw [← mul_assoc,hh]

def secondRootNumerator (a : ℕ) : PowerSeries ℚ :=
  C (1/2)*B ((a:ℤ)-2)+X*B ((a:ℤ)-1)*evenCatalanSeries.subst (X*(1+X))

theorem secondRootNumerator_subst (a : ℕ) :
    (secondRootNumerator a).subst secondRoot=P*U a*(1-X) := by
  have hs : HasSubst secondRoot := HasSubst.of_constantCoeff_zero' secondRoot_constantCoeff
  have hx : HasSubst (X*(1+X) : PowerSeries ℚ) := HasSubst.X'.mul_left
  have hi := PowerSeries.inv_mul_cancel (1-X : PowerSeries ℚ) (by simp)
  have he : (X*(1+X) : PowerSeries ℚ).subst secondRoot=catalanArgument := by
    rw [subst_mul hs,subst_X hs]
    have hh : (1+X : PowerSeries ℚ).subst secondRoot=1+secondRoot := by
      rw [← coe_substAlgHom (R:=ℚ) hs,map_add,map_one,substAlgHom_X]
    rw [hh,one_add_secondRoot]
    unfold secondRoot catalanArgument
    ring
  unfold secondRootNumerator
  rw [subst_add hs,subst_mul hs,subst_C,subst_mul hs,subst_mul hs,subst_X hs,
    subst_comp_subst_apply hx hs,he,evenCatalanSeries_argument]
  have hb2 := B_subst_secondRoot_shift a 2
  have hb1 := B_subst_secondRoot_shift a 1
  norm_num only [Nat.cast_ofNat] at hb2 hb1
  rw [hb2,hb1,U_eq_inv_one_sub_X_pow]
  simp only [pow_one]
  change C (1/2)*(((1-X : PowerSeries ℚ)⁻¹)^a*(1-X)^2) +
    secondRoot*(((1-X : PowerSeries ℚ)⁻¹)^a*(1-X))*(C (1/2)*(1-X)*(1+R)) =
    P*((1-X : PowerSeries ℚ)⁻¹)^a*(1-X)
  unfold secondRoot P
  linear_combination C (1/2)*((1-X : PowerSeries ℚ)⁻¹)^a*X*(1-X)*(1+R)*hi

theorem second_root_diagonal (a n : ℕ) :
    coeff n (secondRootNumerator a*(1+X)^n)=coeff n (P*U a) := by
  apply (diagonal_coefficient (1+X) (secondRootNumerator a) secondRoot (P*U a)
    (by simp) secondRoot_constantCoeff secondRoot_equation ?_ n).symm
  rw [secondRootNumerator_subst]
  have hs : HasSubst secondRoot := HasSubst.of_constantCoeff_zero' secondRoot_constantCoeff
  have hone : (1 : PowerSeries ℚ).subst secondRoot=1 := by
    simpa only [coe_substAlgHom] using (map_one (substAlgHom (R:=ℚ) hs))
  simp only [map_add,derivative_one,derivative_X,zero_add,hone,mul_one]

end ASR312
