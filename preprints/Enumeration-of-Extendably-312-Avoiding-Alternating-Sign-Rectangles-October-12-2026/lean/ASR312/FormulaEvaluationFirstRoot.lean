import ASR312.FormulaEvaluationShift
import ASR312.SeriesDiagonal

noncomputable section
open PowerSeries
namespace ASR312

private theorem two_series_ne_zero : (2:PowerSeries ℚ)≠0 := by
  intro h
  have hc := congrArg constantCoeff h
  rw [show (2:PowerSeries ℚ)=1+1 by ring] at hc
  simp at hc

def firstRoot : PowerSeries ℚ := C (1/2)*(R-1)

theorem firstRoot_twice : 2*firstRoot=R-1 := by
  unfold firstRoot
  linear_combination (R-1)*C_half_mul_two

@[simp] theorem constantCoeff_firstRoot : constantCoeff firstRoot=0 := by
  simp [firstRoot]

theorem firstRoot_relation : firstRoot=X*((1+firstRoot)*(1+2*firstRoot)) := by
  have ht := firstRoot_twice
  have hR := R_quadratic
  apply mul_left_cancel₀ two_series_ne_zero
  rw [show R=1+2*firstRoot by linear_combination -ht] at hR
  linear_combination hR

theorem firstRoot_inverse : 1+firstRoot=(1-X*R)⁻¹ := by
  have ht := firstRoot_twice
  have hq := one_sub_XR_mul_one_add_R
  have he : (1-X*R)*(1+firstRoot)=1 := by
    apply mul_left_cancel₀ two_series_ne_zero
    linear_combination hq + (1-X*R)*ht
  have hi : (1-X*R:PowerSeries ℚ)*(1-X*R)⁻¹=1 :=
    PowerSeries.mul_inv_cancel _ (by simp)
  exact mul_left_cancel₀ (by intro h; have := congrArg constantCoeff h; simp at this) (he.trans hi.symm)

theorem P_mul_firstRoot : P*(1+firstRoot)=C (1/2)*R := by
  have ht := firstRoot_twice
  have hp := P_mul_one_add_R
  apply mul_left_cancel₀ two_series_ne_zero
  linear_combination hp + P*ht - R*C_half_mul_two

theorem firstRoot_jacobian :
    (1+firstRoot)*R*(1-X*(3+4*firstRoot))=1-2*firstRoot^2 := by
  have hw := firstRoot_relation
  have ht := firstRoot_twice
  linear_combination (3+4*firstRoot)*hw -
    (1+firstRoot)*(1-X*(3+4*firstRoot))*ht

def firstRootNumerator (a b : ℕ) : PowerSeries ℚ :=
  C (1/2)*B ((a:ℤ)-2)*(1+2*X)^b*(1-2*X^2)

theorem first_root_diagonal (a b n : ℕ) :
    coeff n (firstRootNumerator a b*((1+X)*(1+2*X))^n)=
      coeff n (P*R^b*(1-X*R)⁻¹^a) := by
  have hw : HasSubst firstRoot := HasSubst.of_constantCoeff_zero' constantCoeff_firstRoot
  have hr : 1+2*firstRoot=R := by linear_combination firstRoot_twice
  have hy : (1+firstRoot:PowerSeries ℚ)≠0 := by
    intro h
    have hc := congrArg constantCoeff h
    simp at hc
  have hb := B_subst_shift_cleared a 2 firstRoot hw
  norm_num at hb
  have hsub : (firstRootNumerator a b).subst firstRoot=
      C (1/2)*(B ((a:ℤ)-2)).subst firstRoot*R^b*(1-2*firstRoot^2) := by
    unfold firstRootNumerator
    rw [← coe_substAlgHom (R:=ℚ) hw]
    simp only [map_mul,map_sub,map_add,map_pow,map_one,map_ofNat,
      coe_substAlgHom,subst_C,subst_X hw,hr]
    rfl
  have hder : (derivative ((1+X)*(1+2*X):PowerSeries ℚ)).subst firstRoot=
      3+4*firstRoot := by
    have hd2 : derivative (2:PowerSeries ℚ)=0 := by
      rw [show (2:PowerSeries ℚ)=1+1 by ring]
      simp
    have he : derivative ((1+X)*(1+2*X):PowerSeries ℚ)=3+4*X := by
      simp only [Derivation.leibniz,map_add,derivative_one,derivative_X,
        smul_eq_mul,hd2]
      ring
    rw [he,← coe_substAlgHom (R:=ℚ) hw]
    simp only [map_add,map_mul,map_ofNat,coe_substAlgHom,subst_X hw]
  have ht : (P*R^b*(1-X*R)⁻¹^a)*
      (1-X*(derivative ((1+X)*(1+2*X):PowerSeries ℚ)).subst firstRoot)=
      (firstRootNumerator a b).subst firstRoot := by
    rw [hder,hsub,← firstRoot_inverse]
    apply mul_right_cancel₀ (pow_ne_zero 2 hy)
    calc
      _ = (P*(1+firstRoot))*R^b*(1+firstRoot)^a*
          ((1+firstRoot)*(1-X*(3+4*firstRoot))) := by ring
      _ = C (1/2)*R^b*(1+firstRoot)^a*
          ((1+firstRoot)*R*(1-X*(3+4*firstRoot))) := by rw [P_mul_firstRoot]; ring
      _ = C (1/2)*R^b*(1+firstRoot)^a*(1-2*firstRoot^2) := by rw [firstRoot_jacobian]
      _ = _ := by rw [← hb]; ring
  apply (diagonal_coefficient _ _ firstRoot _ (by simp) constantCoeff_firstRoot ?_ ht n).symm
  rw [← coe_substAlgHom (R:=ℚ) hw]
  simpa only [map_mul,map_add,map_one,map_ofNat,coe_substAlgHom,subst_X hw]
    using firstRoot_relation

end ASR312
