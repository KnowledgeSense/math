import Dowling.DowlingLeadingReduction
import Fan.CoefficientChangeVariable

noncomputable section
namespace Dowling
open PowerSeries
variable {R : Type*} [CommRing R] [NoZeroDivisors R] [CharZero R]

omit [NoZeroDivisors R] in
theorem candidate_coeff_X_derivative (f : PowerSeries R) (n : ℕ) :
    coeff n (X*derivative f)=(n : R)*coeff n f := by
  cases n with
  | zero => simp
  | succ n => rw [coeff_succ_X_mul,coeff_derivative]; push_cast; ring

/-- The derivative form of formal Lagrange inversion, deduced from the proved
finite coefficient-change theorem. -/
theorem candidate_lagrange_derivative (f u v L : PowerSeries R)
    (huv : u*v=1) (hL0 : L.constantCoeff=0) (hL : L.subst (X*u)=X) (n : ℕ) :
    (n : R)*coeff n (f.subst L)=coeff n ((X*derivative f)*v^n) := by
  let F : PowerSeries R := f.subst L
  have hq : HasSubst ((X : PowerSeries R)*u) := HasSubst.of_constantCoeff_zero' (by simp)
  have hF : F.subst (X*u)=f := by
    dsimp only [F]
    rw [subst_comp_subst_apply (HasSubst.of_constantCoeff_zero' hL0) hq,hL,X_subst]
  have hd := congrArg (derivative (R := R)) hF
  rw [derivative_subst hq] at hd
  rw [← candidate_coeff_X_derivative, Fan.coeff_change_variable _ u v huv]
  apply congrArg (coeff n)
  rw [← coe_substAlgHom hq,map_mul,substAlgHom_X,coe_substAlgHom]
  change (X*u*(derivative F).subst (X*u))*(v^(n+1)*derivative (X*u))=
    (X*derivative f)*v^n
  have huv' : u*v^(n+1)=v^n := by
    rw [pow_succ,mul_left_comm,huv,mul_one]
  calc
    _ = X*(u*v^(n+1))*((derivative F).subst (X*u)*derivative (X*u)) := by ring
    _ = _ := by rw [huv',hd]; ring

 theorem dowlingLambertInverse_constantCoeff : dowlingLambertInverse.constantCoeff=0 :=
  dowlingLambertInverse_weight.constantCoeff_eq_zero (by omega)

 theorem dowlingLambertInverse_subst_coordinate :
    dowlingLambertInverse.subst dowlingLambertCoordinate=X :=
  subst_substInvOfIsUnit_left _ dowlingLambertCoordinate_constantCoeff _

 theorem dowlingLambert_lagrange (f : PowerSeries (Polynomial ℝ)) (n : ℕ) :
    (n : Polynomial ℝ)*coeff n (f.subst dowlingLambertInverse)=
      coeff n ((X*derivative f)*(candidateExp (-dowlingQuadraticExponent))^n) := by
  apply candidate_lagrange_derivative f (candidateExp dowlingQuadraticExponent)
    (candidateExp (-dowlingQuadraticExponent)) dowlingLambertInverse
  · exact candidateExp_neg dowlingQuadraticExponent_constantCoeff
  · exact dowlingLambertInverse_constantCoeff
  · exact dowlingLambertInverse_subst_coordinate

end Dowling
