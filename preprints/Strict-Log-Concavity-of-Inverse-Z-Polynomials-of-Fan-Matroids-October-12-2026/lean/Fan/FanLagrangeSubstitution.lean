import Fan.FanGeneratingCandidates
import Fan.CoefficientChangeVariable

namespace Fan
open PowerSeries
variable {R : Type*} [CommRing R]

noncomputable def fanLagrangeUnit (t : R) : PowerSeries R :=
  (geometricSeries (-1 : R)).subst (C t * X ^ 2)

noncomputable def fanLagrangePolynomial (t : R) : PowerSeries R := 1 + C t * X ^ 2

theorem fanLagrange_inverse (t : R) :
    fanLagrangeUnit t * fanLagrangePolynomial t = 1 := by
  have h := geometricSeries_subst_inverse (-1 : R) (C t * (X : PowerSeries R) ^ 2)
    (by simp)
  simpa only [map_neg, map_one, neg_mul, one_mul, sub_neg_eq_add,
    fanLagrangeUnit, fanLagrangePolynomial] using h

@[simp] theorem fanLagrangeUnit_constantCoeff (t : R) :
    (fanLagrangeUnit t).constantCoeff = 1 := by
  change MvPowerSeries.constantCoeff _ = 1
  rw [fanLagrangeUnit, constantCoeff_subst_of_constantCoeff_zero
    (show (C t * (X : PowerSeries R) ^ 2).constantCoeff = 0 by simp)]
  exact geometricSeries_constantCoeff _

@[simp] theorem fanLagrangePolynomial_constantCoeff (t : R) :
    (fanLagrangePolynomial t).constantCoeff = 1 := by simp [fanLagrangePolynomial]

theorem fanLagrange_change_variable (t : R) :
    (fanLagrangeSeries t).subst (X * fanLagrangeUnit t) = X := by
  let z : PowerSeries R := X * fanLagrangeUnit t
  let f := (fanLagrangeSeries t).subst z
  have hz0 : z.constantCoeff = 0 := by simp [z]
  have hz : HasSubst z := HasSubst.of_constantCoeff_zero' hz0
  have hf0 : f.constantCoeff = 0 := by
    rw [constantCoeff_subst_of_constantCoeff_zero hz0]
    exact fanLagrangeSeries_constantCoeff t
  have h := congrArg (substAlgHom (R := R) hz) (fanLagrangeSeries_equation t)
  simp only [map_mul, map_add, map_pow, map_one, substAlgHom_X, coe_substAlgHom,
    subst_C] at h
  have hf : f = z * (1 + C t * f ^ 2) := h
  have hx : X = z * (1 + C t * X ^ 2) := by
    dsimp [z]
    rw [mul_assoc, ← fanLagrangePolynomial, fanLagrange_inverse, mul_one]
  have hu : IsUnit (1 - z * C t * (f + X)) := by
    apply isUnit_iff_constantCoeff.mpr
    simp [hz0]
  have he : (f - X) * (1 - z * C t * (f + X)) = 0 := by
    linear_combination hf - hx
  exact sub_eq_zero.mp (hu.mul_left_eq_zero.mp he)

theorem fanLagrange_jacobian (t : R) :
    fanLagrangePolynomial t ^ 2 * derivative (X * fanLagrangeUnit t) =
      1 - C t * X ^ 2 := by
  let u := fanLagrangeUnit t
  let v := fanLagrangePolynomial t
  have hu : u * v = 1 := fanLagrange_inverse t
  have hd := congrArg (derivative (R := R)) hu
  rw [Derivation.leibniz, derivative_one] at hd
  simp only [smul_eq_mul] at hd
  have hvd : v ^ 2 * derivative u = -derivative v := by
    linear_combination v * hd - derivative v * hu
  have hv : derivative v = 2 * C t * X := by
    dsimp [v, fanLagrangePolynomial]
    simp only [map_add, derivative_one, Derivation.leibniz, derivative_C,
      derivative_pow, derivative_X, smul_eq_mul]
    ring
  change v ^ 2 * derivative (X * u) = _
  rw [Derivation.leibniz, derivative_X]
  simp only [smul_eq_mul]
  have hval : v = 1 + C t * X ^ 2 := rfl
  linear_combination X * hvd + v * hu - X * hv + hval

theorem fanQCandidate_eq_subst (t : R) :
    fanQCandidate t = ((1 - X) * geometricSeries (2 : R)).subst (fanLagrangeSeries t) := by
  have hs := HasSubst.of_constantCoeff_zero' (fanLagrangeSeries_constantCoeff t)
  rw [← coe_substAlgHom hs]
  simp only [map_mul, map_sub, map_one, substAlgHom_X, coe_substAlgHom]
  rfl

noncomputable def fanRationalY (t : R) : PowerSeries R :=
  (1 - C (1 + t) * X + C t * X ^ 2) *
    (geometricSeries (1 : R)).subst (2 * C (1 + t) * X - 2 * C t * X ^ 2)

theorem fanYCandidate_eq_subst (t : R) :
    fanYCandidate t = (fanRationalY t).subst (fanLagrangeSeries t) := by
  have hs := HasSubst.of_constantCoeff_zero' (fanLagrangeSeries_constantCoeff t)
  have hp : HasSubst (2 * C (1 + t) * (X : PowerSeries R) - 2 * C t * X ^ 2) :=
    HasSubst.of_constantCoeff_zero' (by simp)
  rw [fanRationalY, subst_mul hs, subst_comp_subst_apply hp hs]
  rw [← coe_substAlgHom hs]
  simp only [map_add, map_sub, map_mul, map_pow, map_ofNat, map_one,
    substAlgHom_X, coe_substAlgHom, subst_C]
  simp only [fanYCandidate, map_add, map_one]
  rfl

variable [NoZeroDivisors R] [CharZero R]

theorem fanLagrange_coeff_factored (t : R) (f : PowerSeries R) (n : ℕ) :
    coeff (n + 1) (f.subst (fanLagrangeSeries t)) =
    coeff (n + 1) (f * fanLagrangePolynomial t ^ n * (1 - C t * X ^ 2)) := by
  rw [coeff_change_variable _ (fanLagrangeUnit t) (fanLagrangePolynomial t)
    (fanLagrange_inverse t) (n + 1)]
  rw [subst_comp_subst_apply (HasSubst.of_constantCoeff_zero' (fanLagrangeSeries_constantCoeff t))
    (HasSubst.of_constantCoeff_zero' (by simp)), fanLagrange_change_variable, X_subst]
  congr 1
  rw [show n + 1 + 1 = n + 2 by omega, pow_add, mul_assoc,
    fanLagrange_jacobian, ← mul_assoc]

theorem fanQCandidate_coeff_factored (t : R) (n : ℕ) :
    coeff (n + 1) (fanQCandidate t) = coeff (n + 1)
      (((1 - X) * geometricSeries (2 : R)) * fanLagrangePolynomial t ^ n *
        (1 - C t * X ^ 2)) := by
  rw [fanQCandidate_eq_subst, fanLagrange_coeff_factored]

theorem fanYCandidate_coeff_factored (t : R) (n : ℕ) :
    coeff (n + 1) (fanYCandidate t) = coeff (n + 1)
      (fanRationalY t * fanLagrangePolynomial t ^ n * (1 - C t * X ^ 2)) := by
  rw [fanYCandidate_eq_subst, fanLagrange_coeff_factored]

end Fan
