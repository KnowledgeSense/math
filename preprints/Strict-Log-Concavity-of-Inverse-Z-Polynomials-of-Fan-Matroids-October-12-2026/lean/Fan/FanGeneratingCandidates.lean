import Mathlib.RingTheory.PowerSeries.Catalan
import Mathlib.RingTheory.PowerSeries.Substitution
import Mathlib.RingTheory.PowerSeries.WellKnown
import Mathlib.RingTheory.PowerSeries.Inverse
import Mathlib.Tactic

namespace Fan
open PowerSeries
variable {R : Type*} [CommRing R]

noncomputable def catalanOver : PowerSeries R :=
  PowerSeries.map (Nat.castRingHom R) PowerSeries.catalanSeries

@[simp] theorem catalanOver_constantCoeff : (catalanOver : PowerSeries R).constantCoeff = 1 := by
  rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply]
  simp [catalanOver, PowerSeries.coeff_map]

theorem catalanOver_quadratic : (catalanOver : PowerSeries R) ^ 2 * X + 1 = catalanOver := by
  have h := congrArg (PowerSeries.map (Nat.castRingHom R))
    PowerSeries.catalanSeries_sq_mul_X_add_one
  simpa only [map_add, map_mul, map_pow, PowerSeries.map_X, map_one, catalanOver] using h

/-- Geometric series, used only with its proved formal inverse identity. -/
noncomputable def geometricSeries (c : R) : PowerSeries R := PowerSeries.rescale c (PowerSeries.mk 1)

@[simp] theorem geometricSeries_constantCoeff (c : R) : (geometricSeries c).constantCoeff = 1 := by
  rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply]
  simp [geometricSeries, PowerSeries.coeff_rescale]

theorem geometricSeries_mul_denominator (c : R) : geometricSeries c * (1 - C c * X) = 1 := by
  have h := congrArg (PowerSeries.rescale c) (PowerSeries.mk_one_mul_one_sub_eq_one R)
  simpa only [map_mul, map_sub, map_one, PowerSeries.rescale_X, geometricSeries] using h

theorem geometricSeries_pow_coeff (c : R) (d k : ℕ) :
    PowerSeries.coeff k (geometricSeries c ^ (d + 1)) = c ^ k * ((d + k).choose d : R) := by
  rw [geometricSeries, ← map_pow, PowerSeries.mk_one_pow_eq_mk_choose_add,
    PowerSeries.coeff_rescale, PowerSeries.coeff_mk]

noncomputable def fanLagrangeSeries (t : R) : PowerSeries R :=
  X * (catalanOver : PowerSeries R).subst (C t * X ^ 2)

@[simp] theorem fanLagrangeSeries_constantCoeff (t : R) :
    (fanLagrangeSeries t).constantCoeff = 0 := by simp [fanLagrangeSeries]

theorem fanLagrangeSeries_equation (t : R) :
    fanLagrangeSeries t = X * (1 + C t * fanLagrangeSeries t ^ 2) := by
  have hs : HasSubst (C t * (X : PowerSeries R) ^ 2) :=
    HasSubst.of_constantCoeff_zero' (by simp)
  have h := congrArg (substAlgHom (R := R) hs) (catalanOver_quadratic (R := R))
  simp only [map_add, map_mul, map_pow, map_one, substAlgHom_X, coe_substAlgHom] at h
  dsimp [fanLagrangeSeries]
  linear_combination -X * h

noncomputable def fanQCandidate (t : R) : PowerSeries R :=
  (1 - fanLagrangeSeries t) * (geometricSeries (2 : R)).subst (fanLagrangeSeries t)

noncomputable def fanYCandidate (t : R) : PowerSeries R :=
  (1 - C (1 + t) * fanLagrangeSeries t + C t * fanLagrangeSeries t ^ 2) *
    (geometricSeries (1 : R)).subst
      (2 * C (1 + t) * fanLagrangeSeries t - 2 * C t * fanLagrangeSeries t ^ 2)

theorem geometricSeries_subst_inverse (c : R) (w : PowerSeries R)
    (hw : w.constantCoeff = 0) :
    (geometricSeries c).subst w * (1 - C c * w) = 1 := by
  have hs : HasSubst w := HasSubst.of_constantCoeff_zero' hw
  have h := congrArg (substAlgHom (R := R) hs) (geometricSeries_mul_denominator c)
  simp only [map_mul, map_sub, map_one, substAlgHom_X, coe_substAlgHom, subst_C] at h
  exact h

@[simp] theorem fanQCandidate_constantCoeff (t : R) :
    (fanQCandidate t).constantCoeff = 1 := by
  simp only [fanQCandidate, map_mul, map_sub, map_one, fanLagrangeSeries_constantCoeff,
    sub_zero, one_mul]
  change MvPowerSeries.constantCoeff _ = 1
  rw [constantCoeff_subst_of_constantCoeff_zero (fanLagrangeSeries_constantCoeff t)]
  exact geometricSeries_constantCoeff _

theorem fanQCandidate_denominator (t : R) :
    fanQCandidate t * (1 - 2 * fanLagrangeSeries t) = 1 - fanLagrangeSeries t := by
  have h := geometricSeries_subst_inverse (2 : R) (fanLagrangeSeries t)
    (fanLagrangeSeries_constantCoeff t)
  simp only [map_ofNat] at h
  dsimp [fanQCandidate]
  rw [mul_assoc, h, mul_one]

theorem fanYCandidate_denominator (t : R) :
    fanYCandidate t *
      (1 - 2 * C (1 + t) * fanLagrangeSeries t + 2 * C t * fanLagrangeSeries t ^ 2) =
    1 - C (1 + t) * fanLagrangeSeries t + C t * fanLagrangeSeries t ^ 2 := by
  have h := geometricSeries_subst_inverse (1 : R)
    (2 * C (1 + t) * fanLagrangeSeries t - 2 * C t * fanLagrangeSeries t ^ 2)
    (by simp)
  simp only [map_one, one_mul] at h
  dsimp [fanYCandidate]
  linear_combination (1 - C (1 + t) * fanLagrangeSeries t + C t * fanLagrangeSeries t ^ 2) * h

end Fan
