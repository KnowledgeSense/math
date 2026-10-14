import Fan.FanGeneratingCandidates

namespace Fan
open PowerSeries
variable {R : Type*} [CommRing R]

theorem fanCandidate_renewal (t : R) :
    (1 - C (1+t)*X - C t*X*fanQCandidate t)*fanYCandidate t =
      (1 - C (1+t)*X)*fanQCandidate t := by
  let w := fanLagrangeSeries t
  let q := fanQCandidate t
  let y := fanYCandidate t
  let a : PowerSeries R := 1-2*w
  let c : PowerSeries R := 1+C t*w^2
  let b : PowerSeries R := 1-2*C (1+t)*w+2*C t*w^2
  let d : PowerSeries R := 1-C (1+t)*w+C t*w^2
  have hw : X*c=w := (fanLagrangeSeries_equation t).symm
  have hq : q*a=1-w := fanQCandidate_denominator t
  have hy : y*b=d := fanYCandidate_denominator t
  have hl : a*c*(1-C (1+t)*X-C t*X*q)=(1-w)*b := by
    dsimp [a, c, b] at *
    simp only [map_add, map_one] at *
    linear_combination -(1-2*w)*(1+C t+C t*q)*hw - C t*w*hq
  have hr : a*c*((1-C (1+t)*X)*q)=(1-w)*d := by
    dsimp [d]
    calc
      a*c*((1-C (1+t)*X)*q) = (q*a)*(c-C (1+t)*(X*c)) := by ring
      _ = (1-w)*(c-C (1+t)*w) := by rw [hq, hw]
      _ = _ := by dsimp [c]; ring
  have hu : IsUnit (a*c) := by
    apply isUnit_iff_constantCoeff.mpr
    simp [a, c, w]
  apply hu.mul_left_cancel
  change a*c*((1-C (1+t)*X-C t*X*q)*y)=a*c*((1-C (1+t)*X)*q)
  rw [← mul_assoc, hl, mul_assoc, mul_comm b y, hy, hr]

@[simp] theorem fanYCandidate_constantCoeff (t : R) :
    (fanYCandidate t).constantCoeff = 1 := by
  have hz : (2 * C (1+t) * fanLagrangeSeries t -
      2 * C t * fanLagrangeSeries t ^ 2).constantCoeff = (0 : R) := by simp
  have h := constantCoeff_subst_of_constantCoeff_zero hz (geometricSeries (1 : R))
  simp [fanYCandidate, map_add]
  simp [map_add] at h
  exact h

end Fan
