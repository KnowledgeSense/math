import Fan.FanGeneratingCandidates

namespace Fan
open PowerSeries
variable {R S : Type*} [CommRing R] [CommRing S]

theorem map_subst_series (h : R →+* S) (f w : PowerSeries R)
    (hw : HasSubst w) : PowerSeries.map h (f.subst w) =
      (PowerSeries.map h f).subst (PowerSeries.map h w) := by
  exact PowerSeries.map_subst hw f

theorem catalanOver_map (h : R →+* S) :
    PowerSeries.map h (catalanOver : PowerSeries R) = catalanOver := by
  ext n
  simp only [catalanOver, coeff_map]
  simp

theorem geometricSeries_map (h : R →+* S) (c : R) :
    PowerSeries.map h (geometricSeries c) = geometricSeries (h c) := by
  ext n
  simp [geometricSeries, coeff_map, coeff_rescale, coeff_mk]

theorem fanLagrangeSeries_map (h : R →+* S) (t : R) :
    PowerSeries.map h (fanLagrangeSeries t) = fanLagrangeSeries (h t) := by
  have hs : HasSubst (C t * (X : PowerSeries R)^2) :=
    HasSubst.of_constantCoeff_zero' (by simp)
  simp only [fanLagrangeSeries, map_mul, map_X, map_subst_series h _ _ hs, catalanOver_map,
    map_pow, map_C]

theorem fanQCandidate_map (h : R →+* S) (t : R) :
    PowerSeries.map h (fanQCandidate t) = fanQCandidate (h t) := by
  have hs := HasSubst.of_constantCoeff_zero' (fanLagrangeSeries_constantCoeff t)
  simp only [fanQCandidate, map_mul, map_sub, map_one, fanLagrangeSeries_map,
    map_subst_series h _ _ hs, geometricSeries_map, map_ofNat]

theorem fanYCandidate_map (h : R →+* S) (t : R) :
    PowerSeries.map h (fanYCandidate t) = fanYCandidate (h t) := by
  have hs : HasSubst (2*C (1+t)*fanLagrangeSeries t - 2*C t*fanLagrangeSeries t^2) :=
    HasSubst.of_constantCoeff_zero' (by simp)
  rw [fanYCandidate, map_mul, map_subst_series h _ _ hs]
  simp only [fanYCandidate, map_mul, map_add, map_sub, map_pow, map_one, map_ofNat,
    map_C, fanLagrangeSeries_map, geometricSeries_map]

end Fan
