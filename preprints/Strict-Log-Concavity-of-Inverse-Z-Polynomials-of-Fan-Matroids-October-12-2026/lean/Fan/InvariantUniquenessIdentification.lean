import Fan.InvariantUniqueness
import Fan.InvariantUniquenessBounds
import Fan.ActualGeneratingFunction
import Fan.FanQCoefficients
import Fan.FanYCoefficientBridge
import Fan.FanCandidateRenewal

namespace Fan
open PowerSeries

noncomputable def realPolynomialMap : Polynomial ℤ →+* Polynomial ℝ :=
  Polynomial.mapRingHom (Int.castRingHom ℝ)

@[simp] theorem realPolynomialMap_X : realPolynomialMap Polynomial.X = Polynomial.X := by
  simp [realPolynomialMap]

@[simp] theorem realPolynomialMap_coeff (p : Polynomial ℤ) (j : ℕ) :
    (realPolynomialMap p).coeff j = (p.coeff j : ℝ) := by
  simp [realPolynomialMap]

theorem actual_candidates_real :
    PowerSeries.map realPolynomialMap actualQSeries = fanQCandidate Polynomial.X ∧
    PowerSeries.map realPolynomialMap actualYSeries = fanYCandidate Polynomial.X := by
  apply coupled_renewal_unique (1 + Polynomial.X) Polynomial.X
  · rw [coeff_map, actualQSeries_coeff, Q_zero, map_one,
      coeff_zero_eq_constantCoeff, fanQCandidate_constantCoeff]
  · rw [coeff_map, actualYSeries_coeff, inverseZ_zero, map_one,
      coeff_zero_eq_constantCoeff, fanYCandidate_constantCoeff]
  · intro n hn j hj
    simp only [coeff_map, actualQSeries_coeff, realPolynomialMap_coeff, Q_high_coeff n j hn hj,
      Int.cast_zero]
  · intro n hn j hj
    exact fanQCandidate_high_coeff n j hn hj
  · intro n j hj
    simp only [coeff_map, actualYSeries_coeff, realPolynomialMap_coeff,
      inverseZ_rank_coeff_symm n j hj]
  · intro n j hj
    by_cases hn : n = 0
    · subst n
      have : j = 0 := by omega
      subst j
      rfl
    · exact (fanYCandidate_coeff_symm n j (by omega) hj).symm
  · have h := congrArg (PowerSeries.map realPolynomialMap) actual_renewal
    simpa only [map_mul, map_sub, map_one, PowerSeries.map_C, PowerSeries.map_X,
      map_add, realPolynomialMap_X] using h
  · exact fanCandidate_renewal _

theorem inverseZ_coeff_eq_fanCoefficient (n k : ℕ) (hn : 0 < n) :
    ((inverseZ n).coeff k : ℝ) = fanCoefficient n k := by
  have h := congrArg (fun f : PowerSeries (Polynomial ℝ) => (coeff n f).coeff k)
    actual_candidates_real.2
  simpa only [coeff_map, actualYSeries_coeff, realPolynomialMap_coeff,
    fanYCandidate_coeff_eq n k hn] using h

end Fan
