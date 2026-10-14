import Fan.TrailingWeights
import Mathlib.RingTheory.PowerSeries.Basic

namespace Fan
open PowerSeries

noncomputable def actualQSeries : PowerSeries (Polynomial ℤ) := PowerSeries.mk Q
noncomputable def actualYSeries : PowerSeries (Polynomial ℤ) := PowerSeries.mk inverseZ
noncomputable def actualPrefixSeries : PowerSeries (Polynomial ℤ) := PowerSeries.mk prefixWeightSum

@[simp] theorem actualQSeries_coeff (n : ℕ) : coeff n actualQSeries=Q n := coeff_mk _ _
@[simp] theorem actualYSeries_coeff (n : ℕ) : coeff n actualYSeries=inverseZ n := coeff_mk _ _
@[simp] theorem actualPrefixSeries_coeff (n : ℕ) : coeff n actualPrefixSeries=prefixWeightSum n := coeff_mk _ _

@[simp] theorem actualQSeries_constantCoeff : actualQSeries.constantCoeff=1 := by
  rw [← coeff_zero_eq_constantCoeff_apply,actualQSeries_coeff,Q_zero]
@[simp] theorem actualYSeries_constantCoeff : actualYSeries.constantCoeff=1 := by
  rw [← coeff_zero_eq_constantCoeff_apply,actualYSeries_coeff,inverseZ_zero]
@[simp] theorem actualPrefixSeries_constantCoeff : actualPrefixSeries.constantCoeff=1 := by
  rw [← coeff_zero_eq_constantCoeff_apply,actualPrefixSeries_coeff,prefixWeightSum_zero]

theorem actualY_eq_prefix_mul_Q : actualYSeries=actualPrefixSeries*actualQSeries := by
  apply PowerSeries.ext
  intro n
  rw [actualYSeries_coeff,coeff_mul,Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  simp only [actualPrefixSeries_coeff,actualQSeries_coeff]
  rw [← Fin.sum_univ_eq_sum_range]
  exact inverseZ_convolution n

theorem actualPrefix_identity :
    (1-C (1+Polynomial.X)*X)*actualPrefixSeries =
      1-C (1+Polynomial.X)*X+C Polynomial.X*X*actualYSeries := by
  rw [sub_mul,one_mul,mul_assoc,mul_assoc]
  apply PowerSeries.ext
  intro n
  cases n with
  | zero => simp
  | succ n =>
    rw [map_sub (coeff (n+1)),map_add (coeff (n+1)),map_sub (coeff (n+1)),coeff_C_mul,coeff_succ_X_mul,
      coeff_C_mul,coeff_C_mul,coeff_succ_X_mul]
    rw [actualPrefixSeries_coeff,actualPrefixSeries_coeff,actualYSeries_coeff]
    cases n with
    | zero => simp [prefixWeightSum_succ,prefixWeightSum_zero,nonhubSum_zero,inverseZ_zero]
    | succ n =>
      simp only [coeff_one,coeff_X,show n+1+1≠0 by omega,show n+1+1≠1 by omega,
        ite_false,mul_zero,zero_sub,prefixWeightSum_succ,nonhubSum_recurrence]
      ring

theorem actual_renewal :
    (1-C (1+Polynomial.X)*X-C Polynomial.X*X*actualQSeries)*actualYSeries =
      (1-C (1+Polynomial.X)*X)*actualQSeries := by
  have h := actualPrefix_identity
  calc
    _ = ((1-C (1+Polynomial.X)*X)*actualPrefixSeries-
        C Polynomial.X*X*actualYSeries)*actualQSeries := by
      rw [actualY_eq_prefix_mul_Q]
      ring
    _ = _ := by rw [h]; ring

end Fan
