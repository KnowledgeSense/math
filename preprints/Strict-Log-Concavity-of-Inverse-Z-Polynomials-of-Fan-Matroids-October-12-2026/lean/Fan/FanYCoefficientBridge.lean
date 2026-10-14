import Fan.FanCoefficientExtraction
import Fan.FanDelannoySeries
import Fan.WeightedTransferFan

noncomputable section
namespace Fan
open PowerSeries Finset

theorem fanYCandidate_polynomial_sum (N : ℕ) (hN : 0 < N) :
    (2 * N : Polynomial ℝ) * coeff N (fanYCandidate (Polynomial.X : Polynomial ℝ)) =
      ∑ r ∈ range (N+1), if 2*r < N then
        Polynomial.C ((N.choose r : ℝ) * (N-2*r : ℕ)) * Polynomial.X^r *
          fanDelannoyRow (N-2*r) else 0 := by
  have h := fanLagrange_coeff_sum (Polynomial.X : Polynomial ℝ)
    (fanRationalY Polynomial.X) N hN
  rw [← fanYCandidate_eq_subst] at h
  calc
    _ = 2 * ((N : Polynomial ℝ) * coeff N (fanYCandidate (Polynomial.X : Polynomial ℝ))) := by ring
    _ = 2 * ∑ r ∈ range (N+1), if 2*r < N then
        (N.choose r : Polynomial ℝ) * Polynomial.X^r * ((N-2*r : ℕ) : Polynomial ℝ) *
          coeff (N-2*r) (fanRationalY Polynomial.X) else 0 := by rw [h]
    _ = _ := by
      rw [mul_sum]
      apply sum_congr rfl
      intro r _
      by_cases hr : 2*r < N
      · rw [ite_eq_left hr, ite_eq_left hr]
        rw [show (2 : Polynomial ℝ) *
            ((N.choose r : Polynomial ℝ) * Polynomial.X^r * ((N-2*r : ℕ) : Polynomial ℝ) *
              coeff (N-2*r) (fanRationalY Polynomial.X)) =
            Polynomial.C ((N.choose r : ℝ) * (N-2*r : ℕ)) * Polynomial.X^r *
              (2 * coeff (N-2*r) (fanRationalY Polynomial.X)) by
          simp only [map_mul, map_natCast]; ring]
        rw [fanRationalY_coeff _ (by omega)]
      · simp only [ite_eq_right hr, mul_zero]

theorem fan_weight_scaling (N r : ℕ) (hN : 0 < N) (hr : 2*r < N) :
    2 * N * (2 : ℝ)^(N-1) * ballotWeight N r =
      (N.choose r : ℝ) * (N-2*r : ℕ) * 2^(N-2*r) := by
  have hn : (N : ℝ) ≠ 0 := by positivity
  have hp : (4 : ℝ)^r ≠ 0 := by positivity
  have he : (2 : ℝ)^(N-2*r) * 4^r = 2^N := by
    rw [show (4 : ℝ) = 2^2 by norm_num, ← pow_mul, ← pow_add]
    congr 1
    omega
  have he2 : (2 : ℝ) * 2^(N-1) = 2^N := by
    rw [← pow_succ']
    congr 1
    omega
  rw [ballotWeight, ite_eq_left hr]
  have hc : ((N-2*r : ℕ) : ℝ) = N-2*r := by
    rw [Nat.cast_sub (by omega), Nat.cast_mul, Nat.cast_ofNat]
  rw [hc]
  field_simp
  linear_combination (N.choose r : ℝ) * ((N : ℝ)-2*r) * (he2 - he)

theorem fanYCandidate_term_coeff (N r k : ℕ) (hN : 0 < N) :
    (if 2*r < N then
      Polynomial.C ((N.choose r : ℝ) * (N-2*r : ℕ)) * Polynomial.X^r *
        fanDelannoyRow (N-2*r) else 0).coeff k =
    2 * N * (2 : ℝ)^(N-1) * (kernelEntry (1/2) N k r * ballotWeight N r) := by
  by_cases hr : 2*r < N
  · rw [ite_eq_left hr, mul_assoc, Polynomial.coeff_C_mul, Polynomial.coeff_X_pow_mul']
    by_cases hk : r ≤ k
    · rw [ite_eq_left hk, fanDelannoyRow_coeff]
      by_cases hn : k+r ≤ N
      · rw [ite_eq_left (by omega), kernelEntry, ite_eq_left ⟨hk, hn⟩]
        rw [show N-2*r-(k-r) = N-k-r by omega]
        have he := fan_weight_scaling N r hN hr
        linear_combination -delannoy (1/2) (k-r) (N-k-r) * he
      · rw [ite_eq_right (by omega), mul_zero, kernelEntry,
          ite_eq_right (by tauto), zero_mul, mul_zero]
    · rw [ite_eq_right hk, mul_zero, kernelEntry, ite_eq_right (by tauto),
        zero_mul, mul_zero]
  · rw [ite_eq_right hr, Polynomial.coeff_zero, ballotWeight,
      ite_eq_right hr, mul_zero, mul_zero]

theorem fanYCandidate_coeff_eq (N k : ℕ) (hN : 0 < N) :
    (coeff N (fanYCandidate (Polynomial.X : Polynomial ℝ))).coeff k = fanCoefficient N k := by
  have h := congrArg (fun p : Polynomial ℝ => p.coeff k) (fanYCandidate_polynomial_sum N hN)
  rw [show (2 * N : Polynomial ℝ) * coeff N (fanYCandidate (Polynomial.X : Polynomial ℝ)) =
    2 * ((N : Polynomial ℝ) * coeff N (fanYCandidate (Polynomial.X : Polynomial ℝ))) by ring,
    Polynomial.coeff_ofNat_mul, Polynomial.coeff_natCast_mul, Polynomial.finsetSum_coeff] at h
  simp only [fanYCandidate_term_coeff N _ k hN] at h
  rw [← mul_sum] at h
  rw [fanCoefficient_eq_weighted N k hN, weightedKernel,
    ← Finset.sum_range (fun r => kernelEntry (1/2) N k r * ballotWeight N r)]
  apply (mul_left_cancel₀ (show (2 * N : ℝ) ≠ 0 by positivity))
  linear_combination h

theorem fanYCandidate_coeff_symm (N k : ℕ) (hN : 0 < N) (hk : k ≤ N) :
    (coeff N (fanYCandidate (Polynomial.X : Polynomial ℝ))).coeff (N-k) =
      (coeff N (fanYCandidate (Polynomial.X : Polynomial ℝ))).coeff k := by
  rw [fanYCandidate_coeff_eq _ _ hN, fanYCandidate_coeff_eq _ _ hN,
    fanCoefficient_symm N k hN hk]

theorem fanYCandidate_coeff_above (N k : ℕ) (hN : 0 < N) (hk : N < k) :
    (coeff N (fanYCandidate (Polynomial.X : Polynomial ℝ))).coeff k = 0 := by
  rw [fanYCandidate_coeff_eq _ _ hN, fanCoefficient_outside N k hN hk]

end Fan
