import HilbertBipartite.Definitions
import HilbertBipartite.PartialBinomial
import Mathlib.Algebra.Polynomial.Coeff

open Finset Polynomial

namespace HilbertBipartite

theorem full_binomial_numerator (i : ℕ) (hi : 1 ≤ i) :
    (∑ j ∈ range i, C ((-1 : ℚ)^j * ((i-1).choose j : ℚ)) * (1-X)^j) =
      (X : Polynomial ℚ)^(i-1) := by
  have h := add_pow (-(1-X) : Polynomial ℚ) 1 (i-1)
  rw [show i-1+1=i by omega] at h
  have hp : (-(1-X) + 1 : Polynomial ℚ) = X := by ring
  rw [hp] at h
  rw [h]
  apply sum_congr rfl
  intro j _
  rw [neg_pow (1-X : Polynomial ℚ)]
  simp only [one_pow, mul_one, map_mul, map_pow, map_neg, map_one, C_eq_natCast]
  ring


theorem gPoly_partial (m i : ℕ) (hi : 1 ≤ i) (hm : m ≤ i) :
    gPoly m i = ∑ j ∈ range m,
      C ((-1 : ℚ)^j * ((i-1).choose j : ℚ)) * (1-X)^j := by
  have hf : (range i).filter (fun j => ¬ m ≤ j) = range m := by
    ext j
    simp only [mem_filter, mem_range]
    omega
  have h := sum_filter_add_sum_filter_not (range i) (fun j => m ≤ j)
    (fun j => C ((-1 : ℚ)^j * ((i-1).choose j : ℚ)) * (1-X)^j)
  rw [hf, full_binomial_numerator i hi] at h
  unfold gPoly delta
  rw [← h]
  ring

theorem weightedCoeff_add (P Q : Polynomial ℚ) (i r : ℕ) :
    weightedCoeff (P+Q) i r = weightedCoeff P i r + weightedCoeff Q i r := by
  simp only [weightedCoeff, coeff_add, add_mul, sum_add_distrib]

theorem weightedCoeff_sub (P Q : Polynomial ℚ) (i r : ℕ) :
    weightedCoeff (P-Q) i r = weightedCoeff P i r - weightedCoeff Q i r := by
  simp only [weightedCoeff, coeff_sub, sub_mul, sum_sub_distrib]

theorem weightedCoeff_C_mul (a : ℚ) (P : Polynomial ℚ) (i r : ℕ) :
    weightedCoeff (C a * P) i r = a * weightedCoeff P i r := by
  simp only [weightedCoeff, coeff_C_mul, mul_assoc, mul_sum]

theorem weightedCoeff_nonneg (P : Polynomial ℚ) (i r : ℕ)
    (h : ∀ j ≤ r, 0 ≤ P.coeff j) : 0 ≤ weightedCoeff P i r := by
  unfold weightedCoeff
  apply sum_nonneg
  intro j hj
  exact mul_nonneg (mul_nonneg (h j (by have := mem_range.mp hj; omega))
    (by positivity)) (by positivity)

end HilbertBipartite
