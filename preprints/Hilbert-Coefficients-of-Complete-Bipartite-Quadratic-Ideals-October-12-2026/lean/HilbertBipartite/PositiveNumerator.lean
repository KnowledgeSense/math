import HilbertBipartite.PartialBinomialWeighted
import HilbertBipartite.Signs
import Mathlib.Algebra.Polynomial.Eval.Defs

open Finset Polynomial

namespace HilbertBipartite

noncomputable def signedTransform (m i : ℕ) : Polynomial ℚ :=
  C ((-1 : ℚ)^(m-1)) * ∑ j ∈ range m,
    C ((-1/2 : ℚ)^j * ((i-1).choose j : ℚ)) * (1+X)^j

theorem signedTransform_coeff (m i c : ℕ) (hm : 1 ≤ m) (hc : c < m) :
    (signedTransform m i).coeff c = signedBinomialCoefficient m i c := by
  unfold signedTransform
  simp only [coeff_C_mul, finsetSum_coeff, coeff_one_add_X_pow]
  have hw := partialBinomial_choose_weight (m-1) (i-1) c (-1/2) (by omega)
  rw [show m-1+1=m by omega] at hw
  rw [hw]
  unfold signedBinomialCoefficient signedPartial
  have he : m-1 = c+(m-1-c) := by omega
  have hs : (-1 : ℚ)^c * (-1 : ℚ)^c = 1 := by
    rw [← pow_add, ← two_mul, pow_mul]
    norm_num
  have hp : (-1 : ℚ)^(m-1) = (-1 : ℚ)^c * (-1 : ℚ)^(m-1-c) := by
    conv_lhs => rw [he, pow_add]
  rw [hp, show (-1/2 : ℚ) = -1*(1/2) by norm_num, mul_pow]
  calc
    _ = ((-1 : ℚ)^c * (-1 : ℚ)^c) *
      ((1/2 : ℚ)^c * ((i-1).choose c : ℚ) *
        ((-1 : ℚ)^(m-1-c) * partialBinomial (m-1-c) (i-1-c) (-1*(1/2)))) := by ring
    _ = _ := by rw [hs, one_mul]

theorem signedTransform_coeff_zero (m i c : ℕ) (hc : m ≤ c) :
    (signedTransform m i).coeff c = 0 := by
  unfold signedTransform
  simp only [coeff_C_mul, finsetSum_coeff, coeff_one_add_X_pow]
  have hz : (∑ j ∈ range m,
      (-1/2 : ℚ)^j * ((i-1).choose j : ℚ) * (j.choose c : ℚ)) = 0 := by
    apply sum_eq_zero
    intro j hj
    have hz : j.choose c = 0 := Nat.choose_eq_zero_of_lt (by have := mem_range.mp hj; omega)
    rw [hz]
    simp
  rw [hz, mul_zero]

theorem signedTransform_coeff_nonneg (m i : ℕ) (hm : 1 ≤ m) (hi : m < i) (c : ℕ) :
    0 ≤ (signedTransform m i).coeff c := by
  by_cases hc : c < m
  · rw [signedTransform_coeff m i c hm hc]
    exact signedBinomialCoefficient_nonneg m i c hm hi
  · rw [signedTransform_coeff_zero m i c (by omega)]

theorem signedTransform_top_pos (m i : ℕ) (hm : 1 ≤ m) (hi : m < i) :
    0 < (signedTransform m i).coeff (m-1) := by
  rw [signedTransform_coeff m i (m-1) hm (by omega)]
  exact signedBinomialCoefficient_top_pos m i hm hi



theorem signedTransform_expansion (m i : ℕ) :
    signedTransform m i = ∑ c ∈ range m,
      C ((signedTransform m i).coeff c) * X^c := by
  ext c
  simp only [finsetSum_coeff, coeff_C_mul_X_pow]
  by_cases hc : c < m
  · simp [hc]
  · rw [signedTransform_coeff_zero m i c (by omega)]
    simp [hc]

theorem transformed_binomial_term (j N : ℕ) :
    C ((-1/2 : ℚ)^j * (N.choose j : ℚ)) *
      (1 + (1 - C 2 * X))^j =
    C ((-1 : ℚ)^j * (N.choose j : ℚ)) * (1-X)^j := by
  rw [show (1 + (1-C 2*X) : Polynomial ℚ) = C 2*(1-X) by simp only [map_ofNat]; ring,
    mul_pow]
  have h : (-1/2 : ℚ)^j * (N.choose j : ℚ) * 2^j =
      (-1 : ℚ)^j * (N.choose j : ℚ) := by
    calc
      _ = ((-1/2 : ℚ)^j * 2^j) * (N.choose j : ℚ) := by ring
      _ = _ := by rw [← mul_pow]; norm_num
  rw [← mul_assoc, ← map_pow, ← map_mul, h]

theorem signedTransform_comp (m i : ℕ) (hi : 1 ≤ i) (hm : m ≤ i) :
    (signedTransform m i).comp (1-C 2*X) = C ((-1 : ℚ)^(m-1)) * gPoly m i := by
  unfold signedTransform
  rw [mul_comp, C_comp, Polynomial.sum_comp, gPoly_partial m i hi hm]
  congr 1
  apply sum_congr rfl
  intro j _
  simp only [mul_comp, C_comp, pow_comp, add_comp, one_comp, X_comp]
  exact transformed_binomial_term j (i-1)

end HilbertBipartite
