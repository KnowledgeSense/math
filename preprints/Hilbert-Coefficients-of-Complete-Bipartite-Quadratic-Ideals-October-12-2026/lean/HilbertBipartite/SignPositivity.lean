import HilbertBipartite.PositiveNumerator
import HilbertBipartite.CoefficientConvolution

open Finset Polynomial

namespace HilbertBipartite

theorem weightedCoeff_sum {α : Type*} (s : Finset α) (f : α → Polynomial ℚ) (i r : ℕ) :
    weightedCoeff (∑ a ∈ s, f a) i r = ∑ a ∈ s, weightedCoeff (f a) i r := by
  simp only [weightedCoeff, finsetSum_coeff, Finset.sum_mul]
  exact Finset.sum_comm

theorem signed_gPoly_expansion (m i : ℕ) (hi : 1 ≤ i) (hm : m ≤ i) :
    C ((-1 : ℚ)^(m-1))*gPoly m i = ∑ c ∈ range m,
      C ((signedTransform m i).coeff c) * (1-C 2*X)^c := by
  rw [← signedTransform_comp m i hi hm]
  conv_lhs => lhs; rw [signedTransform_expansion m i]
  simp only [Polynomial.sum_comp, mul_comp, C_comp, pow_comp, X_comp]

theorem signed_tau_formula (m i r : ℕ) (hm : 1 ≤ m) (hi : m < i) :
    (-1 : ℚ)^(m-1)*tau m i r = ∑ c ∈ range m,
      (signedTransform m i).coeff c * (2^r * ((r+i-c).choose r : ℚ)) := by
  unfold tau
  rw [← weightedCoeff_C_mul, signed_gPoly_expansion m i (by omega) (by omega),
    weightedCoeff_sum]
  apply sum_congr rfl
  intro c hc
  rw [weightedCoeff_C_mul, weightedCoeff_cancel_pow c i r (by have := mem_range.mp hc; omega)]

theorem signed_tau_pos (m i r : ℕ) (hm : 1 ≤ m) (hi : m < i) :
    0 < (-1 : ℚ)^(m-1)*tau m i r := by
  rw [signed_tau_formula m i r hm hi]
  apply Finset.sum_pos'
  · intro c _
    exact mul_nonneg (signedTransform_coeff_nonneg m i hm hi c) (by positivity)
  · refine ⟨m-1, mem_range.mpr (by omega), ?_⟩
    apply mul_pos (signedTransform_top_pos m i hm hi)
    apply mul_pos (by positivity)
    exact_mod_cast Nat.choose_pos (by omega : r ≤ r+i-(m-1))

end HilbertBipartite
