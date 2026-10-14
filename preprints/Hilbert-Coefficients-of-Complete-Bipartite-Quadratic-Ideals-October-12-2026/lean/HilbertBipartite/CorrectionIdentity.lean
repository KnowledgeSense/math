import HilbertBipartite.CorrectionNumerator
import Mathlib.Algebra.Polynomial.Degree.Support
import Mathlib.Algebra.Polynomial.Degree.Lemmas

open Finset Polynomial
namespace HilbertBipartite

@[simp] theorem correctionPolynomial_zero (b : ℕ) : correctionPolynomial 0 b = 0 := by
  simp [correctionPolynomial]

@[simp] theorem correctionPolynomial_one (b : ℕ) : correctionPolynomial 1 b = 0 := by
  simp [correctionPolynomial]

theorem correctionPolynomial_coeff_zero (a b d : ℕ) (hd : a-1 ≤ d) :
    (correctionPolynomial a b).coeff d = 0 := by
  unfold correctionPolynomial
  simp only [finsetSum_coeff]
  apply sum_eq_zero
  intro t ht
  apply sum_eq_zero
  intro r hr
  apply sum_eq_zero
  intro k hk
  have h1 := (mem_Icc.mp hr).1
  have h2 := (mem_Icc.mp hk).1
  have h3 := (mem_Icc.mp hk).2
  rw [coeff_C_mul_X_pow]
  simp only [ite_eq_right_iff]
  intro he
  omega

theorem correctionPolynomial_comp_coeff_zero (a b d : ℕ) (hd : a-1 ≤ d) :
    ((correctionPolynomial a b).comp (1+X)).coeff d = 0 := by
  unfold correctionPolynomial
  simp only [Polynomial.sum_comp, mul_comp, C_comp, pow_comp, X_comp, finsetSum_coeff,
    coeff_C_mul, coeff_one_add_X_pow]
  apply sum_eq_zero
  intro t ht
  apply sum_eq_zero
  intro r hr
  apply sum_eq_zero
  intro k hk
  have h1 := (mem_Icc.mp hr).1
  have h2 := (mem_Icc.mp hk).1
  have h3 := (mem_Icc.mp hk).2
  rw [Nat.choose_eq_zero_of_lt (by omega : t+r-1 < d)]
  simp

theorem correctionPolynomial_comp_natDegree (a b : ℕ) :
    ((correctionPolynomial a b).comp (1+X)).natDegree ≤ a-2 := by
  apply natDegree_le_iff_coeff_eq_zero.mpr
  intro d hd
  apply correctionPolynomial_comp_coeff_zero
  omega

/-- The contribution of one defect block to the numerator after translating by one. -/
noncomputable def correctionTranslated (a b : ℕ) : Polynomial ℚ :=
  (-X)^(a+1) * (correctionPolynomial b a).comp (1+X)

theorem correctionTranslated_coeff_low (a b i : ℕ) (hi : i ≤ a) :
    (correctionTranslated a b).coeff i = 0 := by
  unfold correctionTranslated
  have he : (-X : Polynomial ℚ)^(a+1) = C ((-1 : ℚ)^(a+1)) * X^(a+1) := by
    rw [neg_pow]
    simp
  rw [he, mul_assoc, coeff_C_mul, mul_comm (X^(a+1)), coeff_mul_X_pow']
  simp [show ¬ a+1 ≤ i by omega]

theorem correctionTranslated_coeff_high (a b i : ℕ) (hb : 1 ≤ b) (hi : a+b ≤ i) :
    (correctionTranslated a b).coeff i = 0 := by
  unfold correctionTranslated
  have he : (-X : Polynomial ℚ)^(a+1) = C ((-1 : ℚ)^(a+1)) * X^(a+1) := by
    rw [neg_pow]
    simp
  rw [he, mul_assoc, coeff_C_mul, coeff_X_pow_mul']
  split_ifs with h
  · rw [correctionPolynomial_comp_coeff_zero b a (i-(a+1)) (by omega), mul_zero]
  · exact mul_zero _

end HilbertBipartite
