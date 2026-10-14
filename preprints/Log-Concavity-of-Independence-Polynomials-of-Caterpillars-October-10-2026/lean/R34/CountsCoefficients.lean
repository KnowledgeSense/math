import R34.CaterpillarCounts
import R34.SchurIsing

/-! Coefficients of the exact caterpillar independence polynomial. -/

namespace R34.CaterpillarCounts

open scoped BigOperators Classical
noncomputable section

theorem independentCounts_eq_zero_of_card_lt (n : ℕ) (m : Fin n → ℕ)
    (k : ℕ) (hk : Fintype.card (Vertex n m) < k) :
    independentCounts n m k = 0 := by
  classical
  unfold independentCounts
  apply Finset.card_eq_zero.mpr
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro A hA
  have hcard := (Finset.mem_filter.mp hA).2.2
  have hbound : A.card ≤ Fintype.card (Vertex n m) := by
    simpa using Finset.card_le_card (Finset.subset_univ A)
  omega

theorem coeff_count_term (a b k l c d : ℕ) :
    R34.coeff (R34.exponent a b)
      (((c : Poly) * S ^ k) * ((d : Poly) * T ^ l)) =
      if k = a ∧ l = b then (c : ℝ) * (d : ℝ) else 0 := by
  have hpower : S ^ k * T ^ l =
      MvPolynomial.monomial (R34.exponent k l) (1 : ℝ) :=
    R34.power_monomial k l
  have hpoly : ((c : Poly) * S ^ k) * ((d : Poly) * T ^ l) =
      MvPolynomial.monomial (R34.exponent k l) ((c : ℝ) * (d : ℝ)) := by
    calc
      _ = MvPolynomial.C ((c : ℝ) * (d : ℝ)) * (S ^ k * T ^ l) := by
        simp only [map_mul, map_natCast]
        ring
      _ = _ := by rw [hpower, MvPolynomial.C_mul_monomial, mul_one]
  rw [hpoly, R34.coeff_monomial]
  simp only [R34.exponent_injective]

theorem coeff_independencePolynomial_product (n : ℕ) (m : Fin n → ℕ)
    (a b : ℕ) :
    R34.coeff (R34.exponent a b)
      (independencePolynomial n m S * independencePolynomial n m T) =
      (independentCounts n m a : ℝ) * (independentCounts n m b : ℝ) := by
  classical
  unfold independencePolynomial
  simp only [Finset.sum_mul_sum, R34.coeff, MvPolynomial.coeff_sum]
  simp_rw [show ∀ k l : ℕ,
    (((independentCounts n m k : Poly) * S ^ k) *
        ((independentCounts n m l : Poly) * T ^ l)).coeff (R34.exponent a b) =
      if k = a ∧ l = b then
        (independentCounts n m k : ℝ) * (independentCounts n m l : ℝ) else 0 from
    fun k l => coeff_count_term a b k l (independentCounts n m k)
      (independentCounts n m l)]
  have hinner : ∀ k : ℕ,
      (∑ l ∈ Finset.range (Fintype.card (Vertex n m) + 1),
        if k = a ∧ l = b then
          (independentCounts n m k : ℝ) * (independentCounts n m l : ℝ) else 0) =
      if k = a then
        if b ∈ Finset.range (Fintype.card (Vertex n m) + 1) then
          (independentCounts n m k : ℝ) * (independentCounts n m b : ℝ) else 0
        else 0 := by
    intro k
    by_cases hk : k = a
    · simp only [hk, true_and, ite_true, Finset.sum_ite_eq']
    · simp only [hk, false_and, ite_false, Finset.sum_const_zero]
  simp_rw [hinner]
  rw [Finset.sum_ite_eq']
  simp only [Finset.mem_range]
  by_cases ha : a < Fintype.card (Vertex n m) + 1
  · by_cases hb : b < Fintype.card (Vertex n m) + 1
    · rw [ite_eq_left ha, ite_eq_left hb]
    · have hz := independentCounts_eq_zero_of_card_lt n m b (by omega)
      rw [ite_eq_left ha, ite_eq_right hb, hz]
      simp
  · have hz := independentCounts_eq_zero_of_card_lt n m a (by omega)
    rw [ite_eq_right ha, hz]
    simp

theorem actual_counts_logConcave_of_schurPositive (n : ℕ) (m : Fin n → ℕ)
    (h : R34.SchurPositive
      (independencePolynomial n m S * independencePolynomial n m T))
    (k : ℕ) (hk : 1 ≤ k) :
    independentCounts n m (k - 1) * independentCounts n m (k + 1) ≤
      independentCounts n m k ^ 2 := by
  have hd := R34.diagonal_difference_nonnegative h k hk
  rw [coeff_independencePolynomial_product, coeff_independencePolynomial_product] at hd
  have hr : (independentCounts n m (k - 1) : ℝ) *
      (independentCounts n m (k + 1) : ℝ) ≤ (independentCounts n m k : ℝ) ^ 2 := by
    nlinarith
  exact_mod_cast hr

end
end R34.CaterpillarCounts
