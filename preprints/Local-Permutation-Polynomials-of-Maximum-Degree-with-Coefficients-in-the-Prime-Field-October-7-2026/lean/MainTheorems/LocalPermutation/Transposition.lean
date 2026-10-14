import MainTheorems.LocalPermutation.RecursiveExtension

namespace ResearchMain.LocalPermutation

open Classical Polynomial

variable {K : Type} [Field K] [Fintype K]

noncomputable def transpositionDifference : K[X] :=
  (X - C 1) ^ (Fintype.card K - 1) - X ^ (Fintype.card K - 1)

noncomputable def transpositionPolynomial : K[X] := X + transpositionDifference

theorem eval_transpositionDifference (x : K) :
    transpositionDifference.eval x = Equiv.swap (0 : K) 1 x - x := by
  have hq := Fintype.one_lt_card (α := K)
  simp only [transpositionDifference, eval_sub, eval_pow, eval_X, eval_C]
  by_cases hx0 : x = 0
  · subst x
    rw [Equiv.swap_apply_left, zero_pow (by omega : Fintype.card K - 1 ≠ 0),
      FiniteField.pow_card_sub_one_eq_one (0 - 1 : K) (by simp)]
  · by_cases hx1 : x = 1
    · subst x
      rw [Equiv.swap_apply_right, sub_self, zero_pow (by omega : Fintype.card K - 1 ≠ 0), one_pow]
    · rw [Equiv.swap_apply_of_ne_of_ne hx0 hx1,
        FiniteField.pow_card_sub_one_eq_one (x - 1) (sub_ne_zero.mpr hx1),
        FiniteField.pow_card_sub_one_eq_one x hx0]
      ring

theorem eval_transpositionPolynomial (x : K) :
    transpositionPolynomial.eval x = Equiv.swap (0 : K) 1 x := by
  simp only [transpositionPolynomial, eval_add, eval_X, eval_transpositionDifference]
  ring

theorem transpositionDifference_degree : (transpositionDifference (K := K)).natDegree ≤ Fintype.card K - 1 := by
  apply (natDegree_sub_le _ _).trans
  apply max_le
  · exact (natDegree_pow_le_of_le _ (natDegree_X_sub_C_le 1)).trans (by simp)
  · simp

theorem transpositionPolynomial_degree (hq : 2 < Fintype.card K) :
    (transpositionPolynomial (K := K)).natDegree < Fintype.card K := by
  apply (natDegree_add_le _ _).trans_lt
  apply max_lt
  · simp only [natDegree_X]
    omega
  · exact transpositionDifference_degree.trans_lt (by omega)

theorem cast_card_sub (k : ℕ) (hk : k ≤ Fintype.card K) : ((Fintype.card K - k : ℕ) : K) = -(k : K) := by
  rw [Nat.cast_sub hk, FiniteField.cast_card_eq_zero, zero_sub]

theorem derivative_transpositionDifference (hq : 2 < Fintype.card K) (x : K) :
    transpositionDifference.derivative.eval x = x⁻¹ - (x - 1)⁻¹ := by
  simp only [transpositionDifference, derivative_sub, derivative_X_sub_C_pow, derivative_X_pow,
    eval_sub, eval_mul, eval_C, eval_pow, eval_X]
  rw [cast_card_sub 1 (by omega), show Fintype.card K - 1 - 1 = Fintype.card K - 2 by omega,
    inverse_power hq, inverse_power hq]
  ring

theorem derivative_transpositionPolynomial (hq : 2 < Fintype.card K) (x : K) :
    transpositionPolynomial.derivative.eval x = 1 + x⁻¹ - (x - 1)⁻¹ := by
  simp only [transpositionPolynomial, derivative_add, derivative_X, eval_add, eval_one,
    derivative_transpositionDifference hq]
  ring

omit [Fintype K] in
theorem transposition_frobenius (p : ℕ) [Fact p.Prime] [CharP K p] (x : K) :
    Equiv.swap (0 : K) 1 (x ^ p) = (Equiv.swap (0 : K) 1 x) ^ p := by
  have h0 : x ^ p = 0 ↔ x = 0 := pow_eq_zero_iff (Fact.out : p.Prime).ne_zero
  have h1 : x ^ p = 1 ↔ x = 1 := by
    constructor
    · intro h
      apply (frobenius K p).injective
      simpa only [frobenius_def, one_pow] using h
    · intro h
      simp [h]
  simp only [Equiv.swap_apply_def, h0, h1]
  split_ifs <;> simp [(Fact.out : p.Prime).ne_zero]

theorem inverse_power_two (hq : 3 < Fintype.card K) (x : K) :
    x ^ (Fintype.card K - 3) = (x⁻¹) ^ 2 := by
  by_cases hx : x = 0
  · simp [hx, zero_pow (by omega : Fintype.card K - 3 ≠ 0)]
  · apply (mul_right_inj' (pow_ne_zero 2 hx)).mp
    rw [← pow_add, show 2 + (Fintype.card K - 3) = Fintype.card K - 1 by omega,
      FiniteField.pow_card_sub_one_eq_one x hx, inv_pow, mul_inv_cancel₀ (pow_ne_zero 2 hx)]

end ResearchMain.LocalPermutation
