import MainTheorems.LocalPermutation.Transposition

namespace ResearchMain.LocalPermutation

open Classical Polynomial

variable {K : Type} [Field K] [Fintype K] [CharP K 3]

noncomputable def stateA (x : K) : K := 2 + Equiv.swap (0 : K) 1 x + (x - 1)⁻¹

noncomputable def stateB (x : K) : K := x + ((x - 1)⁻¹) ^ 2 - (Equiv.swap (0 : K) 1 x - x)

noncomputable def stateAPolynomial : K[X] :=
  C 2 + X + (X - C 1) ^ (Fintype.card K - 2) + transpositionDifference

noncomputable def stateBPolynomial : K[X] :=
  X + (X - C 1) ^ (Fintype.card K - 3) - transpositionDifference

noncomputable def stateBSwappedPolynomial : K[X] :=
  X + (X - C 1) ^ (Fintype.card K - 3) + transpositionDifference

omit [Fintype K] in
theorem three_eq_zero : (3 : K) = 0 := by exact_mod_cast (CharP.cast_eq_zero K 3)

omit [Fintype K] in
theorem two_eq_neg_one : (2 : K) = -1 := by
  linear_combination three_eq_zero (K := K)

omit [Fintype K] [CharP K 3] in
theorem stateA_zero : stateA (0 : K) = 2 := by simp [stateA]

omit [Fintype K] [CharP K 3] in
theorem stateA_one : stateA (1 : K) = 2 := by simp [stateA]

omit [Fintype K] [CharP K 3] in
theorem stateB_zero : stateB (0 : K) = 0 := by simp [stateB]

omit [Fintype K] [CharP K 3] in
theorem stateB_one : stateB (1 : K) = 2 := by
  simp only [stateB, Equiv.swap_apply_right, sub_self, inv_zero, zero_pow (by decide : 2 ≠ 0)]
  ring

omit [Fintype K] [CharP K 3] in
theorem stateA_swap (x : K) : stateA (Equiv.swap (0 : K) 1 x) = stateA x := by
  by_cases hx0 : x = 0
  · subst x
    rw [Equiv.swap_apply_left, stateA_one, stateA_zero]
  · by_cases hx1 : x = 1
    · subst x
      rw [Equiv.swap_apply_right, stateA_zero, stateA_one]
    · rw [Equiv.swap_apply_of_ne_of_ne hx0 hx1]

omit [CharP K 3] in
theorem eval_stateAPolynomial (hq : 3 < Fintype.card K) (x : K) :
    stateAPolynomial.eval x = stateA x := by
  simp only [stateAPolynomial, eval_add, eval_C, eval_X, eval_pow, eval_sub,
    inverse_power (by omega : 2 < Fintype.card K), eval_transpositionDifference, stateA]
  ring

omit [CharP K 3] in
theorem eval_stateBPolynomial (hq : 3 < Fintype.card K) (x : K) :
    stateBPolynomial.eval x = stateB x := by
  simp only [stateBPolynomial, eval_add, eval_sub, eval_X, eval_pow, eval_C,
    inverse_power_two hq, eval_transpositionDifference, stateB]

omit [CharP K 3] in
theorem eval_stateBSwappedPolynomial (hq : 3 < Fintype.card K) (x : K) :
    stateBSwappedPolynomial.eval x = stateB (Equiv.swap (0 : K) 1 x) := by
  simp only [stateBSwappedPolynomial, eval_add, eval_X, eval_pow, eval_sub, eval_C,
    inverse_power_two hq, eval_transpositionDifference]
  by_cases hx0 : x = 0
  · subst x
    simp [stateB_one, one_add_one_eq_two]
  · by_cases hx1 : x = 1
    · subst x
      simp [stateB_zero]
    · rw [Equiv.swap_apply_of_ne_of_ne hx0 hx1]
      simp only [stateB, Equiv.swap_apply_of_ne_of_ne hx0 hx1, sub_self, sub_zero, add_zero]

omit [CharP K 3] in
theorem derivative_transposition_inv (hq : 3 < Fintype.card K) (x : K) :
    transpositionPolynomial.derivative.eval x⁻¹ = stateA x := by
  rw [derivative_transpositionPolynomial (by omega), inv_inv]
  by_cases hx0 : x = 0
  · subst x
    simp [stateA_zero, one_add_one_eq_two]
  · by_cases hx1 : x = 1
    · subst x
      simp [stateA_one, one_add_one_eq_two]
    · simp only [stateA, Equiv.swap_apply_of_ne_of_ne hx0 hx1]
      field_simp
      ring

theorem derivative_stateAPolynomial (hq : 3 < Fintype.card K) (x : K) :
    stateAPolynomial.derivative.eval x⁻¹ = stateB x := by
  have hcast : ((Fintype.card K - 2 : ℕ) : K) = 1 := by
    rw [cast_card_sub 2 (by omega)]
    change -(2 : K) = 1
    rw [two_eq_neg_one, neg_neg]
  simp only [stateAPolynomial, derivative_add, derivative_C, derivative_X,
    derivative_X_sub_C_pow, eval_add, eval_zero, eval_one, eval_mul, eval_C, eval_pow, eval_sub, eval_X]
  rw [hcast, one_mul, show Fintype.card K - 2 - 1 = Fintype.card K - 3 by omega,
    inverse_power_two hq, derivative_transpositionDifference (by omega), inv_inv]
  by_cases hx0 : x = 0
  · subst x
    simp only [inv_zero, zero_sub, inv_neg, inv_one, neg_one_sq, stateB_zero]
    linear_combination three_eq_zero (K := K)
  · by_cases hx1 : x = 1
    · subst x
      simp [stateB_one, one_add_one_eq_two]
    · simp only [stateB, Equiv.swap_apply_of_ne_of_ne hx0 hx1, sub_self, sub_zero]
      field_simp
      linear_combination (x * (x - 1) ^ 3) * three_eq_zero (K := K)

theorem derivative_stateBSwappedPolynomial (hq : 3 < Fintype.card K) (x : K) :
    stateBSwappedPolynomial.derivative.eval x⁻¹ = stateA x := by
  have hcast : ((Fintype.card K - 3 : ℕ) : K) = 0 := by
    rw [cast_card_sub 3 (by omega)]
    change -(3 : K) = 0
    rw [three_eq_zero, neg_zero]
  simp only [stateBSwappedPolynomial, derivative_add, derivative_X, derivative_X_sub_C_pow,
    hcast, C_0, zero_mul, eval_add, eval_one, add_zero]
  have h := derivative_transposition_inv hq x
  simpa only [transpositionPolynomial, derivative_add, derivative_X, eval_add, eval_one] using h

omit [CharP K 3] in
theorem stateAPolynomial_degree (hq : 3 < Fintype.card K) :
    (stateAPolynomial (K := K)).natDegree < Fintype.card K := by
  apply (natDegree_add_le _ _).trans_lt
  apply max_lt
  · apply (natDegree_add_le _ _).trans_lt
    apply max_lt
    · apply (natDegree_add_le _ _).trans_lt
      simp only [natDegree_C, natDegree_X]
      omega
    · exact (natDegree_pow_le_of_le _ (natDegree_X_sub_C_le 1)).trans_lt (by omega)
  · exact transpositionDifference_degree.trans_lt (by omega)

omit [CharP K 3] in
theorem stateBSwappedPolynomial_degree (hq : 3 < Fintype.card K) :
    (stateBSwappedPolynomial (K := K)).natDegree < Fintype.card K := by
  apply (natDegree_add_le _ _).trans_lt
  apply max_lt
  · apply (natDegree_add_le _ _).trans_lt
    apply max_lt
    · simp only [natDegree_X]
      omega
    · exact (natDegree_pow_le_of_le _ (natDegree_X_sub_C_le 1)).trans_lt (by omega)
  · exact transpositionDifference_degree.trans_lt (by omega)

end ResearchMain.LocalPermutation
