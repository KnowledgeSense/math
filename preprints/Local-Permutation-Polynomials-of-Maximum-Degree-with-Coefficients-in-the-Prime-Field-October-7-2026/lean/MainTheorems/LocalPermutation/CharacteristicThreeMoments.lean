import MainTheorems.LocalPermutation.CharacteristicThreeData
import Mathlib.Algebra.Polynomial.Coeff

namespace ResearchMain.LocalPermutation

open Classical Polynomial

variable {K : Type} [Field K] [Fintype K]

theorem sum_eval_mul_variable (hq : 2 < Fintype.card K) {P : K[X]}
    (hP : P.natDegree < Fintype.card K) : (∑ x : K, P.eval x * x) = -P.coeff (Fintype.card K - 2) := by
  simp_rw [P.eval_eq_sum_range' hP, Finset.sum_mul, mul_assoc, ← pow_succ]
  rw [Finset.sum_comm]
  simp_rw [← Finset.mul_sum]
  have hs : (∑ j ∈ Finset.range (Fintype.card K), P.coeff j * ∑ x : K, x ^ (j + 1)) =
      ∑ j ∈ Finset.range (Fintype.card K), if j = Fintype.card K - 2 then -P.coeff j else 0 := by
    apply Finset.sum_congr rfl
    intro j hj
    rw [sum_power_weighted hq j (by have := Finset.mem_range.mp hj; omega)]
    split_ifs <;> simp
  rw [hs, Finset.sum_eq_single (Fintype.card K - 2)]
  · simp
  · intro j _ hj
    rw [ite_eq_right hj]
  · intro h
    exact (h (Finset.mem_range.mpr (by omega))).elim

theorem one_variable_moment (H : K → K) : weightedMoment (fun x : Fin 1 → K => H (x 0)) =
    ∑ a : K, H a * a := by
  unfold weightedMoment
  simp only [Fin.prod_univ_one]
  exact Equiv.sum_comp (Equiv.funUnique (Fin 1) K) (fun a : K => H a * a)

theorem transpositionDifference_coeff (hq : 3 < Fintype.card K) :
    (transpositionDifference (K := K)).coeff (Fintype.card K - 2) = 1 := by
  unfold transpositionDifference
  rw [coeff_sub, show (X - C (1 : K)) = X + C (-1) by rw [C_neg, sub_eq_add_neg]]
  rw [coeff_X_add_C_pow, coeff_X_pow, ite_eq_right (by omega)]
  rw [show Fintype.card K - 1 = (Fintype.card K - 2) + 1 by omega, Nat.choose_succ_self_right]
  rw [show Fintype.card K - 2 + 1 - (Fintype.card K - 2) = 1 by omega, pow_one, sub_zero]
  rw [show Fintype.card K - 2 + 1 = Fintype.card K - 1 by omega, cast_card_sub 1 (by omega)]
  simp

theorem stateAPolynomial_coeff (hq : 3 < Fintype.card K) :
    (stateAPolynomial (K := K)).coeff (Fintype.card K - 2) = 2 := by
  unfold stateAPolynomial
  rw [coeff_add, coeff_add, coeff_add, coeff_C, ite_eq_right (by omega), coeff_X,
    ite_eq_right (by omega), zero_add, zero_add, transpositionDifference_coeff hq]
  rw [show (X - C (1 : K)) = X + C (-1) by rw [C_neg, sub_eq_add_neg], coeff_X_add_C_pow,
    Nat.sub_self, pow_zero, Nat.choose_self, Nat.cast_one, one_mul]
  ring

theorem stateBPolynomial_coeff (hq : 3 < Fintype.card K) :
    (stateBPolynomial (K := K)).coeff (Fintype.card K - 2) = -1 := by
  unfold stateBPolynomial
  rw [coeff_sub, coeff_add, coeff_X, ite_eq_right (by omega), zero_add,
    coeff_eq_zero_of_natDegree_lt (p := (X - C (1 : K)) ^ (Fintype.card K - 3))
      ((natDegree_pow_le_of_le _ (natDegree_X_sub_C_le 1)).trans_lt (by omega)),
    transpositionDifference_coeff hq, zero_sub]

theorem stateBPolynomial_degree (hq : 3 < Fintype.card K) :
    (stateBPolynomial (K := K)).natDegree < Fintype.card K := by
  apply (natDegree_sub_le _ _).trans_lt
  apply max_lt
  · apply (natDegree_add_le _ _).trans_lt
    apply max_lt
    · simp only [natDegree_X]
      omega
    · exact (natDegree_pow_le_of_le _ (natDegree_X_sub_C_le 1)).trans_lt (by omega)
  · exact transpositionDifference_degree.trans_lt (by omega)

variable [CharP K 3]

theorem stateA_moment (hq : 3 < Fintype.card K) :
    weightedMoment (fun x : Fin 1 → K => stateA (x 0)) = 1 := by
  rw [one_variable_moment]
  simp_rw [← eval_stateAPolynomial hq]
  rw [sum_eval_mul_variable (by omega) (stateAPolynomial_degree hq), stateAPolynomial_coeff hq,
    two_eq_neg_one, neg_neg]

omit [CharP K 3] in
theorem stateB_moment (hq : 3 < Fintype.card K) :
    weightedMoment (fun x : Fin 1 → K => stateB (x 0)) = 1 := by
  rw [one_variable_moment]
  simp_rw [← eval_stateBPolynomial hq]
  rw [sum_eval_mul_variable (by omega) (stateBPolynomial_degree hq), stateBPolynomial_coeff hq, neg_neg]

end ResearchMain.LocalPermutation
