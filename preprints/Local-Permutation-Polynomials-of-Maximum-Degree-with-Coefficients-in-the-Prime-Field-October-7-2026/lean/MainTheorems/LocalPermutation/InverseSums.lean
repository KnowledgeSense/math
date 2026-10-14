import MainTheorems.LocalPermutation.FiniteSums
import Mathlib.Algebra.Polynomial.Taylor

namespace ResearchMain.LocalPermutation

open Classical Polynomial

variable {K : Type} [Field K] [Fintype K]

theorem sum_inverse (hq : 2 < Fintype.card K) : (∑ x : K, x⁻¹) = 0 := by
  have h := Equiv.sum_comp (Equiv.inv K) (fun x : K => x)
  change (∑ x : K, x⁻¹) = ∑ x : K, x at h
  rw [h]
  simpa only [pow_one] using FiniteField.sum_pow_lt_card_sub_one K 1 (by omega)

theorem sum_mul_inverse : (∑ x : K, x * x⁻¹) = -1 := by
  convert sum_power_last (K := K) using 1
  apply Finset.sum_congr rfl
  intro x _
  by_cases hx : x = 0
  · simp [hx, zero_pow (by have := Fintype.one_lt_card (α := K); omega : Fintype.card K - 1 ≠ 0)]
  · rw [mul_inv_cancel₀ hx, FiniteField.pow_card_sub_one_eq_one x hx]

theorem sum_power_mul_inverse (hq : 2 < Fintype.card K) {j : ℕ} (hj : j < Fintype.card K) :
    (∑ x : K, x ^ j * x⁻¹) = if j = 1 then -1 else 0 := by
  by_cases hj0 : j = 0
  · subst j
    simpa only [pow_zero, one_mul, ite_eq_right (by decide : (0 : ℕ) ≠ 1)] using sum_inverse hq
  · by_cases hj1 : j = 1
    · subst j
      simpa only [pow_one, ite_true] using sum_mul_inverse (K := K)
    · rw [ite_eq_right hj1]
      have he (x : K) : x ^ j * x⁻¹ = x ^ (j - 1) := by
        by_cases hx : x = 0
        · simp [hx, zero_pow (by omega : j - 1 ≠ 0)]
        · rw [show j = j - 1 + 1 by omega, pow_succ, mul_assoc, mul_inv_cancel₀ hx, mul_one]
          simp only [Nat.add_sub_cancel]
      simp_rw [he]
      exact FiniteField.sum_pow_lt_card_sub_one K (j - 1) (by omega)

theorem sum_eval_mul_inverse (hq : 2 < Fintype.card K) {P : K[X]}
    (hP : P.natDegree < Fintype.card K) : (∑ x : K, P.eval x * x⁻¹) = -P.coeff 1 := by
  simp_rw [P.eval_eq_sum_range' hP, Finset.sum_mul, mul_assoc]
  rw [Finset.sum_comm]
  simp_rw [← Finset.mul_sum]
  have hs : (∑ j ∈ Finset.range (Fintype.card K), P.coeff j * ∑ x : K, x ^ j * x⁻¹) =
      ∑ j ∈ Finset.range (Fintype.card K), if j = 1 then -P.coeff j else 0 := by
    apply Finset.sum_congr rfl
    intro j hj
    rw [sum_power_mul_inverse hq (Finset.mem_range.mp hj)]
    split_ifs <;> simp
  rw [hs, Finset.sum_eq_single 1]
  · simp
  · intro j _ hj
    rw [ite_eq_right hj]
  · intro h
    exact (h (Finset.mem_range.mpr hq.le)).elim

theorem sum_eval_add_mul_inverse (hq : 2 < Fintype.card K) {P : K[X]}
    (hP : P.natDegree < Fintype.card K) (v : K) :
    (∑ x : K, P.eval (v + x) * x⁻¹) = -P.derivative.eval v := by
  have h := sum_eval_mul_inverse hq (P := taylor v P) (by rwa [natDegree_taylor])
  simpa only [taylor_eval, add_comm, taylor_coeff_one] using h

end ResearchMain.LocalPermutation
