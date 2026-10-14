import MainTheorems.LocalPermutation.Interpolation
import Mathlib.Algebra.Polynomial.Eval.Degree

namespace ResearchMain.LocalPermutation

open Classical

variable {K : Type*} [Field K] [Fintype K]

theorem sum_power_last : (∑ x : K, x ^ (Fintype.card K - 1)) = -1 := by
  have hq : 1 < Fintype.card K := Fintype.one_lt_card
  rw [← Finset.add_sum_erase Finset.univ (fun x : K => x ^ (Fintype.card K - 1)) (Finset.mem_univ 0)]
  rw [zero_pow (by omega : Fintype.card K - 1 ≠ 0), zero_add]
  calc
    ∑ x ∈ Finset.univ.erase (0 : K), x ^ (Fintype.card K - 1) = ∑ _x ∈ Finset.univ.erase (0 : K), (1 : K) := by
      apply Finset.sum_congr rfl
      intro x hx
      exact FiniteField.pow_card_sub_one_eq_one x (Finset.mem_erase.mp hx).1
    _ = -1 := by
      simp only [Finset.sum_const, Finset.card_erase_of_mem (Finset.mem_univ (0 : K)), Finset.card_univ,
        nsmul_eq_mul, mul_one]
      rw [Nat.cast_sub (by omega : 1 ≤ Fintype.card K), FiniteField.cast_card_eq_zero, Nat.cast_one, zero_sub]

theorem sum_eval {P : Polynomial K} (hP : P.natDegree < Fintype.card K) :
    (∑ x : K, P.eval x) = -P.coeff (Fintype.card K - 1) := by
  simp_rw [Polynomial.eval_eq_sum_range' hP]
  rw [Finset.sum_comm]
  simp_rw [← Finset.mul_sum]
  rw [Finset.sum_eq_single (Fintype.card K - 1)]
  · rw [sum_power_last, mul_neg_one]
  · intro i hi hne
    rw [FiniteField.sum_pow_lt_card_sub_one K i (by have := Finset.mem_range.mp hi; omega), mul_zero]
  · intro h
    exact (h (Finset.mem_range.mpr (by have := Fintype.card_pos (α := K); omega))).elim

theorem sum_bijective (hq : 2 < Fintype.card K) {f : K → K} (hf : Function.Bijective f) :
    (∑ x : K, f x) = 0 := by
  have h := Equiv.sum_comp (Equiv.ofBijective f hf) (fun x : K => x)
  change (∑ x : K, f x) = ∑ x : K, x at h
  rw [h]
  simpa only [pow_one] using FiniteField.sum_pow_lt_card_sub_one K 1 (by omega)

theorem permutation_coeff_last_zero (hq : 2 < Fintype.card K) {P : Polynomial K}
    (hP : P.natDegree < Fintype.card K) (hf : Function.Bijective P.eval) :
    P.coeff (Fintype.card K - 1) = 0 := by
  have h := sum_eval hP
  rw [sum_bijective hq hf] at h
  exact neg_eq_zero.mp h.symm

end ResearchMain.LocalPermutation
