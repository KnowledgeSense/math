import HilbertBipartite.HilbertExpansion
import HilbertBipartite.CorrectionNumerator
import HilbertBipartite.CompositionLength

open Finset Polynomial

namespace HilbertBipartite

theorem hilbertConvolution_X_pow (d n r : ℕ) :
    hilbertConvolution (X^d) n r =
      if d ≤ r then ((r-d+n).choose n : ℚ) else 0 := by
  simp [hilbertConvolution, coeff_X_pow, Finset.sum_ite_eq']

theorem hilbertConvolution_cancel_pow_mul (P : Polynomial ℚ) (c n r : ℕ)
    (hc : c ≤ n) :
    hilbertConvolution ((1-X)^c*P) n r = hilbertConvolution P (n-c) r := by
  induction c generalizing n with
  | zero => simp
  | succ c ih =>
    obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : n ≠ 0)
    rw [pow_succ', mul_assoc, hilbertConvolution_cancel, ih n (by omega)]
    simp only [Nat.succ_eq_add_one, Nat.add_sub_add_right]

/-- The finite numerator from equation (3.1) yields the exact correction count. -/
theorem correction_hilbertConvolution (a b s : ℕ) (ha : 1 ≤ a) (hs : 1 ≤ s) :
    hilbertConvolution (correctionPolynomial a b) (a-1) (s-1) = correction a b s := by
  classical
  unfold correctionPolynomial correction
  simp only [hilbertConvolution_sum, hilbertConvolution_C_mul, hilbertConvolution_X_pow,
    Nat.cast_sum, Nat.cast_mul]
  apply Finset.sum_congr_of_eq_on_inter
  · intro t ht ht'
    apply sum_eq_zero
    intro r hr
    apply sum_eq_zero
    intro k hk
    have htr : s < t+r := by
      have := mem_range.mp ht
      have := mem_Icc.mp hr
      simp only [mem_range, not_lt] at ht'
      omega
    rw [ite_eq_right (by omega)]
    simp
  · intro t ht ht'
    apply sum_eq_zero
    intro r hr
    apply sum_eq_zero
    intro k hk
    have := mem_Icc.mp hk
    simp only [mem_range, not_lt] at ht'
    omega
  · intro t ht ht'
    apply Finset.sum_congr_of_eq_on_inter
    · intro r hr hr'
      apply sum_eq_zero
      intro k hk
      have := mem_Icc.mp hr
      simp only [mem_Icc, not_and, not_le] at hr'
      rw [ite_eq_right (by omega)]
      simp
    · intro r hr hr'
      apply sum_eq_zero
      intro k hk
      have := mem_Icc.mp hr
      have := mem_Icc.mp hk
      simp only [mem_Icc, not_and, not_le] at hr'
      omega
    · intro r hr hr'
      apply sum_congr rfl
      intro k hk
      have hr1 := (mem_Icc.mp hr).1
      have hrs := (mem_Icc.mp hr').2
      have ht' := mem_range.mp ht'
      rw [ite_eq_left (by omega : t+r-1 ≤ s-1)]
      rw [show s-1-(t+r-1)+(a-1) = s-t-r+a-1 by omega]

end HilbertBipartite
