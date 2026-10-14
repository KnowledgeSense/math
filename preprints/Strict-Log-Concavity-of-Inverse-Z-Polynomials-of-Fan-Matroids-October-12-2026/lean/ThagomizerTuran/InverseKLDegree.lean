import ThagomizerTuran.KLFunctionalEquation

/-! Strict half-rank support and sign normalization for the true incidence inverse. -/
namespace MatroidInverseZ
open Finset Polynomial
variable {α : Type*} [PartialOrder α] [LocallyFiniteOrder α] [DecidableEq α]

theorem klInverse_high_coeff (r : α → ℕ) (hr : Monotone r) (a b : α)
    (hab : a ≤ b) (hne : a ≠ b) (i : ℕ) (hi : r b - r a ≤ 2 * i) :
    (klInverse r a b).coeff i = 0 := by
  generalize hn : (Icc a b).card = n
  induction n using Nat.strong_induction_on generalizing a b i with
  | h n ih =>
    rw [klInverse_recurrence, ite_eq_right hne, coeff_neg, finsetSum_coeff]
    apply neg_eq_zero.mpr
    apply sum_eq_zero
    intro x hx
    have hax := mem_Ico.mp hx
    by_cases he : a = x
    · subst x
      rw [klInverse_self, one_mul]
      exact kl_high_coeff r a b hne i hi
    · rw [coeff_mul]
      apply sum_eq_zero
      rintro ⟨u, v⟩ huv
      have huv' := Finset.mem_antidiagonal.mp huv
      by_cases hu : r x - r a ≤ 2 * u
      · rw [ih (Icc a x).card (by
          rw [← hn]
          exact card_lt_card (Icc_ssubset_Icc_right hab le_rfl hax.2))
          a x hax.1 he u hu rfl, zero_mul]
      · have ha := hr hax.1
        have hb := hr hax.2.le
        have hv : r b - r x ≤ 2 * v := by omega
        rw [kl_high_coeff r x b hax.2.ne v hv, mul_zero]

theorem inverseKL_high_coeff (r : α → ℕ) (hr : Monotone r) (a b : α)
    (hab : a ≤ b) (hne : a ≠ b) (i : ℕ) (hi : r b - r a ≤ 2 * i) :
    (inverseKL r a b).coeff i = 0 := by
  rw [inverseKL, coeff_C_mul, klInverse_high_coeff r hr a b hab hne i hi, mul_zero]

/-- The two standard sign conventions are mutual inverses. -/
theorem klInverse_eq_signed_inverseKL (r : α → ℕ) (a b : α) :
    klInverse r a b = C ((-1 : ℤ) ^ (r b - r a)) * inverseKL r a b := by
  rw [inverseKL, ← mul_assoc, ← map_mul, ← mul_pow]
  simp

end MatroidInverseZ
