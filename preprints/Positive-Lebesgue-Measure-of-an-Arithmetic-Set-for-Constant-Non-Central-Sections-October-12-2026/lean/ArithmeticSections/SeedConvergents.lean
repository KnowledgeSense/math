import ArithmeticSections.SeedDigits
import ArithmeticSections.ApproximationBounds

namespace ArithmeticSections

private theorem seed_sqrt_bounds : 1 < Real.sqrt 2 ∧ Real.sqrt 2 < 2 := by
  have hs := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)
  have hp := Real.sqrt_nonneg (2 : ℝ)
  constructor <;> nlinarith

theorem seedRotation_floor_zero : ⌊seedRotation⌋ = (0 : ℤ) := by
  apply Int.floor_eq_iff.mpr
  have h := seedRotation_bounds
  norm_num only [Int.cast_zero]
  constructor <;> linarith

theorem seedRotation_complete_one : completeQuotient seedRotation 1 = 4 - Real.sqrt 2 := by
  simp only [completeQuotient, Int.fract, seedRotation_floor_zero, Int.cast_zero, sub_zero]
  have hs := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)
  have hb := seed_sqrt_bounds
  unfold seedRotation
  rw [inv_div]
  apply (div_eq_iff (by positivity : 4 + Real.sqrt 2 ≠ 0)).mpr
  nlinarith

theorem seedRotation_floor_one : ⌊completeQuotient seedRotation 1⌋ = (2 : ℤ) := by
  rw [seedRotation_complete_one]
  apply Int.floor_eq_iff.mpr
  have h := seed_sqrt_bounds
  norm_num only [Int.cast_ofNat]
  constructor <;> linarith

theorem seedRotation_complete_two : completeQuotient seedRotation 2 = 1 + Real.sqrt 2 / 2 := by
  change (Int.fract (completeQuotient seedRotation 1))⁻¹ = _
  rw [Int.fract, seedRotation_floor_one, seedRotation_complete_one]
  norm_num only [Int.cast_ofNat]
  have hb := seed_sqrt_bounds
  have hs := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)
  apply (mul_eq_one_iff_inv_eq₀ (by linarith : 4 - Real.sqrt 2 - 2 ≠ 0)).mp
  nlinarith

theorem seedRotation_floor_two : ⌊completeQuotient seedRotation 2⌋ = (1 : ℤ) := by
  rw [seedRotation_complete_two]
  apply Int.floor_eq_iff.mpr
  have h := seed_sqrt_bounds
  norm_num only [Int.cast_one]
  constructor <;> linarith

theorem seedRotation_complete_three : completeQuotient seedRotation 3 = Real.sqrt 2 := by
  change (Int.fract (completeQuotient seedRotation 2))⁻¹ = _
  rw [Int.fract, seedRotation_floor_two, seedRotation_complete_two]
  norm_num only [Int.cast_one]
  have hb := seed_sqrt_bounds
  have hs := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)
  apply (mul_eq_one_iff_inv_eq₀ (by linarith : 1 + Real.sqrt 2 / 2 - 1 ≠ 0)).mp
  nlinarith

theorem seedRotation_floor_three : ⌊completeQuotient seedRotation 3⌋ = (1 : ℤ) := by
  rw [seedRotation_complete_three]
  apply Int.floor_eq_iff.mpr
  have h := seed_sqrt_bounds
  norm_num only [Int.cast_one]
  exact ⟨h.1.le, h.2⟩

private theorem seedRotation_tail_floor : ⌊1 + Real.sqrt 2⌋ = (2 : ℤ) := by
  apply Int.floor_eq_iff.mpr
  have h := seed_sqrt_bounds
  norm_num only [Int.cast_ofNat]
  constructor <;> linarith

theorem seedRotation_complete_tail (n : ℕ) : completeQuotient seedRotation (n + 4) = 1 + Real.sqrt 2 := by
  induction n with
  | zero =>
    change (Int.fract (completeQuotient seedRotation 3))⁻¹ = _
    rw [Int.fract, seedRotation_floor_three, seedRotation_complete_three]
    norm_num only [Int.cast_one]
    have h := seed_inversion_identities.2.2
    simpa only [one_div, show (2 : ℝ) + (Real.sqrt 2 - 1) = 1 + Real.sqrt 2 by ring] using h
  | succ n ih =>
    change (Int.fract (completeQuotient seedRotation (n + 4)))⁻¹ = _
    rw [ih, Int.fract, seedRotation_tail_floor]
    norm_num only [Int.cast_ofNat]
    convert seed_inversion_identities.2.2 using 1 <;> ring_nf

theorem seedRotation_digit_one : actualDigit seedRotation 1 = 2 := by simp [actualDigit, seedRotation_floor_one]
theorem seedRotation_digit_two : actualDigit seedRotation 2 = 1 := by simp [actualDigit, seedRotation_floor_two]
theorem seedRotation_digit_three : actualDigit seedRotation 3 = 1 := by simp [actualDigit, seedRotation_floor_three]
theorem seedRotation_digit_tail (n : ℕ) : actualDigit seedRotation (n + 4) = 2 := by
  rw [actualDigit, seedRotation_complete_tail, seedRotation_tail_floor]
  rfl

theorem seedRotation_denominator_two : actualDenominator seedRotation 2 = 3 := by
  simp [actualDenominator, denominator, seedRotation_digit_one, seedRotation_digit_two]
theorem seedRotation_denominator_three : actualDenominator seedRotation 3 = 5 := by
  simp [actualDenominator, denominator, seedRotation_digit_one, seedRotation_digit_two, seedRotation_digit_three]
theorem seedRotation_denominator_four : actualDenominator seedRotation 4 = 13 := by
  simp [actualDenominator, denominator, seedRotation_digit_one, seedRotation_digit_two,
    seedRotation_digit_three, seedRotation_digit_tail]

theorem seedRotation_denominator_odd (n : ℕ) : Odd (actualDenominator seedRotation (n + 2)) := by
  induction n using Nat.twoStepInduction with
  | zero => rw [seedRotation_denominator_two]; decide
  | one => rw [seedRotation_denominator_three]; decide
  | more n hn hn1 =>
    change Odd (actualDigit seedRotation (n + 4) * actualDenominator seedRotation (n + 3) +
      actualDenominator seedRotation (n + 2))
    rw [seedRotation_digit_tail]
    exact (even_two_mul _).add_odd hn

end ArithmeticSections
