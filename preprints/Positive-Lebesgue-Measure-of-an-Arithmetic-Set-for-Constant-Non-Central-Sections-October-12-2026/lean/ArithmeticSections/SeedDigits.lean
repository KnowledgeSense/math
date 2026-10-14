import ArithmeticSections.Seed
import ArithmeticSections.ContinuedFractionDigits

namespace ArithmeticSections

private theorem sqrt_two_bounds : 1 < Real.sqrt 2 ∧ Real.sqrt 2 < 2 := by
  have hs := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)
  have hp := Real.sqrt_nonneg (2 : ℝ)
  constructor <;> nlinarith

theorem seed_floor_zero : ⌊seedDoubledRotation⌋ = (0 : ℤ) := by
  apply Int.floor_eq_iff.mpr
  have hb := seedRotation_bounds
  rw [seedDoubledRotation_eq]
  norm_num only [Int.cast_zero, Int.cast_one, Int.cast_ofNat]
  constructor <;> linarith

theorem seed_completeQuotient_one :
    completeQuotient seedDoubledRotation 1 = 1 + (2 - Real.sqrt 2) / 2 := by
  simpa only [completeQuotient, Int.fract, seed_floor_zero, Int.cast_zero, sub_zero, one_div]
    using seed_inversion_identities.1

theorem seed_floor_one : ⌊completeQuotient seedDoubledRotation 1⌋ = (1 : ℤ) := by
  rw [seed_completeQuotient_one]
  apply Int.floor_eq_iff.mpr
  have hb := sqrt_two_bounds
  norm_num only [Int.cast_zero, Int.cast_one, Int.cast_ofNat]
  constructor <;> linarith

theorem seed_completeQuotient_two :
    completeQuotient seedDoubledRotation 2 = 3 + (Real.sqrt 2 - 1) := by
  change (Int.fract (completeQuotient seedDoubledRotation 1))⁻¹ = _
  rw [Int.fract, seed_floor_one, seed_completeQuotient_one]
  norm_num only [Int.cast_one]
  calc
    (1 + (2 - Real.sqrt 2) / 2 - 1)⁻¹ = ((2 - Real.sqrt 2) / 2)⁻¹ := by congr 1; ring
    _ = 2 / (2 - Real.sqrt 2) := inv_div _ _
    _ = 3 + (Real.sqrt 2 - 1) := seed_inversion_identities.2.1

theorem seed_floor_two : ⌊completeQuotient seedDoubledRotation 2⌋ = (3 : ℤ) := by
  rw [seed_completeQuotient_two]
  apply Int.floor_eq_iff.mpr
  have hb := sqrt_two_bounds
  norm_num only [Int.cast_zero, Int.cast_one, Int.cast_ofNat]
  constructor <;> linarith

private theorem seed_tail_floor : ⌊(2 + (Real.sqrt 2 - 1))⌋ = (2 : ℤ) := by
  apply Int.floor_eq_iff.mpr
  have hb := sqrt_two_bounds
  norm_num only [Int.cast_zero, Int.cast_one, Int.cast_ofNat]
  constructor <;> linarith

theorem seed_completeQuotient_tail (n : ℕ) :
    completeQuotient seedDoubledRotation (n + 3) = 2 + (Real.sqrt 2 - 1) := by
  induction n with
  | zero =>
    change (Int.fract (completeQuotient seedDoubledRotation 2))⁻¹ = _
    rw [Int.fract, seed_floor_two, seed_completeQuotient_two]
    norm_num only [Int.cast_ofNat]
    convert seed_inversion_identities.2.2 using 1
    simp only [one_div]
    congr 1
    ring
  | succ n ih =>
    change (Int.fract (completeQuotient seedDoubledRotation (n + 3)))⁻¹ = _
    rw [ih, Int.fract, seed_tail_floor]
    norm_num only [Int.cast_ofNat]
    convert seed_inversion_identities.2.2 using 1
    simp only [one_div]
    congr 1
    ring

theorem seed_actualDigit_one : actualDigit seedDoubledRotation 1 = 1 := by
  simp only [actualDigit, seed_floor_one, Int.toNat_one]

theorem seed_actualDigit_two : actualDigit seedDoubledRotation 2 = 3 := by
  simp [actualDigit, seed_floor_two]

theorem seed_actualDigit_tail (n : ℕ) : actualDigit seedDoubledRotation (n + 3) = 2 := by
  rw [actualDigit, seed_completeQuotient_tail, seed_tail_floor]
  rfl

theorem seed_actualDigit_le_square (l : ℕ) : actualDigit seedDoubledRotation l ≤ l ^ 2 := by
  rcases l with _ | (_ | (_ | n))
  · simp [actualDigit, completeQuotient, seed_floor_zero]
  · simp [seed_actualDigit_one]
  · norm_num [seed_actualDigit_two]
  · rw [seed_actualDigit_tail]
    change 2 ≤ (n + 3) ^ 2
    have h := Nat.pow_le_pow_left (show 3 ≤ n + 3 by omega) 2
    norm_num at h
    omega

end ArithmeticSections
