import ArithmeticSections.OddDistances

namespace ArithmeticSections

noncomputable def seedRotation : ℝ := (4 + Real.sqrt 2) / 14
noncomputable def seedDoubledRotation : ℝ := (4 + Real.sqrt 2) / 7

theorem seedDoubledRotation_eq : seedDoubledRotation = 2 * seedRotation := by
  unfold seedDoubledRotation seedRotation
  ring

theorem seedRotation_irrational : Irrational seedRotation := by
  have h := (irrational_sqrt_two.ratCast_add 4).div_ratCast (q := 14) (by norm_num)
  simpa [seedRotation] using h

theorem seedDoubledRotation_irrational : Irrational seedDoubledRotation := by
  have h := seedRotation_irrational.mul_ratCast (q := 2) (by norm_num)
  simpa [seedDoubledRotation_eq, mul_comm] using h

theorem seedRotation_bounds : 1 / 3 < seedRotation ∧ seedRotation < 1 / 2 := by
  have hs := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)
  have hp := Real.sqrt_nonneg (2 : ℝ)
  unfold seedRotation
  constructor <;> nlinarith

theorem seed_inversion_identities :
    1 / seedDoubledRotation = 1 + (2 - Real.sqrt 2) / 2 ∧
    2 / (2 - Real.sqrt 2) = 3 + (Real.sqrt 2 - 1) ∧
    1 / (Real.sqrt 2 - 1) = 2 + (Real.sqrt 2 - 1) := by
  have hs := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)
  have hp := Real.sqrt_nonneg (2 : ℝ)
  have h1 : 4 + Real.sqrt 2 ≠ 0 := by nlinarith
  have h2 : 2 - Real.sqrt 2 ≠ 0 := by nlinarith
  have h3 : Real.sqrt 2 - 1 ≠ 0 := by nlinarith
  unfold seedDoubledRotation
  constructor
  · field_simp
    nlinarith
  constructor
  · apply (div_eq_iff h2).mpr
    nlinarith
  · apply (div_eq_iff h3).mpr
    nlinarith

end ArithmeticSections
