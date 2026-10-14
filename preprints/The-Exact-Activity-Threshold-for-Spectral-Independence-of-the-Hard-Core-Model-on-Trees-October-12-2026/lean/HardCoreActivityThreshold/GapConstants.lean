import HardCoreActivityThreshold.FieldBoosting

/-! Explicit, size-independent constants for reducing capped activities to at most one half. -/
namespace HardCoreActivityThreshold

noncomputable def halfActivityField (Λ : ℝ) : ℝ := 1 / (2 * max 1 Λ)

theorem halfActivityField_pos (Λ : ℝ) : 0 < halfActivityField Λ := by
  unfold halfActivityField
  have hm : 0 < max (1 : ℝ) Λ := lt_of_lt_of_le zero_lt_one (le_max_left _ _)
  positivity

theorem halfActivityField_le_half (Λ : ℝ) : halfActivityField Λ ≤ 1 / 2 := by
  unfold halfActivityField
  have hm : 1 ≤ max (1 : ℝ) Λ := le_max_left _ _
  have hp : 0 < 2 * max (1 : ℝ) Λ := by linarith
  apply (div_le_iff₀ hp).mpr
  linarith

theorem halfActivityField_lt_one (Λ : ℝ) : halfActivityField Λ < 1 :=
  lt_of_le_of_lt (halfActivityField_le_half Λ) (by norm_num)

theorem halfActivityField_mul_le_half (Λ a : ℝ) (ha : a ≤ Λ) :
    halfActivityField Λ * a ≤ 1 / 2 := by
  have hm : 0 < max (1 : ℝ) Λ := lt_of_lt_of_le zero_lt_one (le_max_left _ _)
  have ha' : a ≤ max (1 : ℝ) Λ := ha.trans (le_max_right _ _)
  unfold halfActivityField
  rw [one_div_mul_eq_div]
  apply (div_le_iff₀ (mul_pos (by norm_num) hm)).mpr
  nlinarith

/-- The resulting positive numerator in the uniform `c / n` heat-bath gap. -/
noncomputable def boostedForestGapConstant (Λ B : ℝ) : ℝ :=
  halfActivityField Λ ^ Nat.ceil B / 18

theorem boostedForestGapConstant_pos (Λ B : ℝ) : 0 < boostedForestGapConstant Λ B :=
  div_pos (pow_pos (halfActivityField_pos Λ) _) (by norm_num)

theorem boostedForestGapConstant_le_one (Λ B : ℝ) : boostedForestGapConstant Λ B ≤ 1 := by
  unfold boostedForestGapConstant
  have hp : halfActivityField Λ ^ Nat.ceil B ≤ 1 :=
    pow_le_one₀ (halfActivityField_pos Λ).le (halfActivityField_lt_one Λ).le
  apply (div_le_one (by norm_num : (0 : ℝ) < 18)).mpr
  linarith

end HardCoreActivityThreshold
