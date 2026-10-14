import ArithmeticSections.SeedFiniteDistances
import ArithmeticSections.CosineCriterion

namespace ArithmeticSections

/-- Rational enclosure; all constants are proved from Mathlib's π bounds and √2²=2. -/
theorem seedAngle_rational_bounds : (12148 : ℝ) / 10000 < Real.pi * seedRotation ∧
    Real.pi * seedRotation < 12151 / 10000 := by
  have hg := seedRotation_rational_bounds
  have hp0 := Real.pi_pos
  have hp1 := Real.pi_gt_d4
  have hp2 := Real.pi_lt_d4
  constructor <;> nlinarith

private theorem seed_cos_a :
    1 - ((12151 : ℝ) / 10000) ^ 2 / 2 + ((12151 : ℝ) / 10000) ^ 4 / 32 ≤ Real.cos (Real.pi * seedRotation) ∧
      Real.cos (Real.pi * seedRotation) ≤ 1 - ((3037 : ℝ) / 2500) ^ 2 / 2 + ((3037 : ℝ) / 2500) ^ 4 / 24 := by
  have ha := seedAngle_rational_bounds
  have hp1 := Real.pi_gt_d4
  have hp2 := Real.pi_lt_d4
  apply cosine_rational_bounds (by norm_num : (0 : ℝ) ≤ (3037 : ℝ) / 2500)
    (by norm_num : ((12151 : ℝ) / 10000) ≤ 2)
  · norm_num only [seedDistance]
    nlinarith only [ha.1, ha.2, hp1, hp2]
  · norm_num only [seedDistance]
    nlinarith only [ha.1, ha.2, hp1, hp2]

private theorem seed_cos_s2 :
    1 - ((2519 : ℝ) / 5000) ^ 2 / 2 + ((2519 : ℝ) / 5000) ^ 4 / 32 ≤ Real.cos (seedDistance 2) ∧
      Real.cos (seedDistance 2) ≤ 1 - ((1257 : ℝ) / 2500) ^ 2 / 2 + ((1257 : ℝ) / 2500) ^ 4 / 24 := by
  have ha := seedAngle_rational_bounds
  have hp1 := Real.pi_gt_d4
  have hp2 := Real.pi_lt_d4
  apply cosine_rational_bounds (by norm_num : (0 : ℝ) ≤ (1257 : ℝ) / 2500)
    (by norm_num : ((2519 : ℝ) / 5000) ≤ 2)
  · norm_num only [seedDistance]
    nlinarith only [ha.1, ha.2, hp1, hp2]
  · norm_num only [seedDistance]
    nlinarith only [ha.1, ha.2, hp1, hp2]

private theorem seed_cos_s3 :
    1 - ((523 : ℝ) / 2500) ^ 2 / 2 + ((523 : ℝ) / 2500) ^ 4 / 32 ≤ Real.cos (seedDistance 3) ∧
      Real.cos (seedDistance 3) ≤ 1 - ((83 : ℝ) / 400) ^ 2 / 2 + ((83 : ℝ) / 400) ^ 4 / 24 := by
  have ha := seedAngle_rational_bounds
  have hp1 := Real.pi_gt_d4
  have hp2 := Real.pi_lt_d4
  apply cosine_rational_bounds (by norm_num : (0 : ℝ) ≤ (83 : ℝ) / 400)
    (by norm_num : ((523 : ℝ) / 2500) ≤ 2)
  · norm_num only [seedDistance]
    nlinarith only [ha.1, ha.2, hp1, hp2]
  · norm_num only [seedDistance]
    nlinarith only [ha.1, ha.2, hp1, hp2]

private theorem seed_cos_minus2 :
    1 - ((2519 : ℝ) / 2500) ^ 2 / 2 + ((2519 : ℝ) / 2500) ^ 4 / 32 ≤ Real.cos (Real.pi * seedRotation - seedDistance 3) ∧
      Real.cos (Real.pi * seedRotation - seedDistance 3) ≤ 1 - ((1257 : ℝ) / 1250) ^ 2 / 2 + ((1257 : ℝ) / 1250) ^ 4 / 24 := by
  have ha := seedAngle_rational_bounds
  have hp1 := Real.pi_gt_d4
  have hp2 := Real.pi_lt_d4
  apply cosine_rational_bounds (by norm_num : (0 : ℝ) ≤ (1257 : ℝ) / 1250)
    (by norm_num : ((2519 : ℝ) / 2500) ≤ 2)
  · norm_num only [seedDistance]
    nlinarith only [ha.1, ha.2, hp1, hp2]
  · norm_num only [seedDistance]
    nlinarith only [ha.1, ha.2, hp1, hp2]

private theorem seed_cos_minus3 :
    1 - ((2963 : ℝ) / 10000) ^ 2 / 2 + ((2963 : ℝ) / 10000) ^ 4 / 32 ≤ Real.cos (Real.pi * seedRotation - seedDistance 4) ∧
      Real.cos (Real.pi * seedRotation - seedDistance 4) ≤ 1 - ((367 : ℝ) / 1250) ^ 2 / 2 + ((367 : ℝ) / 1250) ^ 4 / 24 := by
  have ha := seedAngle_rational_bounds
  have hp1 := Real.pi_gt_d4
  have hp2 := Real.pi_lt_d4
  apply cosine_rational_bounds (by norm_num : (0 : ℝ) ≤ (367 : ℝ) / 1250)
    (by norm_num : ((2963 : ℝ) / 10000) ≤ 2)
  · norm_num only [seedDistance]
    nlinarith only [ha.1, ha.2, hp1, hp2]
  · norm_num only [seedDistance]
    nlinarith only [ha.1, ha.2, hp1, hp2]

private theorem seed_cos_minus5 :
    1 - ((523 : ℝ) / 1250) ^ 2 / 2 + ((523 : ℝ) / 1250) ^ 4 / 32 ≤ Real.cos (Real.pi * seedRotation - seedDistance 6) ∧
      Real.cos (Real.pi * seedRotation - seedDistance 6) ≤ 1 - ((83 : ℝ) / 200) ^ 2 / 2 + ((83 : ℝ) / 200) ^ 4 / 24 := by
  have ha := seedAngle_rational_bounds
  have hp1 := Real.pi_gt_d4
  have hp2 := Real.pi_lt_d4
  apply cosine_rational_bounds (by norm_num : (0 : ℝ) ≤ (83 : ℝ) / 200)
    (by norm_num : ((523 : ℝ) / 1250) ≤ 2)
  · norm_num only [seedDistance]
    nlinarith only [ha.1, ha.2, hp1, hp2]
  · norm_num only [seedDistance]
    nlinarith only [ha.1, ha.2, hp1, hp2]

private theorem seed_cos_minus6 :
    1 - ((1413 : ℝ) / 1250) ^ 2 / 2 + ((1413 : ℝ) / 1250) ^ 4 / 32 ≤ Real.cos (Real.pi * seedRotation - seedDistance 7) ∧
      Real.cos (Real.pi * seedRotation - seedDistance 7) ≤ 1 - ((11263 : ℝ) / 10000) ^ 2 / 2 + ((11263 : ℝ) / 10000) ^ 4 / 24 := by
  have ha := seedAngle_rational_bounds
  have hp1 := Real.pi_gt_d4
  have hp2 := Real.pi_lt_d4
  apply cosine_rational_bounds (by norm_num : (0 : ℝ) ≤ (11263 : ℝ) / 10000)
    (by norm_num : ((1413 : ℝ) / 1250) ≤ 2)
  · norm_num only [seedDistance]
    nlinarith only [ha.1, ha.2, hp1, hp2]
  · norm_num only [seedDistance]
    nlinarith only [ha.1, ha.2, hp1, hp2]

private theorem seed_cos_plus2 :
    1 - ((178 : ℝ) / 125) ^ 2 / 2 + ((178 : ℝ) / 125) ^ 4 / 32 ≤ Real.cos (Real.pi * seedRotation + seedDistance 3) ∧
      Real.cos (Real.pi * seedRotation + seedDistance 3) ≤ 1 - ((7113 : ℝ) / 5000) ^ 2 / 2 + ((7113 : ℝ) / 5000) ^ 4 / 24 := by
  have ha := seedAngle_rational_bounds
  have hp1 := Real.pi_gt_d4
  have hp2 := Real.pi_lt_d4
  apply cosine_rational_bounds (by norm_num : (0 : ℝ) ≤ (7113 : ℝ) / 5000)
    (by norm_num : ((178 : ℝ) / 125) ≤ 2)
  · norm_num only [seedDistance]
    nlinarith only [ha.1, ha.2, hp1, hp2]
  · norm_num only [seedDistance]
    nlinarith only [ha.1, ha.2, hp1, hp2]

private theorem seed_cos_sum2 :
    1 - ((17189 : ℝ) / 20000) ^ 2 / 2 + ((17189 : ℝ) / 20000) ^ 4 / 32 ≤ Real.cos ((seedDistance 2 + seedDistance 1) / 2) ∧
      Real.cos ((seedDistance 2 + seedDistance 1) / 2) ≤ 1 - ((2147 : ℝ) / 2500) ^ 2 / 2 + ((2147 : ℝ) / 2500) ^ 4 / 24 := by
  have ha := seedAngle_rational_bounds
  have hp1 := Real.pi_gt_d4
  have hp2 := Real.pi_lt_d4
  apply cosine_rational_bounds (by norm_num : (0 : ℝ) ≤ (2147 : ℝ) / 2500)
    (by norm_num : ((17189 : ℝ) / 20000) ≤ 2)
  · norm_num only [seedDistance]
    nlinarith only [ha.1, ha.2, hp1, hp2]
  · norm_num only [seedDistance]
    nlinarith only [ha.1, ha.2, hp1, hp2]

private theorem seed_cos_diff2 :
    1 - ((89 : ℝ) / 250) ^ 2 / 2 + ((89 : ℝ) / 250) ^ 4 / 32 ≤ Real.cos ((seedDistance 1 - seedDistance 2) / 2) ∧
      Real.cos ((seedDistance 1 - seedDistance 2) / 2) ≤ 1 - ((7113 : ℝ) / 20000) ^ 2 / 2 + ((7113 : ℝ) / 20000) ^ 4 / 24 := by
  have ha := seedAngle_rational_bounds
  have hp1 := Real.pi_gt_d4
  have hp2 := Real.pi_lt_d4
  apply cosine_rational_bounds (by norm_num : (0 : ℝ) ≤ (7113 : ℝ) / 20000)
    (by norm_num : ((89 : ℝ) / 250) ≤ 2)
  · norm_num only [seedDistance]
    nlinarith only [ha.1, ha.2, hp1, hp2]
  · norm_num only [seedDistance]
    nlinarith only [ha.1, ha.2, hp1, hp2]

private theorem seed_cos_plus6 :
    1 - ((13039 : ℝ) / 10000) ^ 2 / 2 + ((13039 : ℝ) / 10000) ^ 4 / 32 ≤ Real.cos (Real.pi * seedRotation + seedDistance 7) ∧
      Real.cos (Real.pi * seedRotation + seedDistance 7) ≤ 1 - ((812 : ℝ) / 625) ^ 2 / 2 + ((812 : ℝ) / 625) ^ 4 / 24 := by
  have ha := seedAngle_rational_bounds
  have hp1 := Real.pi_gt_d4
  have hp2 := Real.pi_lt_d4
  apply cosine_rational_bounds (by norm_num : (0 : ℝ) ≤ (812 : ℝ) / 625)
    (by norm_num : ((13039 : ℝ) / 10000) ≤ 2)
  · norm_num only [seedDistance]
    nlinarith only [ha.1, ha.2, hp1, hp2]
  · norm_num only [seedDistance]
    nlinarith only [ha.1, ha.2, hp1, hp2]

private theorem seed_cos_sum6 :
    1 - ((89 : ℝ) / 250) ^ 2 / 2 + ((89 : ℝ) / 250) ^ 4 / 32 ≤ Real.cos ((seedDistance 3 + seedDistance 2) / 2) ∧
      Real.cos ((seedDistance 3 + seedDistance 2) / 2) ≤ 1 - ((7113 : ℝ) / 20000) ^ 2 / 2 + ((7113 : ℝ) / 20000) ^ 4 / 24 := by
  have ha := seedAngle_rational_bounds
  have hp1 := Real.pi_gt_d4
  have hp2 := Real.pi_lt_d4
  apply cosine_rational_bounds (by norm_num : (0 : ℝ) ≤ (7113 : ℝ) / 20000)
    (by norm_num : ((89 : ℝ) / 250) ≤ 2)
  · norm_num only [seedDistance]
    nlinarith only [ha.1, ha.2, hp1, hp2]
  · norm_num only [seedDistance]
    nlinarith only [ha.1, ha.2, hp1, hp2]

private theorem seed_cos_diff6 :
    1 - ((2963 : ℝ) / 20000) ^ 2 / 2 + ((2963 : ℝ) / 20000) ^ 4 / 32 ≤ Real.cos ((seedDistance 2 - seedDistance 3) / 2) ∧
      Real.cos ((seedDistance 2 - seedDistance 3) / 2) ≤ 1 - ((367 : ℝ) / 2500) ^ 2 / 2 + ((367 : ℝ) / 2500) ^ 4 / 24 := by
  have ha := seedAngle_rational_bounds
  have hp1 := Real.pi_gt_d4
  have hp2 := Real.pi_lt_d4
  apply cosine_rational_bounds (by norm_num : (0 : ℝ) ≤ (367 : ℝ) / 2500)
    (by norm_num : ((2963 : ℝ) / 20000) ≤ 2)
  · norm_num only [seedDistance]
    nlinarith only [ha.1, ha.2, hp1, hp2]
  · norm_num only [seedDistance]
    nlinarith only [ha.1, ha.2, hp1, hp2]

theorem seed_minus_sign_2 : Real.cos (seedDistance 2) *
    Real.cos (Real.pi * seedRotation - seedDistance 3) > Real.cos (Real.pi * seedRotation) := by
  have h1 := seed_cos_s2
  have h2 := seed_cos_minus2
  have h3 := seed_cos_a
  norm_num at h1 h2 h3
  nlinarith only [h1.1, h1.2, h2.1, h2.2, h3.1, h3.2]

theorem seed_minus_sign_3 : Real.cos (seedDistance 3) *
    Real.cos (Real.pi * seedRotation - seedDistance 4) > Real.cos (Real.pi * seedRotation) := by
  have h1 := seed_cos_s3
  have h2 := seed_cos_minus3
  have h3 := seed_cos_a
  norm_num at h1 h2 h3
  nlinarith only [h1.1, h1.2, h2.1, h2.2, h3.1, h3.2]

theorem seed_minus_sign_5 : Real.cos (seedDistance 3) *
    Real.cos (Real.pi * seedRotation - seedDistance 6) > Real.cos (Real.pi * seedRotation) := by
  have h1 := seed_cos_s3
  have h2 := seed_cos_minus5
  have h3 := seed_cos_a
  norm_num at h1 h2 h3
  nlinarith only [h1.1, h1.2, h2.1, h2.2, h3.1, h3.2]

theorem seed_minus_sign_6 : Real.cos (seedDistance 3) *
    Real.cos (Real.pi * seedRotation - seedDistance 7) > Real.cos (Real.pi * seedRotation) := by
  have h1 := seed_cos_s3
  have h2 := seed_cos_minus6
  have h3 := seed_cos_a
  norm_num at h1 h2 h3
  nlinarith only [h1.1, h1.2, h2.1, h2.2, h3.1, h3.2]

theorem seed_plus_sign_2 : Real.cos (Real.pi * seedRotation) *
    Real.cos ((seedDistance 2 + seedDistance 1) / 2) >
      Real.cos ((seedDistance 1 - seedDistance 2) / 2) * Real.cos (Real.pi * seedRotation + seedDistance 3) := by
  have h1 := seed_cos_a
  have h2 := seed_cos_sum2
  have h3 := seed_cos_diff2
  have h4 := seed_cos_plus2
  norm_num at h1 h2 h3 h4
  nlinarith only [h1.1, h1.2, h2.1, h2.2, h3.1, h3.2, h4.1, h4.2]

theorem seed_plus_sign_6 : Real.cos (Real.pi * seedRotation) *
    Real.cos ((seedDistance 3 + seedDistance 2) / 2) >
      Real.cos ((seedDistance 2 - seedDistance 3) / 2) * Real.cos (Real.pi * seedRotation + seedDistance 7) := by
  have h1 := seed_cos_a
  have h2 := seed_cos_sum6
  have h3 := seed_cos_diff6
  have h4 := seed_cos_plus6
  norm_num at h1 h2 h3 h4
  nlinarith only [h1.1, h1.2, h2.1, h2.2, h3.1, h3.2, h4.1, h4.2]

/-- The original five initial inequalities, with exact order statistics and cosine signs. -/
theorem seed_condition_initial (k : ℕ) (hk : k ∈ Finset.Icc 2 6) :
    0 < conditionGap seedRotation k := by
  obtain ⟨hklo, hkhi⟩ := Finset.mem_Icc.mp hk
  have hs := (seed_first_second_initial k hk).1
  have ht := (seed_first_second_initial k hk).2
  have hd := oddDistance_seed (k + 1) (by apply Finset.mem_Icc.mpr; omega)
  apply condition_of_cosine_signs seedRotation_irrational seedRotation_bounds.1 seedRotation_bounds.2 hklo
  · rw [hs, hd]
    interval_cases k
    · exact Or.inr (by simpa using seed_minus_sign_2)
    · exact Or.inr (by simpa using seed_minus_sign_3)
    · apply Or.inl
      have hg := seedRotation_rational_bounds
      norm_num [seedDistance]
      nlinarith [Real.pi_pos]
    · exact Or.inr (by simpa using seed_minus_sign_5)
    · exact Or.inr (by simpa using seed_minus_sign_6)
  · rw [hs, ht, hd]
    interval_cases k
    · exact Or.inr (by simpa using seed_plus_sign_2)
    · apply Or.inl
      have hg := seedRotation_rational_bounds
      norm_num [seedDistance]
      nlinarith [Real.pi_pos]
    · apply Or.inl
      have hg := seedRotation_rational_bounds
      norm_num [seedDistance]
      nlinarith [Real.pi_pos]
    · apply Or.inl
      have hg := seedRotation_rational_bounds
      norm_num [seedDistance]
      nlinarith [Real.pi_pos]
    · exact Or.inr (by simpa using seed_plus_sign_6)

/-- All infinitely many strict conditions hold at the original explicit seed. -/
theorem seed_all_conditions (k : ℕ) (hk : 2 ≤ k) : 0 < conditionGap seedRotation k := by
  by_cases h : k ≤ 6
  · exact seed_condition_initial k (Finset.mem_Icc.mpr ⟨hk, h⟩)
  · exact seed_condition_tail (by omega)

/-- The seed lies above the required volume threshold. -/
theorem seed_tan_gt_two : 2 < Real.tan (Real.pi * seedRotation) := by
  have ha := seedAngle_rational_bounds
  have hc := seed_cos_a
  have hs := Real.sin_ge_sub_cube (x := Real.pi * seedRotation) (by linarith : 0 ≤ Real.pi * seedRotation)
  have hca : 0 < Real.cos (Real.pi * seedRotation) :=
    Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos], by nlinarith [Real.pi_pos, seedRotation_bounds.2]⟩
  have hh : Real.pi * seedRotation < 13 / 10 := by linarith
  have hpow := pow_le_pow_left₀ (by linarith : 0 ≤ Real.pi * seedRotation) hh.le 3
  norm_num at hc hpow
  rw [Real.tan_eq_sin_div_cos]
  apply (lt_div_iff₀ hca).mpr
  nlinarith only [ha.1, hs, hc.2, hpow]

end ArithmeticSections
