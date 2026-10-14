import ArithmeticSections.SeedConvergents
import ArithmeticSections.TailCriterion

namespace ArithmeticSections

theorem denominator_strict_step {b : ℕ → ℕ} (hb : ∀ n, 1 ≤ b (n + 1))
    {n : ℕ} (hn : 1 ≤ n) : denominator b n < denominator b (n + 1) := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : n ≠ 0)
  have hp := denominator_pos hb m
  have hd := hb (m + 1)
  change denominator b (m + 1) < b (m + 2) * denominator b (m + 1) + denominator b m
  nlinarith

/-- A convergent with odd denominator supplies one of the actual odd multiples. -/
theorem oddDistance_convergent_upper {γ : ℝ} (hγ : Irrational γ)
    (hlo : 0 ≤ γ) (hhi : γ < 1) (n r : ℕ)
    (hr : 2 * r = actualDenominator γ (n + 1) + 1) :
    oddDistance γ r < Real.pi / (actualDenominator γ (n + 2) : ℝ) := by
  have he : (2 * (r : ℝ) - 1) * γ = (actualDenominator γ (n + 1) : ℝ) * γ := by
    have hrR : 2 * (r : ℝ) = actualDenominator γ (n + 1) + 1 := by exact_mod_cast hr
    nlinarith
  have hdist := integerDistance_le_sub_integer ((actualDenominator γ (n + 1) : ℝ) * γ)
    (actualNumerator γ (n + 1))
  have h := mul_lt_mul_of_pos_left (lt_of_le_of_lt hdist (actual_error_bounds hγ hlo hhi n).2) Real.pi_pos
  unfold oddDistance
  rw [he]
  simpa only [mul_one_div] using h

/-- The seed satisfies every arithmetic condition from k=7 onward.
This direct proof uses actual odd convergents and does not assume the cited HR theorem. -/
theorem seed_condition_tail {k : ℕ} (hk : 7 ≤ k) : 0 < conditionGap seedRotation k := by
  have hγ := seedRotation_irrational
  have hlo := seedRotation_bounds.1
  have hhi := seedRotation_bounds.2
  have hlo0 : 0 ≤ seedRotation := by linarith
  have hhi1 : seedRotation < 1 := by linarith
  have hm : actualDenominator seedRotation 4 ≤ 2 * k - 1 := by
    rw [seedRotation_denominator_four]
    omega
  obtain ⟨j, hj, hqj, hqnext⟩ := exists_denominator_bracket (one_le_actualDigit_succ hγ) 4 (2 * k - 1) hm
  change actualDenominator seedRotation j ≤ 2 * k - 1 at hqj
  change 2 * k - 1 < actualDenominator seedRotation (j + 1) at hqnext
  have hj1 : j - 1 + 1 = j := by omega
  have hj2 : j - 2 + 1 = j - 1 := by omega
  have hj3 : j - 2 + 2 = j := by omega
  have hj4 : j - 1 + 2 = j + 1 := by omega
  have ho : Odd (actualDenominator seedRotation j) := by
    simpa only [show j - 2 + 2 = j by omega] using seedRotation_denominator_odd (j - 2)
  have hop : Odd (actualDenominator seedRotation (j - 1)) := by
    simpa only [show j - 3 + 2 = j - 1 by omega] using seedRotation_denominator_odd (j - 3)
  have hon : Odd (actualDenominator seedRotation (j + 1)) := by
    simpa only [show j - 1 + 2 = j + 1 by omega] using seedRotation_denominator_odd (j - 1)
  obtain ⟨a, ha⟩ := ho
  obtain ⟨b, hb⟩ := hop
  obtain ⟨c, hc⟩ := hon
  have hqp : actualDenominator seedRotation (j - 1) < actualDenominator seedRotation j := by
    simpa only [hj1, actualDenominator] using denominator_strict_step (one_le_actualDigit_succ hγ) (show 1 ≤ j - 1 by omega)
  have hqn : actualDenominator seedRotation j ≤ actualDenominator seedRotation (j + 1) :=
    denominator_mono_step (one_le_actualDigit_succ hγ) j
  have har : 2 * (a + 1) = actualDenominator seedRotation j + 1 := by omega
  have hbr : 2 * (b + 1) = actualDenominator seedRotation (j - 1) + 1 := by omega
  have haq : a + 1 ≤ k := by omega
  have hbq : b + 1 ≤ k := by omega
  have hab : a ≠ b := by omega
  have hdu := oddDistance_convergent_upper hγ hlo0 hhi1 (j - 1) (a + 1) (by simpa only [hj1] using har)
  rw [hj4] at hdu
  have hdv := oddDistance_convergent_upper hγ hlo0 hhi1 (j - 2) (b + 1) (by simpa only [hj2] using hbr)
  rw [hj3] at hdv
  have hqpos : (0 : ℝ) < actualDenominator seedRotation j := by exact_mod_cast denominator_pos (one_le_actualDigit_succ hγ) j
  have hqnpos : (0 : ℝ) < actualDenominator seedRotation (j + 1) := by exact_mod_cast denominator_pos (one_le_actualDigit_succ hγ) (j + 1)
  have hq13 : 13 ≤ actualDenominator seedRotation j := by
    rw [← seedRotation_denominator_four]
    exact denominator_monotone (one_le_actualDigit_succ hγ) hj
  have hq13R : (13 : ℝ) ≤ actualDenominator seedRotation j := by exact_mod_cast hq13
  have hqRn : (actualDenominator seedRotation j : ℝ) ≤ actualDenominator seedRotation (j + 1) := by exact_mod_cast hqn
  have hs : firstDistance seedRotation k < Real.pi / (actualDenominator seedRotation (j + 1) : ℝ) :=
    lt_of_le_of_lt (firstDistance_le (by omega : 1 ≤ a + 1) haq) hdu
  have ht : secondDistance seedRotation k < Real.pi / (actualDenominator seedRotation j : ℝ) := by
    apply lt_of_le_of_lt (secondDistance_le_pair (by omega : a < k) (by omega : b < k) hab)
    apply max_lt
    · exact hdu.trans_le (div_le_div_of_nonneg_left Real.pi_pos.le hqpos hqRn)
    · exact hdv
  have htquarter : secondDistance seedRotation k ≤ 1 / 4 := by
    have hh : Real.pi / (actualDenominator seedRotation j : ℝ) < 1 / 4 := by
      apply (div_lt_iff₀ hqpos).mpr
      nlinarith only [hq13R, Real.pi_lt_d2]
    exact (ht.trans hh).le
  have hmax := max_deviation_le_product hγ hlo hhi (by omega : 2 ≤ k) htquarter
  have hspos := firstDistance_pos hγ (by omega : 1 ≤ k)
  have htpos : 0 < secondDistance seedRotation k := lt_trans hspos (firstDistance_lt_second hγ (by omega))
  have hu : max (minusDeviation seedRotation k) (plusDeviation seedRotation k) <
      (Real.pi / (actualDenominator seedRotation (j + 1) : ℝ)) *
      (Real.pi / (actualDenominator seedRotation j : ℝ)) :=
    lt_of_le_of_lt hmax (mul_lt_mul hs ht.le htpos (by positivity))
  have hdigit : actualDigit seedRotation (j + 2) = 2 := by
    simpa only [show j - 2 + 4 = j + 2 by omega] using seedRotation_digit_tail (j - 2)
  have hd := integerDistance_lower_bound hγ hlo0 hhi1 j (2 * k + 1)
    (by omega) (by omega : 2 * k + 1 ≤ actualDenominator seedRotation (j + 1))
  rw [hdigit] at hd
  norm_num only [Nat.cast_ofNat] at hd
  have hl := mul_lt_mul_of_pos_left hd Real.pi_pos
  have he : (((2 * k + 1 : ℕ) : ℝ) * seedRotation) = (2 * ((k + 1 : ℕ) : ℝ) - 1) * seedRotation := by push_cast; ring
  rw [he] at hl
  change Real.pi * (1 / ((actualDenominator seedRotation (j + 1) : ℝ) * 4)) <
    oddDistance seedRotation (k + 1) at hl
  have hcpr : (Real.pi / (actualDenominator seedRotation (j + 1) : ℝ)) *
      (Real.pi / (actualDenominator seedRotation j : ℝ)) <
      Real.pi * (1 / ((actualDenominator seedRotation (j + 1) : ℝ) * 4)) := by
    have hh : Real.pi / (actualDenominator seedRotation j : ℝ) < 1 / 4 := by
      apply (div_lt_iff₀ hqpos).mpr
      nlinarith only [hq13R, Real.pi_lt_d2]
    have h := mul_lt_mul_of_pos_left hh (show 0 < Real.pi / (actualDenominator seedRotation (j + 1) : ℝ) by positivity)
    convert h using 1
    ring
  unfold conditionGap
  linarith only [hu, hcpr, hl]

end ArithmeticSections
