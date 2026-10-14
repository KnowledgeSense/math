import ArithmeticSections.Continuants
import Mathlib.Algebra.ContinuedFractions.Computation.Approximations

namespace ArithmeticSections

noncomputable def actualNumerator (θ : ℝ) (n : ℕ) : ℕ := numerator (actualDigit θ) n

theorem actualNumerator_eq_mathlib {θ : ℝ} (hθ : Irrational θ)
    (hlo : 0 ≤ θ) (hhi : θ < 1) (n : ℕ) :
    (actualNumerator θ n : ℝ) = (GenContFract.of θ).nums n := by
  have hf : ⌊θ⌋ = (0 : ℤ) := Int.floor_eq_iff.mpr (by simpa using And.intro hlo hhi)
  induction n using Nat.twoStepInduction with
  | zero => simp [actualNumerator, numerator, GenContFract.of_h_eq_floor, hf]
  | one =>
    have hc := GenContFract.conts_recurrenceAux (actualDigit_pair hθ 0) rfl rfl
    have hd := congrArg GenContFract.Pair.a hc
    norm_num only [Nat.zero_add, GenContFract.zeroth_contAux_eq_one_zero,
      GenContFract.first_contAux_eq_h_one, GenContFract.of_h_eq_floor, hf,
      Int.cast_zero, mul_one, mul_zero, add_zero, zero_add] at hd
    simpa only [GenContFract.num_eq_conts_a, actualNumerator, numerator, Nat.cast_one] using hd.symm
  | more n hn hn1 =>
    have h := GenContFract.nums_recurrence (actualDigit_pair hθ (n + 1)) hn.symm hn1.symm
    simpa only [actualNumerator, numerator, Nat.cast_add, Nat.cast_mul, one_mul] using h.symm

set_option backward.isDefEq.respectTransparency false in
/-- Exact error of each non-initial convergent of an irrational in (0,1). -/
theorem actual_error_formula {θ : ℝ} (hθ : Irrational θ)
    (hlo : 0 ≤ θ) (hhi : θ < 1) (n : ℕ) :
    |(actualDenominator θ (n + 1) : ℝ) * θ - actualNumerator θ (n + 1)| =
      1 / (completeQuotient θ (n + 2) * actualDenominator θ (n + 1) + actualDenominator θ n) := by
  have h := GenContFract.sub_convs_eq (completeQuotient_stream hθ (n + 1))
  have hfr := ne_of_gt (completeQuotient_fract_pos hθ (n + 1))
  dsimp only [GenContFract.IntFractPair.of] at h
  rw [ite_eq_right hfr] at h
  change θ - (GenContFract.of θ).convs (n + 1) =
    (-1 : ℝ) ^ (n + 1) / ((GenContFract.of θ).dens (n + 1) *
      (completeQuotient θ (n + 2) * (GenContFract.of θ).dens (n + 1) +
        (GenContFract.of θ).dens n)) at h
  rw [GenContFract.conv_eq_num_div_den,
    ← actualNumerator_eq_mathlib hθ hlo hhi (n + 1),
    ← actualDenominator_eq_mathlib hθ (n + 1), ← actualDenominator_eq_mathlib hθ n] at h
  have hq : (0 : ℝ) < actualDenominator θ (n + 1) := by
    exact_mod_cast denominator_pos (one_le_actualDigit_succ hθ) (n + 1)
  have hc : 0 < completeQuotient θ (n + 2) := by linarith [one_lt_completeQuotient_succ hθ (n + 1)]
  have hd : 0 < completeQuotient θ (n + 2) * actualDenominator θ (n + 1) + actualDenominator θ n := by positivity
  calc
    |(actualDenominator θ (n + 1) : ℝ) * θ - actualNumerator θ (n + 1)| =
        (actualDenominator θ (n + 1) : ℝ) *
          |θ - actualNumerator θ (n + 1) / (actualDenominator θ (n + 1) : ℝ)| := by
      have he : (actualDenominator θ (n + 1) : ℝ) * θ - actualNumerator θ (n + 1) =
          (actualDenominator θ (n + 1) : ℝ) *
            (θ - actualNumerator θ (n + 1) / (actualDenominator θ (n + 1) : ℝ)) := by
        field_simp
      rw [he, abs_mul, abs_of_pos hq]
    _ = (actualDenominator θ (n + 1) : ℝ) *
      (1 / ((actualDenominator θ (n + 1) : ℝ) *
        (completeQuotient θ (n + 2) * actualDenominator θ (n + 1) + actualDenominator θ n))) := by
      rw [h]
      simp only [abs_div, abs_pow, abs_neg, abs_one, one_pow, abs_mul, abs_of_pos hq, abs_of_pos hd]
    _ = _ := by field_simp

/-- Both strict error bounds in equation (2.4), for n≥1. -/
theorem actual_error_bounds {θ : ℝ} (hθ : Irrational θ)
    (hlo : 0 ≤ θ) (hhi : θ < 1) (n : ℕ) :
    1 / ((actualDenominator θ (n + 1) : ℝ) * (actualDigit θ (n + 2) + 2)) <
      |(actualDenominator θ (n + 1) : ℝ) * θ - actualNumerator θ (n + 1)| ∧
    |(actualDenominator θ (n + 1) : ℝ) * θ - actualNumerator θ (n + 1)| <
      1 / (actualDenominator θ (n + 2) : ℝ) := by
  rw [actual_error_formula hθ hlo hhi]
  have hq : (0 : ℝ) < actualDenominator θ (n + 1) := by
    exact_mod_cast denominator_pos (one_le_actualDigit_succ hθ) (n + 1)
  have hqnext : (0 : ℝ) < actualDenominator θ (n + 2) := by
    exact_mod_cast denominator_pos (one_le_actualDigit_succ hθ) (n + 2)
  have hprev : (actualDenominator θ n : ℝ) ≤ actualDenominator θ (n + 1) := by
    exact_mod_cast denominator_mono_step (one_le_actualDigit_succ hθ) n
  have hdown : (actualDigit θ (n + 2) : ℝ) < completeQuotient θ (n + 2) := by
    rw [actualDigit_cast hθ (n + 1)]
    have hf := completeQuotient_fract_pos hθ (n + 2)
    unfold Int.fract at hf
    linarith
  have hup : completeQuotient θ (n + 2) < (actualDigit θ (n + 2) : ℝ) + 1 := by
    rw [actualDigit_cast hθ (n + 1)]
    exact Int.lt_floor_add_one _
  have hrec : (actualDenominator θ (n + 2) : ℝ) =
      actualDigit θ (n + 2) * (actualDenominator θ (n + 1) : ℝ) + actualDenominator θ n := by
    simp only [actualDenominator, denominator, Nat.cast_add, Nat.cast_mul]
  have hc : 0 < completeQuotient θ (n + 2) := by linarith [one_lt_completeQuotient_succ hθ (n + 1)]
  have hd : 0 < completeQuotient θ (n + 2) * actualDenominator θ (n + 1) + actualDenominator θ n := by positivity
  constructor
  · apply one_div_lt_one_div_of_lt hd
    nlinarith [mul_lt_mul_of_pos_right hup hq]
  · apply one_div_lt_one_div_of_lt hqnext
    nlinarith [mul_lt_mul_of_pos_right hdown hq]

end ArithmeticSections
