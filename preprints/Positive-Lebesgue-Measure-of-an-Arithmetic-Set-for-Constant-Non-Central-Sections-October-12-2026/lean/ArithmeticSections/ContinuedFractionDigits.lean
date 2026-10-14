import ArithmeticSections.DenominatorGrowth
import ArithmeticSections.IntegerDistance
import Mathlib.Algebra.ContinuedFractions.Computation.Translations
import Mathlib.Algebra.ContinuedFractions.ContinuantsRecurrence

namespace ArithmeticSections

/-- Actual complete quotients under the Gauss algorithm. -/
noncomputable def completeQuotient (θ : ℝ) : ℕ → ℝ
  | 0 => θ
  | n + 1 => (Int.fract (completeQuotient θ n))⁻¹

noncomputable def actualDigit (θ : ℝ) (n : ℕ) : ℕ := (⌊completeQuotient θ n⌋).toNat
noncomputable def actualDenominator (θ : ℝ) (n : ℕ) : ℕ := denominator (actualDigit θ) n

theorem completeQuotient_irrational {θ : ℝ} (hθ : Irrational θ) (n : ℕ) :
    Irrational (completeQuotient θ n) := by
  induction n with
  | zero => exact hθ
  | succ n ih =>
    have h := (ih.sub_intCast ⌊completeQuotient θ n⌋).inv
    simpa only [completeQuotient, Int.fract] using h

theorem completeQuotient_fract_pos {θ : ℝ} (hθ : Irrational θ) (n : ℕ) :
    0 < Int.fract (completeQuotient θ n) := by
  have hi := (completeQuotient_irrational hθ n).sub_intCast ⌊completeQuotient θ n⌋
  have hn : Int.fract (completeQuotient θ n) ≠ 0 := by simpa only [Int.fract] using hi.ne_zero
  exact lt_of_le_of_ne (Int.fract_nonneg _) hn.symm

theorem one_lt_completeQuotient_succ {θ : ℝ} (hθ : Irrational θ) (n : ℕ) :
    1 < completeQuotient θ (n + 1) := by
  exact (one_lt_inv₀ (completeQuotient_fract_pos hθ n)).mpr (Int.fract_lt_one _)

theorem one_le_actualDigit_succ {θ : ℝ} (hθ : Irrational θ) (n : ℕ) :
    1 ≤ actualDigit θ (n + 1) := by
  have h : (1 : ℤ) ≤ ⌊completeQuotient θ (n + 1)⌋ :=
    Int.le_floor.mpr (by simpa using (one_lt_completeQuotient_succ hθ n).le)
  unfold actualDigit
  omega

/-- Identification with Mathlib's computation stream. -/
theorem completeQuotient_stream {θ : ℝ} (hθ : Irrational θ) (n : ℕ) :
    GenContFract.IntFractPair.stream θ n =
      some (GenContFract.IntFractPair.of (completeQuotient θ n)) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    exact GenContFract.IntFractPair.stream_succ_of_some ih
      (ne_of_gt (completeQuotient_fract_pos hθ n))

theorem actualDigit_cast {θ : ℝ} (hθ : Irrational θ) (n : ℕ) :
    (actualDigit θ (n + 1) : ℝ) = (⌊completeQuotient θ (n + 1)⌋ : ℝ) := by
  have h : (0 : ℤ) ≤ ⌊completeQuotient θ (n + 1)⌋ :=
    Int.le_floor.mpr (by norm_num only [Int.cast_zero]; linarith [one_lt_completeQuotient_succ hθ n])
  exact_mod_cast Int.toNat_of_nonneg h

theorem actualDigit_pair {θ : ℝ} (hθ : Irrational θ) (n : ℕ) :
    (GenContFract.of θ).s.get? n = some ⟨1, (actualDigit θ (n + 1) : ℝ)⟩ := by
  rw [actualDigit_cast hθ n]
  exact GenContFract.get?_of_eq_some_of_succ_get?_intFractPair_stream
    (completeQuotient_stream hθ (n + 1))

/-- Identification with Mathlib's actual convergent denominators. -/
theorem actualDenominator_eq_mathlib {θ : ℝ} (hθ : Irrational θ) (n : ℕ) :
    (actualDenominator θ n : ℝ) = (GenContFract.of θ).dens n := by
  induction n using Nat.twoStepInduction with
  | zero => simp [actualDenominator, denominator]
  | one =>
    have hc := GenContFract.conts_recurrenceAux (actualDigit_pair hθ 0) rfl rfl
    have hd := congrArg GenContFract.Pair.b hc
    norm_num only [Nat.zero_add, GenContFract.zeroth_contAux_eq_one_zero,
      GenContFract.first_contAux_eq_h_one, mul_one, mul_zero, add_zero] at hd
    simpa only [GenContFract.den_eq_conts_b, actualDenominator, denominator] using hd.symm
  | more n hn hn1 =>
    have h := GenContFract.dens_recurrence (actualDigit_pair hθ (n + 1)) hn.symm hn1.symm
    simpa only [actualDenominator, denominator, Nat.cast_add, Nat.cast_mul, one_mul] using h.symm

theorem exponential_le_actualDenominator {θ : ℝ} (hθ : Irrational θ) (n : ℕ) :
    2 ^ (n / 2) ≤ actualDenominator θ n :=
  exponential_le_denominator (one_le_actualDigit_succ hθ) n

theorem tailThreshold_lt_actualDenominator {θ : ℝ} (hθ : Irrational θ)
    (j : ℕ) (hj : 256 ≤ j) : 72 * tailThreshold j < actualDenominator θ j :=
  tailThreshold_lt_denominator (one_le_actualDigit_succ hθ) j hj

end ArithmeticSections
