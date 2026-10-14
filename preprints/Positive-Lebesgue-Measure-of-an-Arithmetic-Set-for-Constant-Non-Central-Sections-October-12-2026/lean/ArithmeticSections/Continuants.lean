import ArithmeticSections.ContinuedFractionDigits

namespace ArithmeticSections

def numerator (b : ℕ → ℕ) : ℕ → ℕ
  | 0 => 0
  | 1 => 1
  | n + 2 => b (n + 2) * numerator b (n + 1) + numerator b n

theorem continuant_determinant (b : ℕ → ℕ) (n : ℕ) :
    (numerator b (n + 1) : ℤ) * denominator b n -
      (numerator b n : ℤ) * denominator b (n + 1) = (-1) ^ n := by
  induction n with
  | zero => simp [numerator, denominator]
  | succ n ih =>
    change (numerator b (n + 2) : ℤ) * denominator b (n + 1) -
      (numerator b (n + 1) : ℤ) * denominator b (n + 2) = (-1) ^ (n + 1)
    rw [numerator, denominator]
    push_cast
    rw [pow_succ]
    nlinarith

theorem denominator_pos {b : ℕ → ℕ} (hb : ∀ n, 1 ≤ b (n + 1)) (n : ℕ) :
    0 < denominator b n := lt_of_lt_of_le (by positivity) (exponential_le_denominator hb n)

noncomputable def cylinderMap (b : ℕ → ℕ) (n : ℕ) (t : ℝ) : ℝ :=
  ((numerator b (n + 1) : ℝ) + numerator b n * t) /
    ((denominator b (n + 1) : ℝ) + denominator b n * t)

theorem cylinderMap_sub {b : ℕ → ℕ} (hb : ∀ n, 1 ≤ b (n + 1)) (n : ℕ)
    {x y : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) :
    cylinderMap b n y - cylinderMap b n x =
      (-1 : ℝ) ^ (n + 1) * (y - x) /
        (((denominator b (n + 1) : ℝ) + denominator b n * x) *
          ((denominator b (n + 1) : ℝ) + denominator b n * y)) := by
  have hq : (0 : ℝ) < denominator b (n + 1) := by exact_mod_cast denominator_pos hb (n + 1)
  have hq0 : (0 : ℝ) ≤ denominator b n := by positivity
  have hdx : (denominator b (n + 1) : ℝ) + denominator b n * x ≠ 0 := by positivity
  have hdy : (denominator b (n + 1) : ℝ) + denominator b n * y ≠ 0 := by positivity
  have hd : (numerator b (n + 1) : ℝ) * denominator b n -
      (numerator b n : ℝ) * denominator b (n + 1) = (-1 : ℝ) ^ n := by
    exact_mod_cast continuant_determinant b n
  unfold cylinderMap
  field_simp
  rw [pow_succ]
  nlinarith [congrArg (fun z : ℝ => z * (y - x)) hd]

theorem cylinderMap_initial_length {b : ℕ → ℕ} (hb : ∀ n, 1 ≤ b (n + 1))
    (n : ℕ) {z : ℝ} (hz : 0 ≤ z) :
    |cylinderMap b n z - cylinderMap b n 0| =
      z / ((denominator b (n + 1) : ℝ) *
        ((denominator b (n + 1) : ℝ) + denominator b n * z)) := by
  rw [cylinderMap_sub hb n (by norm_num) hz]
  simp only [mul_zero, add_zero, sub_zero, abs_div, abs_mul, abs_pow,
    abs_neg, abs_one, one_pow, one_mul, abs_of_nonneg hz]
  have hq : (0 : ℝ) < denominator b (n + 1) := by exact_mod_cast denominator_pos hb (n + 1)
  rw [abs_of_pos hq, abs_of_pos (by positivity)]

theorem cylinderMap_length_ratio_le {b : ℕ → ℕ} (hb : ∀ n, 1 ≤ b (n + 1))
    (n : ℕ) {z : ℝ} (hz : 0 ≤ z) :
    |cylinderMap b n z - cylinderMap b n 0| ≤
      2 * z * |cylinderMap b n 1 - cylinderMap b n 0| := by
  rw [cylinderMap_initial_length hb n hz, cylinderMap_initial_length hb n (by norm_num)]
  have hq : (0 : ℝ) < denominator b (n + 1) := by exact_mod_cast denominator_pos hb (n + 1)
  have hprev : (denominator b n : ℝ) ≤ denominator b (n + 1) := by
    exact_mod_cast denominator_mono_step hb n
  have hr : ((denominator b (n + 1) : ℝ) + denominator b n) /
      ((denominator b (n + 1) : ℝ) + denominator b n * z) ≤ 2 := by
    apply (div_le_iff₀ (by positivity)).mpr
    have hzq : (0 : ℝ) ≤ denominator b n * z := by positivity
    linarith
  have h := mul_le_mul_of_nonneg_left hr
    (show 0 ≤ z / ((denominator b (n + 1) : ℝ) *
      ((denominator b (n + 1) : ℝ) + denominator b n)) by positivity)
  convert h using 1 <;> field_simp

end ArithmeticSections
