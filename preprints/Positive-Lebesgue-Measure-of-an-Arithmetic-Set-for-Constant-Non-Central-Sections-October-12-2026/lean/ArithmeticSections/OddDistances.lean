import ArithmeticSections.IntegerDistance
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan

namespace ArithmeticSections

/-- The paper's δ_{A,k}, expressed through γ. -/
noncomputable def oddDistance (γ : ℝ) (k : ℕ) : ℝ :=
  Real.pi * integerDistance ((2 * (k : ℝ) - 1) * γ)

theorem continuous_oddDistance (k : ℕ) : Continuous (fun γ => oddDistance γ k) :=
  continuous_const.mul (continuous_integerDistance.comp (continuous_const.mul continuous_id))

theorem odd_multiple_irrational {γ : ℝ} (hγ : Irrational γ) {k : ℕ} (_hk : 1 ≤ k) :
    Irrational ((2 * (k : ℝ) - 1) * γ) := by
  have h := hγ.mul_intCast (show 2 * (k : ℤ) - 1 ≠ 0 by omega)
  simpa only [Int.cast_sub, Int.cast_mul, Int.cast_ofNat, Int.cast_natCast,
    Int.cast_one, mul_comm γ] using h

theorem oddDistance_bounds {γ : ℝ} (hγ : Irrational γ) {k : ℕ} (hk : 1 ≤ k) :
    0 < oddDistance γ k ∧ oddDistance γ k < Real.pi / 2 := by
  have hi := odd_multiple_irrational hγ hk
  have hp := integerDistance_pos hi
  have hu := integerDistance_lt_half hi
  constructor
  · exact mul_pos Real.pi_pos hp
  · unfold oddDistance
    nlinarith [Real.pi_pos]

theorem oddDistance_ne {γ : ℝ} (hγ : Irrational γ)
    {k l : ℕ} (hk : 1 ≤ k) (hl : 1 ≤ l) (hkl : k ≠ l) :
    oddDistance γ k ≠ oddDistance γ l := by
  have h := integerDistance_mul_ne hγ
    (m := 2 * (k : ℤ) - 1) (n := 2 * (l : ℤ) - 1)
    (by omega) (by omega) (by omega)
  simp only [Int.cast_sub, Int.cast_mul, Int.cast_ofNat, Int.cast_natCast, Int.cast_one] at h
  exact fun he => h ((mul_left_cancel₀ Real.pi_ne_zero) he)

theorem oddDistance_one {γ : ℝ} (hlo : 1 / 3 < γ) (hhi : γ < 1 / 2) :
    oddDistance γ 1 = Real.pi * γ := by
  have hr : round γ = 0 := round_eq_zero_iff.mpr ⟨by linarith, hhi⟩
  simp only [oddDistance, Nat.cast_one]
  norm_num
  simp only [integerDistance, hr, Int.cast_zero, sub_zero]
  rw [abs_of_pos (by linarith)]

theorem oddDistance_two {γ : ℝ} (hlo : 1 / 3 < γ) (hhi : γ < 1 / 2) :
    oddDistance γ 2 = Real.pi * (3 * γ - 1) := by
  have hr : round (3 * γ) = 1 := round_eq_iff.mpr ⟨by norm_num; linarith, by norm_num; linarith⟩
  norm_num [oddDistance, integerDistance, hr, abs_of_pos (show 0 < 3 * γ - 1 by linarith)]

theorem oddDistance_two_lt_one {γ : ℝ} (hlo : 1 / 3 < γ) (hhi : γ < 1 / 2) :
    oddDistance γ 2 < oddDistance γ 1 := by
  rw [oddDistance_two hlo hhi, oddDistance_one hlo hhi]
  exact mul_lt_mul_of_pos_left (by linarith) Real.pi_pos

end ArithmeticSections
