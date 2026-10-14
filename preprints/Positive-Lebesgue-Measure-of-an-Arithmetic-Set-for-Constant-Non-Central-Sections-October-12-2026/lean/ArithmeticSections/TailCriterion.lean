import ArithmeticSections.GridApproximation
import ArithmeticSections.QuadraticBounds

set_option maxRecDepth 2048
set_option maxHeartbeats 1000000

namespace ArithmeticSections

theorem denominator_monotone {b : ℕ → ℕ} (hb : ∀ n, 1 ≤ b (n + 1)) :
    Monotone (denominator b) := monotone_nat_of_le_succ (denominator_mono_step hb)

theorem exists_denominator_bracket {b : ℕ → ℕ} (hb : ∀ n, 1 ≤ b (n + 1))
    (a k : ℕ) (hk : denominator b a ≤ k) :
    ∃ j, a ≤ j ∧ denominator b j ≤ k ∧ k < denominator b (j + 1) := by
  have he : ∃ n, k < denominator b n := by
    refine ⟨2 * k, ?_⟩
    have h := exponential_le_denominator hb (2 * k)
    have hp := k.lt_two_pow_self
    have hd : 2 * k / 2 = k := by omega
    rw [hd] at h
    omega
  let n := Nat.find he
  have hn : k < denominator b n := Nat.find_spec he
  have han : a < n := by
    by_contra ha
    have hd := denominator_monotone hb (by omega : n ≤ a)
    omega
  refine ⟨n - 1, by omega, ?_, ?_⟩
  · have hf := Nat.find_min he (show n - 1 < n by omega)
    omega
  · simpa only [Nat.sub_add_cancel (show 1 ≤ n by omega)] using hn

/-- The next odd distance lower bound used in the polynomial-digit tail. -/
theorem oddDistance_tail_lower {θ : ℝ} (hθ : Irrational θ)
    (hlo : 0 ≤ θ) (hhi : θ < 1) (j : ℕ) (hj : 256 ≤ j)
    (hdigits : ∀ l, 257 ≤ l → actualDigit θ l ≤ l ^ 2) {k : ℕ}
    (hk : k < actualDenominator θ (j + 1)) :
    Real.pi / (2 * (tailThreshold j : ℝ) * actualDenominator θ j) <
      oddDistance (θ / 2) (k + 1) := by
  have hg := denominator_two_step (one_le_actualDigit_succ hθ) (j + 1)
  have hm : 2 * k + 1 ≤ actualDenominator θ (j + 3) := by
    change 2 * actualDenominator θ (j + 1) ≤ actualDenominator θ (j + 3) at hg
    omega
  have he := integerDistance_lower_bound hθ hlo hhi (j + 2) (2 * k + 1) (by omega) hm
  have hdist := denominator_distortion (one_le_actualDigit_succ hθ) j hj hdigits
  have hdistR : (actualDenominator θ (j + 3) : ℝ) * (actualDigit θ (j + 4) + 2) ≤
      (tailThreshold j : ℝ) * actualDenominator θ j := by exact_mod_cast hdist
  have hden : 0 < (actualDenominator θ (j + 3) : ℝ) * (actualDigit θ (j + 4) + 2) := by
    have : (0 : ℝ) < actualDenominator θ (j + 3) := by exact_mod_cast denominator_pos (one_le_actualDigit_succ hθ) (j + 3)
    positivity
  have he' : 1 / ((tailThreshold j : ℝ) * actualDenominator θ j) <
      integerDistance (((2 * k + 1 : ℕ) : ℝ) * θ) :=
    lt_of_le_of_lt (one_div_le_one_div_of_le hden hdistR) he
  have hd := integerDistance_double ((((2 * k + 1 : ℕ) : ℝ) * θ) / 2)
  have heq : 2 * ((((2 * k + 1 : ℕ) : ℝ) * θ) / 2) = (((2 * k + 1 : ℕ) : ℝ) * θ) := by ring
  rw [heq] at hd
  have hl := mul_lt_mul_of_pos_left (lt_of_lt_of_le he' hd) (show 0 < Real.pi / 2 by positivity)
  unfold oddDistance
  convert hl using 1 <;> push_cast <;> ring

/-- Proposition 4.2 for the actual Gauss digits, without parity hypotheses. -/
theorem polynomial_digit_tail {γ : ℝ} (hγ : Irrational γ)
    (hlo : 1 / 3 < γ) (hhi : γ < 1 / 2)
    (hdigits : ∀ l, 257 ≤ l → actualDigit (2 * γ) l ≤ l ^ 2)
    {k : ℕ} (hk : actualDenominator (2 * γ) 256 ≤ k) : 0 < conditionGap γ k := by
  have hθ : Irrational (2 * γ) := by
    simpa [mul_comm] using hγ.mul_ratCast (q := 2) (by norm_num)
  have htlo : 0 ≤ 2 * γ := by linarith
  have hthi : 2 * γ < 1 := by linarith
  obtain ⟨j, hj, hqk, hkq⟩ := exists_denominator_bracket (one_le_actualDigit_succ hθ) 256 k hk
  change actualDenominator (2 * γ) j ≤ k at hqk
  change k < actualDenominator (2 * γ) (j + 1) at hkq
  have hqbig := tailThreshold_lt_actualDenominator hθ j hj
  have hM : 1 ≤ tailThreshold j := by
    have : 0 < tailThreshold j := by unfold tailThreshold; positivity
    omega
  have hq : 2 ≤ actualDenominator (2 * γ) j := by omega
  have hqR : (72 : ℝ) * tailThreshold j < actualDenominator (2 * γ) j := by exact_mod_cast hqbig
  have hMR : (1 : ℝ) ≤ tailThreshold j := by exact_mod_cast hM
  have hqpos : (0 : ℝ) < actualDenominator (2 * γ) j := by exact_mod_cast (show 0 < actualDenominator (2 * γ) j by omega)
  have hk2 : 2 ≤ k := by omega
  have hj1 : j - 1 + 1 = j := by omega
  have ht := secondDistance_lt_convergent hθ htlo hthi (j - 1) (by simpa only [hj1] using hq)
    (by simpa only [hj1] using hqk)
  simp only [hj1, mul_div_cancel_left₀ _ (by norm_num : (2 : ℝ) ≠ 0)] at ht
  have ht' : secondDistance γ k < 1 / 4 := by
    have hb : 2 * Real.pi / (actualDenominator (2 * γ) j : ℝ) < 1 / 4 := by
      apply (div_lt_iff₀ hqpos).mpr
      nlinarith only [hqR, hMR, Real.pi_lt_four]
    exact ht.trans hb
  have hmax := max_deviation_le_product hγ hlo hhi hk2 ht'.le
  have hspos := firstDistance_pos hγ (by omega : 1 ≤ k)
  have hst := firstDistance_lt_second hγ hk2
  have hu : max (minusDeviation γ k) (plusDeviation γ k) <
      (2 * Real.pi / (actualDenominator (2 * γ) j : ℝ)) ^ 2 := by
    have hp : 0 < 2 * Real.pi / (actualDenominator (2 * γ) j : ℝ) := by positivity
    nlinarith only [hmax, hspos, hst, ht, hp]
  have hl := oddDistance_tail_lower hθ htlo hthi j hj hdigits hkq
  simp only [mul_div_cancel_left₀ _ (by norm_num : (2 : ℝ) ≠ 0)] at hl
  have hcompare : (2 * Real.pi / (actualDenominator (2 * γ) j : ℝ)) ^ 2 <
      Real.pi / (2 * (tailThreshold j : ℝ) * actualDenominator (2 * γ) j) := by
    have hMpos : (0 : ℝ) < tailThreshold j := by linarith
    field_simp
    nlinarith only [hqR, hMR, Real.pi_pos, Real.pi_lt_four, mul_pos hMpos hqpos]
  unfold conditionGap
  linarith

end ArithmeticSections
