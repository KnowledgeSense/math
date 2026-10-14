/-
Copyright 2026 Google LLC
Adapted from AlphaProof Nexus Results, under the Apache 2.0 license.
See THIRD_PARTY_LICENSES/Apache-2.0.txt.
-/
import Mathlib.Tactic

namespace ResearchMain.Hypercomb

def RatioDecreasing (f : ℤ → ℝ) : Prop :=
  ∀ a b, b ≤ a → f (a + 1) * f (b - 1) ≤ f a * f b

structure PositiveLC (f : ℤ → ℝ) (e : ℕ) : Prop where
  positive : ∀ k : ℤ, 0 ≤ k → k ≤ (e : ℤ) → 0 < f k
  zero : ∀ k, k < 0 ∨ (e : ℤ) < k → f k = 0
  logConcave : ∀ k, f (k - 1) * f (k + 1) ≤ f k ^ 2

theorem PositiveLC.nonnegative {f : ℤ → ℝ} {e : ℕ} (hf : PositiveLC f e) (k : ℤ) : 0 ≤ f k := by
  by_cases h : 0 ≤ k ∧ k ≤ e
  · exact (hf.positive k h.1 h.2).le
  · rw [hf.zero k (by omega)]

theorem PositiveLC.ratioDecreasing {f : ℤ → ℝ} {e : ℕ} (hf : PositiveLC f e) : RatioDecreasing f := by
  intro a b hab
  by_cases hb : 0 ≤ b - 1
  · by_cases ha : a + 1 ≤ e
    · have haux : ∀ n : ℕ, b + n + 1 ≤ e →
          f (b + n + 1) * f (b - 1) ≤ f (b + n) * f b := by
        intro n
        induction n with
        | zero =>
          intro _
          simpa [sq, mul_comm] using hf.logConcave b
        | succ n ih =>
          intro hn
          have hp : 0 < f (b + n + 1) := hf.positive _ (by omega) (by omega)
          have h₁ := mul_le_mul_of_nonneg_left (ih (by omega)) (hf.nonnegative (b + n + 2))
          have h₂ := mul_le_mul_of_nonneg_right (hf.logConcave (b + n + 1)) (hf.nonnegative b)
          rw [show b + (n : ℤ) + 1 - 1 = b + n by ring,
            show b + (n : ℤ) + 1 + 1 = b + n + 2 by ring] at h₂
          have hmul : f (b + n + 1) * (f (b + n + 2) * f (b - 1)) ≤
              f (b + n + 1) * (f (b + n + 1) * f b) := by
            nlinarith only [h₁, h₂]
          have h := le_of_mul_le_mul_left hmul hp
          simpa only [Nat.cast_succ, add_assoc, show (1 : ℤ) + 1 = 2 by decide] using h
      have hn : b + (a - b).toNat = a := by omega
      simpa only [hn] using haux (a - b).toNat (by omega)
    · rw [hf.zero (a + 1) (by omega), zero_mul]
      exact mul_nonneg (hf.nonnegative a) (hf.nonnegative b)
  · rw [hf.zero (b - 1) (by omega), mul_zero]
    exact mul_nonneg (hf.nonnegative a) (hf.nonnegative b)

def tripleSum (f : ℤ → ℝ) (b c : ℝ) (k : ℤ) : ℝ := f k + b * f (k - 1) + c * f (k - 2)

theorem tripleSum_logConcave {f : ℤ → ℝ} (hf : RatioDecreasing f)
    {b c : ℝ} (hb : 0 ≤ b) (hc : 0 ≤ c) (hbc : c ≤ b ^ 2) (k : ℤ) :
    tripleSum f b c (k - 1) * tripleSum f b c (k + 1) ≤ tripleSum f b c k ^ 2 := by
  have h₀ := hf k k le_rfl
  have h₁ := hf k (k - 1) (by omega)
  have h₂ := hf (k - 1) (k - 1) le_rfl
  have h₃ := hf k (k - 2) (by omega)
  have h₄ := hf (k - 1) (k - 2) (by omega)
  have h₅ := hf (k - 2) (k - 2) le_rfl
  rw [show k - 1 - 1 = k - 2 by omega] at h₁
  have hn₀ : 0 ≤ f k ^ 2 - f (k - 1) * f (k + 1) := by nlinarith only [h₀]
  have hn₁ : 0 ≤ b * (f k * f (k - 1) - f (k - 2) * f (k + 1)) :=
    mul_nonneg hb (by nlinarith only [h₁])
  have hn₂ : 0 ≤ (b ^ 2 - c) * (f (k - 1) ^ 2 - f (k - 2) * f k) :=
    mul_nonneg (sub_nonneg.mpr hbc) (by
      have he : k - 1 + 1 = k := by omega
      rw [he] at h₂
      have he' : k - 1 - 1 = k - 2 := by omega
      rw [he'] at h₂
      nlinarith only [h₂])
  have hn₃ : 0 ≤ c * (f k * f (k - 2) - f (k - 3) * f (k + 1)) :=
    mul_nonneg hc (by
      rw [show k - 2 - 1 = k - 3 by omega] at h₃
      nlinarith only [h₃])
  have hn₄ : 0 ≤ b * c * (f (k - 1) * f (k - 2) - f (k - 3) * f k) :=
    mul_nonneg (mul_nonneg hb hc) (by
      rw [show k - 1 + 1 = k by omega, show k - 2 - 1 = k - 3 by omega] at h₄
      nlinarith only [h₄])
  have hn₅ : 0 ≤ c ^ 2 * (f (k - 2) ^ 2 - f (k - 3) * f (k - 1)) :=
    mul_nonneg (sq_nonneg c) (by
      rw [show k - 2 + 1 = k - 1 by omega, show k - 2 - 1 = k - 3 by omega] at h₅
      nlinarith only [h₅])
  have hid : tripleSum f b c k ^ 2 - tripleSum f b c (k - 1) * tripleSum f b c (k + 1) =
      (f k ^ 2 - f (k - 1) * f (k + 1)) +
      b * (f k * f (k - 1) - f (k - 2) * f (k + 1)) +
      (b ^ 2 - c) * (f (k - 1) ^ 2 - f (k - 2) * f k) +
      c * (f k * f (k - 2) - f (k - 3) * f (k + 1)) +
      b * c * (f (k - 1) * f (k - 2) - f (k - 3) * f k) +
      c ^ 2 * (f (k - 2) ^ 2 - f (k - 3) * f (k - 1)) := by
    simp only [tripleSum, show k - 1 - 1 = k - 2 by omega,
      show k - 1 - 2 = k - 3 by omega, show k + 1 - 1 = k by omega,
      show k + 1 - 2 = k - 1 by omega]
    ring
  linarith only [hn₀, hn₁, hn₂, hn₃, hn₄, hn₅, hid]

theorem tripleSum_nonnegative {f : ℤ → ℝ} {e : ℕ} (hf : PositiveLC f e)
    {b c : ℝ} (hb : 0 ≤ b) (hc : 0 ≤ c) (k : ℤ) : 0 ≤ tripleSum f b c k := by
  exact add_nonneg (add_nonneg (hf.nonnegative k) (mul_nonneg hb (hf.nonnegative (k - 1))))
    (mul_nonneg hc (hf.nonnegative (k - 2)))

theorem PositiveLC.linear {f : ℤ → ℝ} {e : ℕ} (hf : PositiveLC f e)
    {b : ℝ} (hb : 0 < b) : PositiveLC (tripleSum f b 0) (e + 1) := by
  constructor
  · intro k hk0 hke
    by_cases hk : k ≤ e
    · have h := hf.positive k hk0 hk
      have hnext := mul_nonneg hb.le (hf.nonnegative (k - 1))
      dsimp [tripleSum]
      linarith
    · have hprev : 0 < b * f (k - 1) := mul_pos hb (hf.positive _ (by omega) (by omega))
      have h := hf.nonnegative k
      dsimp [tripleSum]
      linarith
  · intro k hk
    simp only [tripleSum, hf.zero k (by omega), hf.zero (k - 1) (by omega), zero_mul, mul_zero, add_zero]
  · exact tripleSum_logConcave hf.ratioDecreasing hb.le le_rfl (sq_nonneg b)

theorem PositiveLC.quadratic {f : ℤ → ℝ} {e : ℕ} (hf : PositiveLC f e)
    {b c : ℝ} (hb : 0 < b) (hc : 0 < c) (hbc : c ≤ b ^ 2) :
    PositiveLC (tripleSum f b c) (e + 2) := by
  constructor
  · intro k hk0 hke
    have hf0 := hf.nonnegative k
    have hb0 := mul_nonneg hb.le (hf.nonnegative (k - 1))
    have hc0 := mul_nonneg hc.le (hf.nonnegative (k - 2))
    by_cases hk : k ≤ e
    · have h := hf.positive k hk0 hk
      dsimp [tripleSum]
      linarith
    · by_cases hk1 : k = (e : ℤ) + 1
      · have h := mul_pos hb (hf.positive (k - 1) (by omega) (by omega))
        dsimp [tripleSum]
        linarith
      · have h := mul_pos hc (hf.positive (k - 2) (by omega) (by omega))
        dsimp [tripleSum]
        linarith
  · intro k hk
    simp only [tripleSum, hf.zero k (by omega), hf.zero (k - 1) (by omega), hf.zero (k - 2) (by omega),
      mul_zero, add_zero]
  · exact tripleSum_logConcave hf.ratioDecreasing hb.le hc.le hbc

end ResearchMain.Hypercomb
