/-
Copyright 2026 Google LLC
Adapted from AlphaProof Nexus Results, under the Apache 2.0 license.
See THIRD_PARTY_LICENSES/Apache-2.0.txt.
-/
import MainTheorems.PureOSequences.Basic

namespace ResearchMain.PureOSequences

def RatioDecreasing (f : ℤ → ℤ) : Prop :=
  ∀ a b, b ≤ a → f (a + 1) * f (b - 1) ≤ f a * f b

def windowSum (f : ℤ → ℤ) (c : ℕ) (d : ℤ) : ℤ :=
  ∑ j ∈ Finset.range (c + 1), f (d - j)

theorem window_left_shift (f : ℤ → ℤ) (c : ℕ) (d : ℤ) :
    (∑ j ∈ Finset.range c, f (d - j - 1)) =
      (∑ j ∈ Finset.range c, f (d - j)) - f d + f (d - c) := by
  induction c with
  | zero => simp
  | succ c ih =>
    simp only [Finset.sum_range_succ, Nat.cast_add, Nat.cast_one]
    rw [ih]
    ring_nf

theorem window_right_shift (f : ℤ → ℤ) (c : ℕ) (d : ℤ) :
    windowSum f c (d + 1) = f (d + 1) + ∑ j ∈ Finset.range c, f (d - j) := by
  rw [windowSum, Finset.sum_range_succ']
  simp only [Nat.cast_add, Nat.cast_one, Nat.cast_zero, add_sub_add_right_eq_sub, sub_zero]
  exact add_comm _ _

theorem window_defect (f : ℤ → ℤ) (c : ℕ) (d : ℤ) :
    windowSum f c d ^ 2 - windowSum f c (d - 1) * windowSum f c (d + 1) =
      (∑ j ∈ Finset.range c, (f d * f (d - j) - f (d + 1) * f (d - j - 1))) +
      (∑ j ∈ Finset.range (c + 1),
        (f (d - j) * f (d - c) - f (d - j + 1) * f (d - c - 1))) := by
  have hleft := window_left_shift f c d
  have hright := window_right_shift f c d
  simp only [Finset.sum_sub_distrib, ← Finset.mul_sum, ← Finset.sum_mul]
  have hmid : windowSum f c d =
      (∑ j ∈ Finset.range c, f (d - j)) + f (d - c) := by
    exact Finset.sum_range_succ _ _
  have hminus : windowSum f c (d - 1) =
      (∑ j ∈ Finset.range c, f (d - j)) - f d + f (d - c) + f (d - c - 1) := by
    rw [windowSum, Finset.sum_range_succ]
    simpa only [sub_right_comm] using congrArg (· + f (d - c - 1)) hleft
  have hplus : (∑ j ∈ Finset.range (c + 1), f (d - j + 1)) =
      f (d + 1) + ∑ j ∈ Finset.range c, f (d - j) := by
    simpa only [windowSum, sub_add_eq_add_sub] using hright
  have hmidsum : (∑ j ∈ Finset.range (c + 1), f (d - j)) =
      (∑ j ∈ Finset.range c, f (d - j)) + f (d - c) := hmid
  rw [hmid, hminus, hright, hleft, hplus, hmidsum]
  ring

theorem window_logConcave {f : ℤ → ℤ} (h : RatioDecreasing f) (c : ℕ) (d : ℤ) :
    windowSum f c (d - 1) * windowSum f c (d + 1) ≤ windowSum f c d ^ 2 := by
  have hfirst : 0 ≤ ∑ j ∈ Finset.range c,
      (f d * f (d - j) - f (d + 1) * f (d - j - 1)) := by
    apply Finset.sum_nonneg
    intro j _
    exact sub_nonneg.mpr (h d (d - j) (by omega))
  have hsecond : 0 ≤ ∑ j ∈ Finset.range (c + 1),
      (f (d - j) * f (d - c) - f (d - j + 1) * f (d - c - 1)) := by
    apply Finset.sum_nonneg
    intro j hj
    exact sub_nonneg.mpr (h (d - j) (d - c) (by
      have := Finset.mem_range.mp hj
      omega))
  have hid := window_defect f c d
  linarith

theorem ratioDecreasing_of_logConcave (f : ℤ → ℤ) (e : ℤ)
    (hlc : ∀ k, f (k - 1) * f (k + 1) ≤ f k ^ 2)
    (hpos : ∀ k, 0 ≤ k → k ≤ e → 0 < f k)
    (hzero : ∀ k, k < 0 ∨ e < k → f k = 0) : RatioDecreasing f := by
  have hnonneg : ∀ k, 0 ≤ f k := by
    intro k
    by_cases h : 0 ≤ k ∧ k ≤ e
    · exact (hpos k h.1 h.2).le
    · rw [hzero k (by omega)]
  intro a b hab
  by_cases hb : 0 ≤ b - 1
  · by_cases ha : a + 1 ≤ e
    · have haux : ∀ n : ℕ, b + n + 1 ≤ e →
          f (b + n + 1) * f (b - 1) ≤ f (b + n) * f b := by
        intro n
        induction n with
        | zero =>
          intro _
          simpa [sq, mul_comm] using hlc b
        | succ n ih =>
          intro hn
          have hp : 0 < f (b + n + 1) := hpos _ (by omega) (by omega)
          have h1 := mul_le_mul_of_nonneg_left (ih (by omega)) (hnonneg (b + n + 2))
          have h2 := mul_le_mul_of_nonneg_right (hlc (b + n + 1)) (hnonneg b)
          rw [show b + (n : ℤ) + 1 - 1 = b + n by ring,
            show b + (n : ℤ) + 1 + 1 = b + n + 2 by ring] at h2
          have hmul : f (b + n + 1) * (f (b + n + 2) * f (b - 1)) ≤
              f (b + n + 1) * (f (b + n + 1) * f b) := by
            nlinarith [h1, h2]
          have := le_of_mul_le_mul_left hmul hp
          simpa only [Nat.cast_succ, add_assoc, show (1 : ℤ) + 1 = 2 by decide] using this
      have hn : b + (a - b).toNat = a := by omega
      simpa only [hn] using haux (a - b).toNat (by omega)
    · rw [hzero (a + 1) (by omega), zero_mul]
      exact mul_nonneg (hnonneg a) (hnonneg b)
  · rw [hzero (b - 1) (by omega), mul_zero]
    exact mul_nonneg (hnonneg a) (hnonneg b)

end ResearchMain.PureOSequences
