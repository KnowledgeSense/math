import MeanMaximumForests.PeakAnalysis.FiniteTilt
import Mathlib.Data.Nat.Choose.Sum

namespace MeanMaximumForests.PeakAnalysis
open HardCoreActivityThreshold Finset

noncomputable def binomialSizeMass (n : ℕ) (z : ℝ) (k : ℕ) : ℝ :=
  (n.choose k : ℝ) * z ^ k / (1 + z) ^ n

theorem binomialWeight_sum (n : ℕ) (z : ℝ) :
    (∑ k : Fin (n + 1), (n.choose k.val : ℝ) * z ^ k.val) = (1 + z) ^ n := by
  rw [Finset.sum_fin_eq_sum_range, add_comm 1 z, add_pow]
  apply sum_congr rfl
  intro k hk
  simp only [dite_eq_left (mem_range.mp hk), one_pow, mul_one, mul_comm]

noncomputable def binomialSizeLaw (n : ℕ) (z : ℝ) (hz : 0 < z) : FiniteLaw (Fin (n + 1)) where
  mass k := binomialSizeMass n z k.val
  nonneg k := by unfold binomialSizeMass; positivity
  sum_one := by
    simp only [binomialSizeMass, ← sum_div, binomialWeight_sum]
    exact div_self (by positivity)

theorem binomialSizeMass_pos (n k : ℕ) (z : ℝ) (hz : 0 < z) (hk : k ≤ n) :
    0 < binomialSizeMass n z k := by
  unfold binomialSizeMass
  have hc : (0 : ℝ) < n.choose k := Nat.cast_pos.mpr (Nat.choose_pos hk)
  positivity

theorem binomialSizeMass_eq_zero {n k : ℕ} (z : ℝ) (hk : n < k) :
    binomialSizeMass n z k = 0 := by simp [binomialSizeMass, Nat.choose_eq_zero_of_lt hk]

theorem binomialSizeMass_step (n k : ℕ) (z : ℝ) :
    (k + 1 : ℝ) * binomialSizeMass n z (k + 1) =
      z * (n - k : ℕ) * binomialSizeMass n z k := by
  unfold binomialSizeMass
  have hc : (n.choose (k + 1) : ℝ) * (k + 1) = (n.choose k : ℝ) * (n - k : ℕ) := by
    exact_mod_cast Nat.choose_succ_right_eq n k
  rw [pow_succ]
  have he : (k + 1) * ((n.choose (k + 1) : ℝ) * (z ^ k * z)) =
      z * (n - k : ℕ) * ((n.choose k : ℝ) * z ^ k) := by
    calc
      _ = ((n.choose (k + 1) : ℝ) * (k + 1)) * (z ^ k * z) := by ring
      _ = _ := by rw [hc]; ring
  simp only [← mul_div_assoc]
  rw [he]

/-- The one-step ratio is located exactly by the binomial mean. -/
theorem binomialSizeMass_step_le_iff (n k : ℕ) (z : ℝ) (hz : 0 < z) (hk : k ≤ n) :
    binomialSizeMass n z (k + 1) ≤ binomialSizeMass n z k ↔
      z * (n : ℝ) ≤ (1 + z) * k + 1 := by
  have hmass := binomialSizeMass_pos n k z hz hk
  have hs := binomialSizeMass_step n k z
  rw [Nat.cast_sub hk] at hs
  have hkpos : (0 : ℝ) < k + 1 := by positivity
  constructor
  · intro h
    have hm := mul_le_mul_of_nonneg_left h hkpos.le
    nlinarith only [hm, hs, hmass]
  · intro h
    have hm := mul_le_mul_of_nonneg_right h hmass.le
    nlinarith only [hm, hs]

end MeanMaximumForests.PeakAnalysis
