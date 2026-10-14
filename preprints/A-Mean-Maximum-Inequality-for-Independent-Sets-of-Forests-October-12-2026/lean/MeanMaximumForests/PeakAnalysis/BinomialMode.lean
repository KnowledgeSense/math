import MeanMaximumForests.PeakAnalysis.BinomialMoments
import Mathlib.Data.Finset.Max

namespace MeanMaximumForests.PeakAnalysis
open HardCoreActivityThreshold Finset

theorem binomialSizeMass_le_step_iff (n k : ℕ) (z : ℝ) (hz : 0 < z) (hk : k ≤ n) :
    binomialSizeMass n z k ≤ binomialSizeMass n z (k + 1) ↔
      (1 + z) * k + 1 ≤ z * (n : ℝ) := by
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

/-- A global binomial mode exists within distance one of its actual mean. -/
theorem exists_binomial_mode (n : ℕ) (z : ℝ) (hz : 0 < z) :
    ∃ j : ℕ, j ≤ n ∧ |(j : ℝ) - z * n / (1 + z)| ≤ 1 ∧
      ∀ k : ℕ, binomialSizeMass n z k ≤ binomialSizeMass n z j := by
  classical
  obtain ⟨j, _, hjmax⟩ := (univ : Finset (Fin (n + 1))).exists_max_image
    (fun j => binomialSizeMass n z j.val) univ_nonempty
  have hjn : j.val ≤ n := by omega
  have hmax (k : ℕ) : binomialSizeMass n z k ≤ binomialSizeMass n z j.val := by
    by_cases hk : k ≤ n
    · exact hjmax ⟨k, by omega⟩ (mem_univ _)
    · rw [binomialSizeMass_eq_zero z (by omega)]
      exact (binomialSizeMass_pos n j.val z hz hjn).le
  refine ⟨j.val, hjn, ?_, hmax⟩
  have hzden : 0 < 1 + z := by linarith
  have hright := (binomialSizeMass_step_le_iff n j.val z hz hjn).mp (hmax (j.val + 1))
  have hlo : z * n / (1 + z) ≤ (j.val : ℝ) + 1 := by
    apply (div_le_iff₀ hzden).mpr
    nlinarith only [hright, hz.le]
  have hhi : (j.val : ℝ) - 1 ≤ z * n / (1 + z) := by
    by_cases hj0 : j.val = 0
    · rw [hj0, Nat.cast_zero]
      have : (0 : ℝ) ≤ z * n / (1 + z) := by positivity
      linarith
    · have hprev : binomialSizeMass n z (j.val - 1) ≤ binomialSizeMass n z (j.val - 1 + 1) := by
        simpa only [Nat.sub_add_cancel (by omega : 1 ≤ j.val)] using hmax (j.val - 1)
      have hleft := (binomialSizeMass_le_step_iff n (j.val - 1) z hz (by omega)).mp hprev
      rw [Nat.cast_sub (by omega : 1 ≤ j.val), Nat.cast_one] at hleft
      apply (le_div_iff₀ hzden).mpr
      linarith
  rw [abs_le]
  constructor <;> linarith

end MeanMaximumForests.PeakAnalysis
