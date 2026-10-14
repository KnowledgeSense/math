import MeanMaximumForests.PeakAnalysis.BinomialMode
import Mathlib.Algebra.BigOperators.Intervals

namespace MeanMaximumForests.PeakAnalysis
open Finset

theorem binomial_increasing_to_mode (n j : ℕ) (z : ℝ) (hz : 0 < z) (hjn : j ≤ n)
    (hmode : ∀ k, binomialSizeMass n z k ≤ binomialSizeMass n z j) :
    ∀ i < j, binomialSizeMass n z i ≤ binomialSizeMass n z (i + 1) := by
  intro i hij
  have hprev : binomialSizeMass n z (j - 1) ≤ binomialSizeMass n z (j - 1 + 1) := by
    simpa only [Nat.sub_add_cancel (by omega : 1 ≤ j)] using hmode (j - 1)
  have hbound := (binomialSizeMass_le_step_iff n (j - 1) z hz (by omega)).mp hprev
  apply (binomialSizeMass_le_step_iff n i z hz (by omega)).mpr
  have hii : (i : ℝ) ≤ (j - 1 : ℕ) := by exact_mod_cast (by omega : i ≤ j - 1)
  have hm := mul_le_mul_of_nonneg_left hii (by linarith : 0 ≤ 1 + z)
  linarith

theorem binomial_decreasing_from_mode (n j : ℕ) (z : ℝ) (hz : 0 < z) (hjn : j ≤ n)
    (hmode : ∀ k, binomialSizeMass n z k ≤ binomialSizeMass n z j) :
    ∀ i, j ≤ i → binomialSizeMass n z (i + 1) ≤ binomialSizeMass n z i := by
  intro i hji
  by_cases hin : i ≤ n
  · have hbound := (binomialSizeMass_step_le_iff n j z hz hjn).mp (hmode (j + 1))
    apply (binomialSizeMass_step_le_iff n i z hz hin).mpr
    have hji' : (j : ℝ) ≤ i := by exact_mod_cast hji
    have hm := mul_le_mul_of_nonneg_left hji' (by linarith : 0 ≤ 1 + z)
    linarith
  · rw [binomialSizeMass_eq_zero z (by omega : n < i + 1),
      binomialSizeMass_eq_zero z (by omega : n < i)]

theorem binomial_total_variation (n j : ℕ) (z : ℝ) (hz : 0 < z) (hjn : j ≤ n)
    (hmode : ∀ k, binomialSizeMass n z k ≤ binomialSizeMass n z j) :
    binomialSizeMass n z 0 +
      (∑ i ∈ range (n + 1), |binomialSizeMass n z (i + 1) - binomialSizeMass n z i|) =
        2 * binomialSizeMass n z j := by
  have hinc := binomial_increasing_to_mode n j z hz hjn hmode
  have hdec := binomial_decreasing_from_mode n j z hz hjn hmode
  have ha : (∑ i ∈ range j, |binomialSizeMass n z (i + 1) - binomialSizeMass n z i|) =
      binomialSizeMass n z j - binomialSizeMass n z 0 := by
    calc
      _ = ∑ i ∈ range j, (binomialSizeMass n z (i + 1) - binomialSizeMass n z i) := by
        apply sum_congr rfl
        intro i hi
        exact abs_of_nonneg (sub_nonneg.mpr (hinc i (mem_range.mp hi)))
      _ = _ := sum_range_sub (binomialSizeMass n z) j
  have hb : (∑ i ∈ Ico j (n + 1), |binomialSizeMass n z (i + 1) - binomialSizeMass n z i|) =
      binomialSizeMass n z j := by
    calc
      _ = -(∑ i ∈ Ico j (n + 1), (binomialSizeMass n z (i + 1) - binomialSizeMass n z i)) := by
        rw [← sum_neg_distrib]
        apply sum_congr rfl
        intro i hi
        exact abs_of_nonpos (sub_nonpos.mpr (hdec i (mem_Ico.mp hi).1))
      _ = _ := by
        rw [sum_Ico_sub (binomialSizeMass n z) (by omega), binomialSizeMass_eq_zero z (by omega)]
        ring
  rw [← sum_range_add_sum_Ico (fun i => |binomialSizeMass n z (i + 1) - binomialSizeMass n z i|)
    (by omega : j ≤ n + 1), ha, hb]
  ring

end MeanMaximumForests.PeakAnalysis
