import MeanMaximumForests.PeakAnalysis.AvailabilityTail

namespace MeanMaximumForests.PeakAnalysis
open HardCoreActivityThreshold Finset

 theorem availability_exponential_le_quarter (N : ℕ) (hN : 2048 ≤ N) :
    Real.exp (-Real.log 2 * (N : ℝ) / 1024) ≤ 1 / 4 := by
  have hlog : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hn : (2048 : ℝ) ≤ N := by exact_mod_cast hN
  have h := mul_le_mul_of_nonneg_left hn hlog.le
  calc
    _ ≤ Real.exp (-(Real.log 2 + Real.log 2)) := Real.exp_le_exp.mpr (by linarith)
    _ = _ := by rw [Real.exp_neg, Real.exp_add, Real.exp_log (by norm_num : (0 : ℝ) < 2)]; norm_num

 theorem availability_exponential_scaled (N : ℕ) :
    (N : ℝ) * Real.exp (-Real.log 2 * (N : ℝ) / 1024) ≤ 1024 / Real.log 2 := by
  have hlog : 0 < Real.log 2 := Real.log_pos (by norm_num)
  let t := Real.log 2 * (N : ℝ) / 1024
  have ht : t ≤ Real.exp t := by linarith [Real.add_one_le_exp t]
  have he : Real.exp t * Real.exp (-t) = 1 := by rw [← Real.exp_add]; simp
  have hm := mul_le_mul_of_nonneg_right ht (Real.exp_pos (-t)).le
  rw [he] at hm
  apply (le_div_iff₀ hlog).mpr
  have heq : -Real.log 2 * (N : ℝ) / 1024 = -t := by dsimp [t]; ring
  rw [heq]
  dsimp [t] at hm
  nlinarith only [hm]

end MeanMaximumForests.PeakAnalysis
