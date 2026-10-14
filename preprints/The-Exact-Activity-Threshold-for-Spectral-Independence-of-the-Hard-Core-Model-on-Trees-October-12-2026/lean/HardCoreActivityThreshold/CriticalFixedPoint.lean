import HardCoreActivityThreshold.RootMarginalGadget
import HardCoreActivityThreshold.CriticalConstants

/-! The critical recursion fixed point and its exact square threshold. -/
namespace HardCoreActivityThreshold

theorem criticalOccupation_mem_Ioo : criticalOccupation ∈ Set.Ioo (0 : ℝ) 1 := by
  have hs : 0 < Real.sqrt 5 := by positivity
  have hsq : Real.sqrt 5 ^ 2 = 5 := Real.sq_sqrt (by norm_num)
  have hs1 : 1 < Real.sqrt 5 := by nlinarith
  constructor
  · unfold criticalOccupation
    positivity
  · unfold criticalOccupation
    exact (div_lt_one hs).mpr hs1

theorem criticalActivity_pos : 0 < criticalActivity := by
  unfold criticalActivity
  exact div_pos criticalOccupation_mem_Ioo.1 (pow_pos (sub_pos.mpr criticalOccupation_mem_Ioo.2) _)

theorem criticalOccupation_fixedpoint :
    criticalOccupation = criticalActivity * (1-criticalOccupation)^6 := by
  unfold criticalActivity
  exact (div_mul_cancel₀ _ (pow_ne_zero _ (sub_pos.mpr criticalOccupation_mem_Ioo.2).ne')).symm

/-- The critical threshold is exactly where the five-child squared-correlation factor reaches one. -/
theorem supercritical_fixedpoint_square {a p : ℝ} (ha : criticalActivity ≤ a)
    (_hp : p ∈ Set.Ioo (0 : ℝ) 1) (hpf : p = a*(1-p)^6) : 1 ≤ 5*p^2 := by
  have hpos : 0 < a := criticalActivity_pos.trans_le ha
  have hpq : criticalOccupation ≤ p := by
    by_contra! h
    have hbase : 1-p ≥ 1-criticalOccupation := by linarith
    have hpow := pow_le_pow_left₀ (sub_pos.mpr criticalOccupation_mem_Ioo.2).le hbase 6
    have hm := mul_le_mul ha hpow (pow_nonneg (sub_pos.mpr criticalOccupation_mem_Ioo.2).le _)
      hpos.le
    rw [← criticalOccupation_fixedpoint, ← hpf] at hm
    linarith
  have hq := criticalOccupation_mem_Ioo.1
  nlinarith [criticalOccupation_square]

end HardCoreActivityThreshold
