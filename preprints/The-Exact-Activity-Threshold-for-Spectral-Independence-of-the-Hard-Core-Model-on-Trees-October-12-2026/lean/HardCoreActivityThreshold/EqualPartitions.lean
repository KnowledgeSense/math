import HardCoreActivityThreshold.ScalarEstimates
import HardCoreActivityThreshold.FivefoldMinimum

namespace HardCoreActivityThreshold

theorem equal_partition_bound (b : ℕ) (x : ℝ) (hx : 0≤x) (hX : x≤criticalEndpoint) :
    (b : ℝ)*scalarPartitionFunction x≤potential ((b : ℝ)*x) := by
  by_cases hb0 : b=0
  · simp [hb0,potential]
  by_cases hx0 : x=0
  · simp [hx0,scalarPartitionFunction,potential]
  have hb : (0 : ℝ)<b := by exact_mod_cast Nat.pos_of_ne_zero hb0
  have hxp : 0<x := lt_of_le_of_ne hx (Ne.symm hx0)
  have hY : 0≤(b : ℝ)*x := mul_nonneg hb.le hx
  by_cases hmiddle : (b : ℝ)*x∈Set.Ioo 2.5 3.1
  · by_cases hb5 : b=5
    · subst b
      norm_num at hmiddle ⊢
      have hg := fivefoldGap_nonneg x (show x∈Set.Icc 0.5 0.62 by constructor <;> linarith [hmiddle.1,hmiddle.2])
      unfold fivefoldGap at hg
      linarith
    · have hfx : scalarPartitionFunction x<x := by
        by_cases hble : b≤4
        · have hbr : (b : ℝ)≤4 := by exact_mod_cast hble
          have hxx : 0.625≤x := by nlinarith [hmiddle.1,mul_le_mul_of_nonneg_right hbr hx]
          exact partitionFunction_upper_bound x hxx hX
        · have hb6 : 6≤b := by omega
          have hbr : (6 : ℝ)≤b := by exact_mod_cast hb6
          have hxx : x≤0.52 := by nlinarith [hmiddle.2,mul_le_mul_of_nonneg_right hbr hx]
          exact partitionFunction_low_bound x hxp hxx
      exact (mul_le_mul_of_nonneg_left hfx.le hb.le).trans (cubicPotential_ge cubicCenter _ hY)
  · have hout : (b : ℝ)*x≤5/2 ∨ 31/10≤(b : ℝ)*x := by
      simp only [Set.mem_Ioo,not_and_or,not_lt] at hmiddle
      rcases hmiddle with h | h
      · left; linarith
      · right; linarith
    have hz : cubicCenter∈Set.Icc (28310/10000) (28311/10000) := by
      convert cubicCenter_bounds using 1; norm_num
    have hp := cubicPotential_outside cubicCenter _ hz hY hout
    have hf := mul_le_mul_of_nonneg_left (partitionFunction_global_bound x hxp hX).le hb.le
    change (b : ℝ)*scalarPartitionFunction x≤cubicPotential cubicCenter ((b : ℝ)*x)
    nlinarith

end HardCoreActivityThreshold
