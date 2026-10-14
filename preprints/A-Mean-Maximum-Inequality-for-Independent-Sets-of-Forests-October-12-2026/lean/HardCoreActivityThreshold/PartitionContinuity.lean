import HardCoreActivityThreshold.ScalarEstimates

namespace HardCoreActivityThreshold

open Set Filter

theorem partitionFunction_zero : scalarPartitionFunction 0=0 := by simp [scalarPartitionFunction]

theorem partitionFunction_global_le (x : ℝ) (hx : x∈Icc 0 criticalEndpoint) :
    scalarPartitionFunction x≤1.001*x := by
  rcases eq_or_lt_of_le hx.1 with hz | hp
  · rw [←hz,partitionFunction_zero]
    norm_num
  · exact (partitionFunction_global_bound x hp hx.2).le

theorem partitionFunction_continuousWithinAt_zero :
    ContinuousWithinAt scalarPartitionFunction (Icc 0 criticalEndpoint) 0 := by
  have h0 : ∀ᶠx in nhdsWithin 0 (Icc 0 criticalEndpoint),0≤scalarPartitionFunction x := by
    filter_upwards [self_mem_nhdsWithin] with x hx
    exact partitionFunction_nonneg x hx.1 hx.2
  have h1 : ∀ᶠx in nhdsWithin 0 (Icc 0 criticalEndpoint),scalarPartitionFunction x≤1.001*x := by
    filter_upwards [self_mem_nhdsWithin] with x hx
    exact partitionFunction_global_le x hx
  have ht : Tendsto (fun x : ℝ => 1.001*x) (nhdsWithin 0 (Icc 0 criticalEndpoint)) (nhds 0) := by
    have h : ContinuousAt (fun x : ℝ => 1.001*x) 0 := by fun_prop
    simpa using h.continuousWithinAt.tendsto (s := Icc 0 criticalEndpoint)
  have hs := squeeze_zero' h0 h1 ht
  simpa [ContinuousWithinAt,partitionFunction_zero] using hs

theorem partitionFunction_continuousOn : ContinuousOn scalarPartitionFunction (Icc 0 criticalEndpoint) := by
  intro x hx
  rcases eq_or_lt_of_le hx.1 with hz | hp
  · rw [←hz]
    exact partitionFunction_continuousWithinAt_zero
  · exact (partitionFunction_hasDerivAt x hp).continuousAt.continuousWithinAt

end HardCoreActivityThreshold
