import HardCoreActivityThreshold.ScalarCover
import HardCoreActivityThreshold.ScalarDerivativeEstimates
import HardCoreActivityThreshold.SmallOccupation

namespace HardCoreActivityThreshold

theorem occupation_le_critical_bound (x : ℝ) (hx : x≤criticalEndpoint) :
    scalarOccupation x≤0.941 :=
  (occupation_strictMono.monotone hx).trans occupation_criticalEndpoint_lt.le

theorem partitionFunction_global_bound (x : ℝ) (hx : 0<x) (hX : x≤criticalEndpoint) :
    scalarPartitionFunction x<1.001*x := by
  by_cases hq : scalarOccupation x≤0.01
  · have h := partitionFunction_small x hx hq
    linarith
  · exact scalar_cover_a_global x hx ⟨(lt_of_not_ge hq).le,occupation_le_critical_bound x hX⟩

theorem partitionFunction_high_bound (x : ℝ) (hA : concavityEndpoint≤x) (hX : x≤criticalEndpoint) :
    scalarPartitionFunction x<0.99*x := by
  apply scalar_cover_b_high x (concavityEndpoint_pos.trans_le hA)
  constructor
  · rw [←occupation_concavityEndpoint]
    exact occupation_strictMono.monotone hA
  · exact occupation_le_critical_bound x hX

theorem occupation_lower_region (x : ℝ) (hx : x≤0.52) : scalarOccupation x≤0.406 := by
  rw [occupation_le_iff x 0.406 (by norm_num)]
  have h := logarithm_lower_bounds
  norm_num at h ⊢
  linarith [h.2]

theorem occupation_upper_region (x : ℝ) (hx : 0.625≤x) : 0.4647≤scalarOccupation x := by
  rw [le_occupation_iff x 0.4647 (by norm_num)]
  have h := logarithm_upper_bounds
  norm_num at h ⊢
  linarith [h.1]

theorem partitionFunction_low_bound (x : ℝ) (hx : 0<x) (hlo : x≤0.52) :
    scalarPartitionFunction x<x := by
  by_cases hq : scalarOccupation x≤0.01
  · have h := partitionFunction_small x hx hq
    linarith
  · have h := scalar_cover_c_low x hx ⟨(lt_of_not_ge hq).le,occupation_lower_region x hlo⟩
    simpa using h

theorem partitionFunction_upper_bound (x : ℝ) (hhi : 0.625≤x) (hX : x≤criticalEndpoint) :
    scalarPartitionFunction x<x := by
  have h := scalar_cover_c_high x (by linarith) ⟨occupation_upper_region x hhi,occupation_le_critical_bound x hX⟩
  simpa using h

end HardCoreActivityThreshold
