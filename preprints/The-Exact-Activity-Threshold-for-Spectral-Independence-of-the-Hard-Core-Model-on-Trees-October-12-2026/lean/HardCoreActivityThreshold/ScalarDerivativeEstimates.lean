import HardCoreActivityThreshold.DerivativeCover
import HardCoreActivityThreshold.ConcavityEndpoint
import HardCoreActivityThreshold.EndpointLogarithms

namespace HardCoreActivityThreshold

theorem concavityEndpoint_pos : 0<concavityEndpoint := by
  unfold concavityEndpoint
  exact Real.log_pos (by norm_num)

theorem concavityEndpoint_lt_criticalEndpoint : concavityEndpoint<criticalEndpoint := by
  unfold concavityEndpoint criticalEndpoint
  apply Real.strictMonoOn_log (by norm_num) (show 1+criticalActivity∈Set.Ioi 0 by simp only [Set.mem_Ioi]; linarith [scalarCriticalActivity_pos])
  linarith [criticalActivity_bounds.1]

theorem secondPartitionDerivative_concavityEndpoint_neg :
    secondPartitionDerivative concavityEndpoint<0 := by
  apply second_derivative_at_occupation_six_tenths _ concavityEndpoint_pos
  rw [occupation_concavityEndpoint]
  exact ⟨le_rfl,le_rfl⟩

theorem fourthPartitionDerivative_pos (x : ℝ) (hx : 0<x) (hA : x≤concavityEndpoint) :
    0<fourthPartitionDerivative x := by
  have hq0 := occupation_pos x hx
  have hqA : scalarOccupation x≤0.6 := by
    rw [←occupation_concavityEndpoint]
    exact occupation_strictMono.monotone hA
  have hy := remainingPotential_nonneg x hx (hA.trans concavityEndpoint_lt_criticalEndpoint.le)
  have hn : 0<fourthNumerator (scalarOccupation x) (remainingPotential x) := by
    by_cases hq : scalarOccupation x≤0.05
    · exact fourthNumerator_pos_small _ _ ⟨hq0.le,hq⟩ hy
    · exact derivative_cover_d_fourth x hx ⟨(lt_of_not_ge hq).le,hqA⟩
  exact div_pos hn (sq_pos_of_pos hq0)

theorem occupation_half_ge (x : ℝ) (hx : 0.5≤x) : 0.393≤scalarOccupation x := by
  rw [le_occupation_iff x 0.393 (by norm_num)]
  have h := logarithm_half_bounds
  norm_num at h ⊢
  linarith [h.1]

theorem occupation_sixtytwo_le (x : ℝ) (hx : x≤0.62) : scalarOccupation x≤0.463 := by
  rw [occupation_le_iff x 0.463 (by norm_num)]
  have h := logarithm_sixtytwo_bounds
  norm_num at h ⊢
  linarith [h.2]

theorem secondFivefoldDerivative_pos (x : ℝ) (hx : x∈Set.Icc 0.5 0.62) :
    0<secondFivefoldDerivative x := by
  exact derivative_cover_e_Gsecond x (by linarith [hx.1])
    ⟨occupation_half_ge x hx.1,occupation_sixtytwo_le x hx.2⟩

end HardCoreActivityThreshold
