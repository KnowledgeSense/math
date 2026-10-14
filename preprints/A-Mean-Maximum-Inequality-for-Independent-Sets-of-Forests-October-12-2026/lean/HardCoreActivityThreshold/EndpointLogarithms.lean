import HardCoreActivityThreshold.ScalarEndpoints

namespace HardCoreActivityThreshold
set_option maxHeartbeats 2000000
set_option maxRecDepth 8192

theorem logarithm_small_bounds : Real.log ((99/100) : ℝ)∈Set.Icc (-0.010050335854) (-0.010050335853) := by
  have hl := logarithm_enclosure (99/100) (99/100) (-5025167927/500000000000) (-10050335853/1000000000000) (1) (1) 14
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [scaledLogLower,logApproximation,logRemainder,Finset.sum_range_succ])
    (by norm_num [scaledLogUpper,logApproximation,logRemainder,Finset.sum_range_succ])
    (((99/100) : ℝ)) (by norm_num)
  norm_num at hl ⊢
  exact hl

theorem logarithm_lower_bounds : Real.log ((297/500) : ℝ)∈Set.Icc (-0.52087595962) (-0.520875959619) := by
  have hl := logarithm_enclosure (297/500) (297/500) (-26043797981/50000000000) (-520875959619/1000000000000) (1) (1) 14
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [scaledLogLower,logApproximation,logRemainder,Finset.sum_range_succ])
    (by norm_num [scaledLogUpper,logApproximation,logRemainder,Finset.sum_range_succ])
    (((297/500) : ℝ)) (by norm_num)
  norm_num at hl ⊢
  exact hl

theorem logarithm_upper_bounds : Real.log ((5353/10000) : ℝ)∈Set.Icc (-0.624927941583) (-0.624927941582) := by
  have hl := logarithm_enclosure (5353/10000) (5353/10000) (-624927941583/1000000000000) (-312463970791/500000000000) (1) (1) 14
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [scaledLogLower,logApproximation,logRemainder,Finset.sum_range_succ])
    (by norm_num [scaledLogUpper,logApproximation,logRemainder,Finset.sum_range_succ])
    (((5353/10000) : ℝ)) (by norm_num)
  norm_num at hl ⊢
  exact hl

theorem logarithm_half_bounds : Real.log ((607/1000) : ℝ)∈Set.Icc (-0.499226487923) (-0.499226487922) := by
  have hl := logarithm_enclosure (607/1000) (607/1000) (-499226487923/1000000000000) (-249613243961/500000000000) (1) (1) 14
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [scaledLogLower,logApproximation,logRemainder,Finset.sum_range_succ])
    (by norm_num [scaledLogUpper,logApproximation,logRemainder,Finset.sum_range_succ])
    (((607/1000) : ℝ)) (by norm_num)
  norm_num at hl ⊢
  exact hl

theorem logarithm_sixtytwo_bounds : Real.log ((537/1000) : ℝ)∈Set.Icc (-0.621757184474) (-0.621757184473) := by
  have hl := logarithm_enclosure (537/1000) (537/1000) (-310878592237/500000000000) (-621757184473/1000000000000) (1) (1) 14
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [scaledLogLower,logApproximation,logRemainder,Finset.sum_range_succ])
    (by norm_num [scaledLogUpper,logApproximation,logRemainder,Finset.sum_range_succ])
    (((537/1000) : ℝ)) (by norm_num)
  norm_num at hl ⊢
  exact hl

theorem logarithm_concavity_bounds : Real.log ((5/2) : ℝ)∈Set.Icc 0.916290731874 0.916290731875 := by
  have hl := logarithm_enclosure (5/2) (5/2) (458145365937/500000000000) (1466065171/1600000000) (-1) (-1) 14
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [scaledLogLower,logApproximation,logRemainder,Finset.sum_range_succ])
    (by norm_num [scaledLogUpper,logApproximation,logRemainder,Finset.sum_range_succ])
    (((5/2) : ℝ)) (by norm_num)
  norm_num at hl ⊢
  exact hl

end HardCoreActivityThreshold
