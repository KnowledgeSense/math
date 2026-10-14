import HardCoreActivityThreshold.DerivativePolynomials

namespace HardCoreActivityThreshold
set_option maxHeartbeats 4000000
set_option maxRecDepth 8192

theorem second_derivative_at_occupation_six_tenths (x : ℝ) (hx : 0<x)
    (hq : scalarOccupation x∈Set.Icc 0.6 0.6) :
    secondPartitionDerivative x<0 := by
  have hc : 1-scalarOccupation x∈Set.Icc (((2/5) : ℚ) : ℝ) (((2/5) : ℚ) : ℝ) := by
    norm_num
    linarith [hq.1,hq.2]
  have hlx := logarithm_enclosure (2/5) (2/5) (-1466065171/1600000000) (-458145365937/500000000000) (2) (2) 14
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [scaledLogLower,logApproximation,logRemainder,Finset.sum_range_succ])
    (by norm_num [scaledLogUpper,logApproximation,logRemainder,Finset.sum_range_succ])
    (1-scalarOccupation x) (hc)
  have hxi : x∈Set.Icc 0.916290731874 0.916290731875 := by
    have he := occupation_log_identity x
    norm_num at hlx
    constructor <;> linarith [hlx.1,hlx.2]
  have hr := remaining_ratio_bounds ((3/5)) ((3/5)) ((1567367648339/100000000000)) ((1567367648341/100000000000))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (scalarOccupation x) criticalActivity (by convert hq using 1; norm_num) (by convert criticalActivity_bounds using 1; norm_num)
  have hri : criticalActivity*(1-scalarOccupation x)/scalarOccupation x∈Set.Icc
      (((1567367648339/150000000000) : ℚ) : ℝ) (((1567367648341/150000000000) : ℚ) : ℝ) := by
    norm_num at hr ⊢
    exact hr
  have hly := logarithm_enclosure (1567367648339/150000000000) (1567367648341/150000000000) (1173258769987/500000000000) (293314692497/125000000000) (-3) (-3) 14
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [scaledLogLower,logApproximation,logRemainder,Finset.sum_range_succ])
    (by norm_num [scaledLogUpper,logApproximation,logRemainder,Finset.sum_range_succ])
    (criticalActivity*(1-scalarOccupation x)/scalarOccupation x) (hri)
  have hyi : remainingPotential x∈Set.Icc 2.346517539974 2.346517539976 := by
    rw [remainingPotential_eq_log_div x hx,occupation_remaining_ratio x hx]
    norm_num at hly ⊢
    exact hly
  have hz := cubicCenter_tight_bounds
  rw [secondPartitionDerivative_expanded]
  unfold expandedSecond
  dyadic_interval +kernel [prec := 80]

end HardCoreActivityThreshold
