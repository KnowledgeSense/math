import HardCoreActivityThreshold.DerivativePolynomials

namespace HardCoreActivityThreshold
set_option maxHeartbeats 4000000
set_option maxRecDepth 8192

theorem gap_box_0040 (x : ℝ) (hx : 0<x)
    (hq : scalarOccupation x∈Set.Icc 0.4455 0.463) :
    0<secondFivefoldDerivative x := by
  have hc : 1-scalarOccupation x∈Set.Icc (((537/1000) : ℚ) : ℝ) (((1109/2000) : ℚ) : ℝ) := by
    norm_num
    constructor <;> linarith [hq.1,hq.2]
  have hlx := logarithm_enclosure (537/1000) (1109/2000) (-310878592237/500000000000) (-589688472191/1000000000000) (1) (1) 14
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [scaledLogLower,logApproximation,logRemainder,Finset.sum_range_succ])
    (by norm_num [scaledLogUpper,logApproximation,logRemainder,Finset.sum_range_succ])
    (1-scalarOccupation x) (hc)
  have hxi : x∈Set.Icc 0.589688472191 0.621757184474 := by
    have he := occupation_log_identity x
    norm_num at hlx
    constructor <;> linarith [hlx.1,hlx.2]
  have hr := remaining_ratio_bounds ((891/2000)) ((463/1000)) ((1567367648339/100000000000)) ((1567367648341/100000000000))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (scalarOccupation x) criticalActivity (by convert hq using 1; norm_num) (by convert criticalActivity_bounds using 1; norm_num)
  have hri : criticalActivity*(1-scalarOccupation x)/scalarOccupation x∈Set.Icc
      (((841676427158043/46300000000000) : ℚ) : ℝ) (((158019156546379/8100000000000) : ℚ) : ℝ) := by
    norm_num at hr ⊢
    exact hr
  have hly := logarithm_enclosure (841676427158043/46300000000000) (158019156546379/8100000000000) (580050737701/200000000000) (742713051991/250000000000) (-4) (-4) 14
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [scaledLogLower,logApproximation,logRemainder,Finset.sum_range_succ])
    (by norm_num [scaledLogUpper,logApproximation,logRemainder,Finset.sum_range_succ])
    (criticalActivity*(1-scalarOccupation x)/scalarOccupation x) (hri)
  have hyi : remainingPotential x∈Set.Icc 2.900253688505 2.970852207964 := by
    rw [remainingPotential_eq_log_div x hx,occupation_remaining_ratio x hx]
    norm_num at hly ⊢
    exact hly
  have hz := cubicCenter_tight_bounds
  unfold secondFivefoldDerivative
  rw [secondPartitionDerivative_expanded]
  rw [show cubicCoefficient=(0.016 : ℝ) by norm_num [cubicCoefficient]]
  unfold expandedSecond
  dyadic_interval +kernel [prec := 80]

end HardCoreActivityThreshold
