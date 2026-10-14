import HardCoreActivityThreshold.DerivativePolynomials

namespace HardCoreActivityThreshold
set_option maxHeartbeats 4000000
set_option maxRecDepth 8192

theorem fourth_box_0020 (x : ℝ) (hx : 0<x)
    (hq : scalarOccupation x∈Set.Icc 0.48828125 0.496875) :
    0<fourthNumerator (scalarOccupation x) (remainingPotential x) := by
  have hc : 1-scalarOccupation x∈Set.Icc (((161/320) : ℚ) : ℝ) (((131/256) : ℚ) : ℝ) := by
    norm_num
    constructor <;> linarith [hq.1,hq.2]
  have hlx := logarithm_enclosure (161/320) (131/256) (-68691663081/100000000000) (-334990060639/500000000000) (1) (1) 14
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [scaledLogLower,logApproximation,logRemainder,Finset.sum_range_succ])
    (by norm_num [scaledLogUpper,logApproximation,logRemainder,Finset.sum_range_succ])
    (1-scalarOccupation x) (hc)
  have hxi : x∈Set.Icc 0.669980121278 0.68691663081 := by
    have he := occupation_log_identity x
    norm_num at hlx
    constructor <;> linarith [hlx.1,hlx.2]
  have hr := remaining_ratio_bounds ((125/256)) ((159/320)) ((1567367648339/100000000000)) ((1567367648341/100000000000))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (scalarOccupation x) criticalActivity (by convert hq using 1; norm_num) (by convert criticalActivity_bounds using 1; norm_num)
  have hri : criticalActivity*(1-scalarOccupation x)/scalarOccupation x∈Set.Icc
      (((252346191382579/15900000000000) : ℚ) : ℝ) (((205325161932671/12500000000000) : ℚ) : ℝ) := by
    norm_num at hr ⊢
    exact hr
  have hly := logarithm_enclosure (252346191382579/15900000000000) (205325161932671/12500000000000) (1382241405423/500000000000) (2798866233983/1000000000000) (-3) (-4) 14
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [scaledLogLower,logApproximation,logRemainder,Finset.sum_range_succ])
    (by norm_num [scaledLogUpper,logApproximation,logRemainder,Finset.sum_range_succ])
    (criticalActivity*(1-scalarOccupation x)/scalarOccupation x) (hri)
  have hyi : remainingPotential x∈Set.Icc 2.764482810846 2.798866233983 := by
    rw [remainingPotential_eq_log_div x hx,occupation_remaining_ratio x hx]
    norm_num at hly ⊢
    exact hly
  have hz := cubicCenter_tight_bounds
  rw [fourthNumerator_expanded]
  unfold expandedFourth
  dyadic_interval +kernel [prec := 80]

theorem fourth_box_0021 (x : ℝ) (hx : 0<x)
    (hq : scalarOccupation x∈Set.Icc 0.496875 0.50546875) :
    0<fourthNumerator (scalarOccupation x) (remainingPotential x) := by
  have hc : 1-scalarOccupation x∈Set.Icc (((633/1280) : ℚ) : ℝ) (((161/320) : ℚ) : ℝ) := by
    norm_num
    constructor <;> linarith [hq.1,hq.2]
  have hlx := logarithm_enclosure (633/1280) (161/320) (-70414493477/100000000000) (-686916630809/1000000000000) (2) (1) 14
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [scaledLogLower,logApproximation,logRemainder,Finset.sum_range_succ])
    (by norm_num [scaledLogUpper,logApproximation,logRemainder,Finset.sum_range_succ])
    (1-scalarOccupation x) (hc)
  have hxi : x∈Set.Icc 0.686916630809 0.70414493477 := by
    have he := occupation_log_identity x
    norm_num at hlx
    constructor <;> linarith [hlx.1,hlx.2]
  have hr := remaining_ratio_bounds ((159/320)) ((647/1280)) ((1567367648339/100000000000)) ((1567367648341/100000000000))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (scalarOccupation x) criticalActivity (by convert hq using 1; norm_num) (by convert criticalActivity_bounds using 1; norm_num)
  have hri : criticalActivity*(1-scalarOccupation x)/scalarOccupation x∈Set.Icc
      (((992143721398587/64700000000000) : ℚ) : ℝ) (((4761248894017/300000000000) : ℚ) : ℝ) := by
    norm_num at hr ⊢
    exact hr
  have hly := logarithm_enclosure (992143721398587/64700000000000) (4761248894017/300000000000) (109204271029/40000000000) (2764482810849/1000000000000) (-3) (-3) 14
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [scaledLogLower,logApproximation,logRemainder,Finset.sum_range_succ])
    (by norm_num [scaledLogUpper,logApproximation,logRemainder,Finset.sum_range_succ])
    (criticalActivity*(1-scalarOccupation x)/scalarOccupation x) (hri)
  have hyi : remainingPotential x∈Set.Icc 2.730106775725 2.764482810849 := by
    rw [remainingPotential_eq_log_div x hx,occupation_remaining_ratio x hx]
    norm_num at hly ⊢
    exact hly
  have hz := cubicCenter_tight_bounds
  rw [fourthNumerator_expanded]
  unfold expandedFourth
  dyadic_interval +kernel [prec := 80]

theorem fourth_box_0022 (x : ℝ) (hx : 0<x)
    (hq : scalarOccupation x∈Set.Icc 0.50546875 0.5140625) :
    0<fourthNumerator (scalarOccupation x) (remainingPotential x) := by
  have hc : 1-scalarOccupation x∈Set.Icc (((311/640) : ℚ) : ℝ) (((633/1280) : ℚ) : ℝ) := by
    norm_num
    constructor <;> linarith [hq.1,hq.2]
  have hlx := logarithm_enclosure (311/640) (633/1280) (-28867010567/40000000000) (-704144934769/1000000000000) (2) (2) 14
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [scaledLogLower,logApproximation,logRemainder,Finset.sum_range_succ])
    (by norm_num [scaledLogUpper,logApproximation,logRemainder,Finset.sum_range_succ])
    (1-scalarOccupation x) (hc)
  have hxi : x∈Set.Icc 0.704144934769 0.721675264175 := by
    have he := occupation_log_identity x
    norm_num at hlx
    constructor <;> linarith [hlx.1,hlx.2]
  have hr := remaining_ratio_bounds ((647/1280)) ((329/640)) ((1567367648339/100000000000)) ((1567367648341/100000000000))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (scalarOccupation x) criticalActivity (by convert hq using 1; norm_num) (by convert criticalActivity_bounds using 1; norm_num)
  have hri : criticalActivity*(1-scalarOccupation x)/scalarOccupation x∈Set.Icc
      (((10371305077307/700000000000) : ℚ) : ℝ) (((992143721399853/64700000000000) : ℚ) : ℝ) := by
    norm_num at hr ⊢
    exact hr
  have hly := logarithm_enclosure (10371305077307/700000000000) (992143721399853/64700000000000) (336964726187/125000000000) (170631673483/62500000000) (-3) (-3) 14
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [scaledLogLower,logApproximation,logRemainder,Finset.sum_range_succ])
    (by norm_num [scaledLogUpper,logApproximation,logRemainder,Finset.sum_range_succ])
    (criticalActivity*(1-scalarOccupation x)/scalarOccupation x) (hri)
  have hyi : remainingPotential x∈Set.Icc 2.695717809496 2.730106775728 := by
    rw [remainingPotential_eq_log_div x hx,occupation_remaining_ratio x hx]
    norm_num at hly ⊢
    exact hly
  have hz := cubicCenter_tight_bounds
  rw [fourthNumerator_expanded]
  unfold expandedFourth
  dyadic_interval +kernel [prec := 80]

theorem fourth_box_0023 (x : ℝ) (hx : 0<x)
    (hq : scalarOccupation x∈Set.Icc 0.5140625 0.52265625) :
    0<fourthNumerator (scalarOccupation x) (remainingPotential x) := by
  have hc : 1-scalarOccupation x∈Set.Icc (((611/1280) : ℚ) : ℝ) (((311/640) : ℚ) : ℝ) := by
    norm_num
    constructor <;> linarith [hq.1,hq.2]
  have hlx := logarithm_enclosure (611/1280) (311/640) (-739518397743/1000000000000) (-360837632087/500000000000) (2) (2) 14
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [scaledLogLower,logApproximation,logRemainder,Finset.sum_range_succ])
    (by norm_num [scaledLogUpper,logApproximation,logRemainder,Finset.sum_range_succ])
    (1-scalarOccupation x) (hc)
  have hxi : x∈Set.Icc 0.721675264174 0.739518397743 := by
    have he := occupation_log_identity x
    norm_num at hlx
    constructor <;> linarith [hlx.1,hlx.2]
  have hr := remaining_ratio_bounds ((329/640)) ((669/1280)) ((1567367648339/100000000000)) ((1567367648341/100000000000))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (scalarOccupation x) criticalActivity (by convert hq using 1; norm_num) (by convert criticalActivity_bounds using 1; norm_num)
  have hri : criticalActivity*(1-scalarOccupation x)/scalarOccupation x∈Set.Icc
      (((957661633135129/66900000000000) : ℚ) : ℝ) (((487451338634051/32900000000000) : ℚ) : ℝ) := by
    norm_num at hr ⊢
    exact hr
  have hly := logarithm_enclosure (957661633135129/66900000000000) (487451338634051/32900000000000) (1330647773563/500000000000) (1347858904749/500000000000) (-3) (-3) 14
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [scaledLogLower,logApproximation,logRemainder,Finset.sum_range_succ])
    (by norm_num [scaledLogUpper,logApproximation,logRemainder,Finset.sum_range_succ])
    (criticalActivity*(1-scalarOccupation x)/scalarOccupation x) (hri)
  have hyi : remainingPotential x∈Set.Icc 2.661295547126 2.695717809498 := by
    rw [remainingPotential_eq_log_div x hx,occupation_remaining_ratio x hx]
    norm_num at hly ⊢
    exact hly
  have hz := cubicCenter_tight_bounds
  rw [fourthNumerator_expanded]
  unfold expandedFourth
  dyadic_interval +kernel [prec := 80]

theorem fourth_box_0024 (x : ℝ) (hx : 0<x)
    (hq : scalarOccupation x∈Set.Icc 0.52265625 0.53125) :
    0<fourthNumerator (scalarOccupation x) (remainingPotential x) := by
  have hc : 1-scalarOccupation x∈Set.Icc (((15/32) : ℚ) : ℝ) (((611/1280) : ℚ) : ℝ) := by
    norm_num
    constructor <;> linarith [hq.1,hq.2]
  have hlx := logarithm_enclosure (15/32) (611/1280) (-378842850849/500000000000) (-369759198871/500000000000) (2) (2) 14
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [scaledLogLower,logApproximation,logRemainder,Finset.sum_range_succ])
    (by norm_num [scaledLogUpper,logApproximation,logRemainder,Finset.sum_range_succ])
    (1-scalarOccupation x) (hc)
  have hxi : x∈Set.Icc 0.739518397742 0.757685701698 := by
    have he := occupation_log_identity x
    norm_num at hlx
    constructor <;> linarith [hlx.1,hlx.2]
  have hr := remaining_ratio_bounds ((669/1280)) ((17/32)) ((1567367648339/100000000000)) ((1567367648341/100000000000))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (scalarOccupation x) criticalActivity (by convert hq using 1; norm_num) (by convert criticalActivity_bounds using 1; norm_num)
  have hri : criticalActivity*(1-scalarOccupation x)/scalarOccupation x∈Set.Icc
      (((4702102945017/340000000000) : ℚ) : ℝ) (((957661633136351/66900000000000) : ℚ) : ℝ) := by
    norm_num at hr ⊢
    exact hr
  have hly := logarithm_enclosure (4702102945017/340000000000) (957661633136351/66900000000000) (328352438141/125000000000) (332661943391/125000000000) (-3) (-3) 14
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [scaledLogLower,logApproximation,logRemainder,Finset.sum_range_succ])
    (by norm_num [scaledLogUpper,logApproximation,logRemainder,Finset.sum_range_succ])
    (criticalActivity*(1-scalarOccupation x)/scalarOccupation x) (hri)
  have hyi : remainingPotential x∈Set.Icc 2.626819505128 2.661295547128 := by
    rw [remainingPotential_eq_log_div x hx,occupation_remaining_ratio x hx]
    norm_num at hly ⊢
    exact hly
  have hz := cubicCenter_tight_bounds
  rw [fourthNumerator_expanded]
  unfold expandedFourth
  dyadic_interval +kernel [prec := 80]

theorem fourth_box_0025 (x : ℝ) (hx : 0<x)
    (hq : scalarOccupation x∈Set.Icc 0.53125 0.53984375) :
    0<fourthNumerator (scalarOccupation x) (remainingPotential x) := by
  have hc : 1-scalarOccupation x∈Set.Icc (((589/1280) : ℚ) : ℝ) (((15/32) : ℚ) : ℝ) := by
    norm_num
    constructor <;> linarith [hq.1,hq.2]
  have hlx := logarithm_enclosure (589/1280) (15/32) (-776189173263/1000000000000) (-757685701697/1000000000000) (2) (2) 14
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [scaledLogLower,logApproximation,logRemainder,Finset.sum_range_succ])
    (by norm_num [scaledLogUpper,logApproximation,logRemainder,Finset.sum_range_succ])
    (1-scalarOccupation x) (hc)
  have hxi : x∈Set.Icc 0.757685701697 0.776189173263 := by
    have he := occupation_log_identity x
    norm_num at hlx
    constructor <;> linarith [hlx.1,hlx.2]
  have hr := remaining_ratio_bounds ((17/32)) ((691/1280)) ((1567367648339/100000000000)) ((1567367648341/100000000000))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (scalarOccupation x) criticalActivity (by convert hq using 1; norm_num) (by convert criticalActivity_bounds using 1; norm_num)
  have hri : criticalActivity*(1-scalarOccupation x)/scalarOccupation x∈Set.Icc
      (((923179544871671/69100000000000) : ℚ) : ℝ) (((4702102945023/340000000000) : ℚ) : ℝ) := by
    norm_num at hr ⊢
    exact hr
  have hly := logarithm_enclosure (923179544871671/69100000000000) (4702102945023/340000000000) (1296134503983/500000000000) (2626819505131/1000000000000) (-3) (-3) 14
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [scaledLogLower,logApproximation,logRemainder,Finset.sum_range_succ])
    (by norm_num [scaledLogUpper,logApproximation,logRemainder,Finset.sum_range_succ])
    (criticalActivity*(1-scalarOccupation x)/scalarOccupation x) (hri)
  have hyi : remainingPotential x∈Set.Icc 2.592269007966 2.626819505131 := by
    rw [remainingPotential_eq_log_div x hx,occupation_remaining_ratio x hx]
    norm_num at hly ⊢
    exact hly
  have hz := cubicCenter_tight_bounds
  rw [fourthNumerator_expanded]
  unfold expandedFourth
  dyadic_interval +kernel [prec := 80]

theorem fourth_box_0026 (x : ℝ) (hx : 0<x)
    (hq : scalarOccupation x∈Set.Icc 0.53984375 0.5484375) :
    0<fourthNumerator (scalarOccupation x) (remainingPotential x) := by
  have hc : 1-scalarOccupation x∈Set.Icc (((289/640) : ℚ) : ℝ) (((589/1280) : ℚ) : ℝ) := by
    norm_num
    constructor <;> linarith [hq.1,hq.2]
  have hlx := logarithm_enclosure (289/640) (589/1280) (-397520744121/500000000000) (-388094586631/500000000000) (2) (2) 14
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [scaledLogLower,logApproximation,logRemainder,Finset.sum_range_succ])
    (by norm_num [scaledLogUpper,logApproximation,logRemainder,Finset.sum_range_succ])
    (1-scalarOccupation x) (hc)
  have hxi : x∈Set.Icc 0.776189173262 0.795041488242 := by
    have he := occupation_log_identity x
    norm_num at hlx
    constructor <;> linarith [hlx.1,hlx.2]
  have hr := remaining_ratio_bounds ((691/1280)) ((351/640)) ((1567367648339/100000000000)) ((1567367648341/100000000000))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (scalarOccupation x) criticalActivity (by convert hq using 1; norm_num) (by convert criticalActivity_bounds using 1; norm_num)
  have hri : criticalActivity*(1-scalarOccupation x)/scalarOccupation x∈Set.Icc
      (((452969250369971/35100000000000) : ℚ) : ℝ) (((923179544872849/69100000000000) : ℚ) : ℝ) := by
    norm_num at hr ⊢
    exact hr
  have hly := logarithm_enclosure (452969250369971/35100000000000) (923179544872849/69100000000000) (2557623112729/1000000000000) (81008406499/31250000000) (-3) (-3) 14
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [scaledLogLower,logApproximation,logRemainder,Finset.sum_range_succ])
    (by norm_num [scaledLogUpper,logApproximation,logRemainder,Finset.sum_range_succ])
    (criticalActivity*(1-scalarOccupation x)/scalarOccupation x) (hri)
  have hyi : remainingPotential x∈Set.Icc 2.557623112729 2.592269007968 := by
    rw [remainingPotential_eq_log_div x hx,occupation_remaining_ratio x hx]
    norm_num at hly ⊢
    exact hly
  have hz := cubicCenter_tight_bounds
  rw [fourthNumerator_expanded]
  unfold expandedFourth
  dyadic_interval +kernel [prec := 80]

theorem fourth_box_0027 (x : ℝ) (hx : 0<x)
    (hq : scalarOccupation x∈Set.Icc 0.5484375 0.55703125) :
    0<fourthNumerator (scalarOccupation x) (remainingPotential x) := by
  have hc : 1-scalarOccupation x∈Set.Icc (((567/1280) : ℚ) : ℝ) (((289/640) : ℚ) : ℝ) := by
    norm_num
    constructor <;> linarith [hq.1,hq.2]
  have hlx := logarithm_enclosure (567/1280) (289/640) (-407128026593/500000000000) (-795041488241/1000000000000) (2) (2) 14
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [scaledLogLower,logApproximation,logRemainder,Finset.sum_range_succ])
    (by norm_num [scaledLogUpper,logApproximation,logRemainder,Finset.sum_range_succ])
    (1-scalarOccupation x) (hc)
  have hxi : x∈Set.Icc 0.795041488241 0.814256053186 := by
    have he := occupation_log_identity x
    norm_num at hlx
    constructor <;> linarith [hlx.1,hlx.2]
  have hr := remaining_ratio_bounds ((351/640)) ((713/1280)) ((1567367648339/100000000000)) ((1567367648341/100000000000))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (scalarOccupation x) criticalActivity (by convert hq using 1; norm_num) (by convert criticalActivity_bounds using 1; norm_num)
  have hri : criticalActivity*(1-scalarOccupation x)/scalarOccupation x∈Set.Icc
      (((38639019852531/3100000000000) : ℚ) : ℝ) (((452969250370549/35100000000000) : ℚ) : ℝ) := by
    norm_num at hr ⊢
    exact hr
  have hly := logarithm_enclosure (38639019852531/3100000000000) (452969250370549/35100000000000) (630715132849/250000000000) (2557623112731/1000000000000) (-3) (-3) 14
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [scaledLogLower,logApproximation,logRemainder,Finset.sum_range_succ])
    (by norm_num [scaledLogUpper,logApproximation,logRemainder,Finset.sum_range_succ])
    (criticalActivity*(1-scalarOccupation x)/scalarOccupation x) (hri)
  have hyi : remainingPotential x∈Set.Icc 2.522860531396 2.557623112731 := by
    rw [remainingPotential_eq_log_div x hx,occupation_remaining_ratio x hx]
    norm_num at hly ⊢
    exact hly
  have hz := cubicCenter_tight_bounds
  rw [fourthNumerator_expanded]
  unfold expandedFourth
  dyadic_interval +kernel [prec := 80]

theorem fourth_box_0028 (x : ℝ) (hx : 0<x)
    (hq : scalarOccupation x∈Set.Icc 0.55703125 0.565625) :
    0<fourthNumerator (scalarOccupation x) (remainingPotential x) := by
  have hc : 1-scalarOccupation x∈Set.Icc (((139/320) : ℚ) : ℝ) (((567/1280) : ℚ) : ℝ) := by
    norm_num
    constructor <;> linarith [hq.1,hq.2]
  have hlx := logarithm_enclosure (139/320) (567/1280) (-104230882833/125000000000) (-162851210637/200000000000) (2) (2) 14
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [scaledLogLower,logApproximation,logRemainder,Finset.sum_range_succ])
    (by norm_num [scaledLogUpper,logApproximation,logRemainder,Finset.sum_range_succ])
    (1-scalarOccupation x) (hc)
  have hxi : x∈Set.Icc 0.814256053185 0.833847062664 := by
    have he := occupation_log_identity x
    norm_num at hlx
    constructor <;> linarith [hlx.1,hlx.2]
  have hr := remaining_ratio_bounds ((713/1280)) ((181/320)) ((1567367648339/100000000000)) ((1567367648341/100000000000))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (scalarOccupation x) criticalActivity (by convert hq using 1; norm_num) (by convert criticalActivity_bounds using 1; norm_num)
  have hri : criticalActivity*(1-scalarOccupation x)/scalarOccupation x∈Set.Icc
      (((217864103119121/18100000000000) : ℚ) : ℝ) (((888697456609347/71300000000000) : ℚ) : ℝ) := by
    norm_num at hr ⊢
    exact hr
  have hly := logarithm_enclosure (217864103119121/18100000000000) (888697456609347/71300000000000) (2487959549947/1000000000000) (1261430265699/500000000000) (-3) (-3) 14
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [scaledLogLower,logApproximation,logRemainder,Finset.sum_range_succ])
    (by norm_num [scaledLogUpper,logApproximation,logRemainder,Finset.sum_range_succ])
    (criticalActivity*(1-scalarOccupation x)/scalarOccupation x) (hri)
  have hyi : remainingPotential x∈Set.Icc 2.487959549947 2.522860531398 := by
    rw [remainingPotential_eq_log_div x hx,occupation_remaining_ratio x hx]
    norm_num at hly ⊢
    exact hly
  have hz := cubicCenter_tight_bounds
  rw [fourthNumerator_expanded]
  unfold expandedFourth
  dyadic_interval +kernel [prec := 80]

theorem fourth_box_0029 (x : ℝ) (hx : 0<x)
    (hq : scalarOccupation x∈Set.Icc 0.565625 0.569921875) :
    0<fourthNumerator (scalarOccupation x) (remainingPotential x) := by
  have hc : 1-scalarOccupation x∈Set.Icc (((1101/2560) : ℚ) : ℝ) (((139/320) : ℚ) : ℝ) := by
    norm_num
    constructor <;> linarith [hq.1,hq.2]
  have hlx := logarithm_enclosure (1101/2560) (139/320) (-843788400751/1000000000000) (-833847062663/1000000000000) (2) (2) 14
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [scaledLogLower,logApproximation,logRemainder,Finset.sum_range_succ])
    (by norm_num [scaledLogUpper,logApproximation,logRemainder,Finset.sum_range_succ])
    (1-scalarOccupation x) (hc)
  have hxi : x∈Set.Icc 0.833847062663 0.843788400751 := by
    have he := occupation_log_identity x
    norm_num at hlx
    constructor <;> linarith [hlx.1,hlx.2]
  have hr := remaining_ratio_bounds ((181/320)) ((1459/2560)) ((1567367648339/100000000000)) ((1567367648341/100000000000))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (scalarOccupation x) criticalActivity (by convert hq using 1; norm_num) (by convert criticalActivity_bounds using 1; norm_num)
  have hri : criticalActivity*(1-scalarOccupation x)/scalarOccupation x∈Set.Icc
      (((1725671780821239/145900000000000) : ℚ) : ℝ) (((217864103119399/18100000000000) : ℚ) : ℝ) := by
    norm_num at hr ⊢
    exact hr
  have hly := logarithm_enclosure (1725671780821239/145900000000000) (217864103119399/18100000000000) (1235225118141/500000000000) (2487959549949/1000000000000) (-3) (-3) 14
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [scaledLogLower,logApproximation,logRemainder,Finset.sum_range_succ])
    (by norm_num [scaledLogUpper,logApproximation,logRemainder,Finset.sum_range_succ])
    (criticalActivity*(1-scalarOccupation x)/scalarOccupation x) (hri)
  have hyi : remainingPotential x∈Set.Icc 2.470450236282 2.487959549949 := by
    rw [remainingPotential_eq_log_div x hx,occupation_remaining_ratio x hx]
    norm_num at hly ⊢
    exact hly
  have hz := cubicCenter_tight_bounds
  rw [fourthNumerator_expanded]
  unfold expandedFourth
  dyadic_interval +kernel [prec := 80]

end HardCoreActivityThreshold
