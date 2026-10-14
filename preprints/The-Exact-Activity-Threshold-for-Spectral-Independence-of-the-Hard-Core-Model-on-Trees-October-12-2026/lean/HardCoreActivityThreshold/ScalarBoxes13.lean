import HardCoreActivityThreshold.ScalarCoordinates

namespace HardCoreActivityThreshold
set_option maxHeartbeats 4000000
set_option maxRecDepth 8192

theorem scalar_box_0208 (x : ℝ) (hx : 0<x)
    (hq : scalarOccupation x∈Set.Icc 0.4510657958984375 0.451179443359375) :
    scalarPartitionFunction x<1.001*x := by
  have hc : 1-scalarOccupation x∈Set.Icc (((2247969/4096000) : ℚ) : ℝ) (((4496869/8192000) : ℚ) : ℝ) := by
    norm_num
    constructor <;> linarith [hq.1,hq.2]
  have hlx := logarithm_enclosure (2247969/4096000) (4496869/8192000) (-599983745837/1000000000000) (-74972086433/125000000000) (1) (1) 14
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [scaledLogLower,logApproximation,logRemainder,Finset.sum_range_succ])
    (by norm_num [scaledLogUpper,logApproximation,logRemainder,Finset.sum_range_succ])
    (1-scalarOccupation x) (hc)
  have hxi : x∈Set.Icc 0.599776691464 0.599983745837 := by
    have he := occupation_log_identity x
    norm_num at hlx
    constructor <;> linarith [hlx.1,hlx.2]
  have hr := remaining_ratio_bounds ((3695131/8192000)) ((1848031/4096000)) ((1567367648339/100000000000)) ((1567367648341/100000000000))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (scalarOccupation x) criticalActivity (by convert hq using 1; norm_num) (by convert criticalActivity_bounds using 1; norm_num)
  have hri : criticalActivity*(1-scalarOccupation x)/scalarOccupation x∈Set.Icc
      (((3523393885068973491/184803100000000000) : ℚ) : ℝ) (((640749726311594939/33592100000000000) : ℚ) : ℝ) := by
    norm_num at hr ⊢
    exact hr
  have hly := logarithm_enclosure (3523393885068973491/184803100000000000) (640749726311594939/33592100000000000) (736972260503/250000000000) (294834801783/100000000000) (-4) (-4) 14
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [scaledLogLower,logApproximation,logRemainder,Finset.sum_range_succ])
    (by norm_num [scaledLogUpper,logApproximation,logRemainder,Finset.sum_range_succ])
    (criticalActivity*(1-scalarOccupation x)/scalarOccupation x) (hri)
  have hyi : remainingPotential x∈Set.Icc (2.947889042012) (2.94834801783) := by
    rw [remainingPotential_eq_log_div x hx,occupation_remaining_ratio x hx]
    norm_num at hly ⊢
    exact hly
  have hz := cubicCenter_tight_bounds
  have hm : (scalarOccupation x)*(scalarOccupation x)*(remainingPotential x*
      (1+0.016*((remainingPotential x-cubicCenter)*(remainingPotential x-cubicCenter))))<1.001*x := by
    dyadic_interval +kernel [prec := 80]
  convert hm using 1; simp [scalarPartitionFunction,hx.ne',potential,cubicPotential,cubicCoefficient,pow_two]; norm_num

theorem scalar_box_0209 (x : ℝ) (hx : 0<x)
    (hq : scalarOccupation x∈Set.Icc 0.451179443359375 0.4512930908203125) :
    scalarPartitionFunction x<1.001*x := by
  have hc : 1-scalarOccupation x∈Set.Icc (((4495007/8192000) : ℚ) : ℝ) (((2247969/4096000) : ℚ) : ℝ) := by
    norm_num
    constructor <;> linarith [hq.1,hq.2]
  have hlx := logarithm_enclosure (4495007/8192000) (2247969/4096000) (-600190843089/1000000000000) (-149995936459/250000000000) (1) (1) 14
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [scaledLogLower,logApproximation,logRemainder,Finset.sum_range_succ])
    (by norm_num [scaledLogUpper,logApproximation,logRemainder,Finset.sum_range_succ])
    (1-scalarOccupation x) (hc)
  have hxi : x∈Set.Icc 0.599983745836 0.600190843089 := by
    have he := occupation_log_identity x
    norm_num at hlx
    constructor <;> linarith [hlx.1,hlx.2]
  have hr := remaining_ratio_bounds ((1848031/4096000)) ((3696993/8192000)) ((1567367648339/100000000000)) ((1567367648341/100000000000))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (scalarOccupation x) criticalActivity (by convert hq using 1; norm_num) (by convert criticalActivity_bounds using 1; norm_num)
  have hri : criticalActivity*(1-scalarOccupation x)/scalarOccupation x∈Set.Icc
      (((7045328550857343373/369699300000000000) : ℚ) : ℝ) (((3523393885073469429/184803100000000000) : ℚ) : ℝ) := by
    norm_num at hr ⊢
    exact hr
  have hly := logarithm_enclosure (7045328550857343373/369699300000000000) (3523393885073469429/184803100000000000) (589486017353/200000000000) (589577808403/200000000000) (-4) (-4) 14
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [scaledLogLower,logApproximation,logRemainder,Finset.sum_range_succ])
    (by norm_num [scaledLogUpper,logApproximation,logRemainder,Finset.sum_range_succ])
    (criticalActivity*(1-scalarOccupation x)/scalarOccupation x) (hri)
  have hyi : remainingPotential x∈Set.Icc (2.947430086765) (2.947889042015) := by
    rw [remainingPotential_eq_log_div x hx,occupation_remaining_ratio x hx]
    norm_num at hly ⊢
    exact hly
  have hz := cubicCenter_tight_bounds
  have hm : (scalarOccupation x)*(scalarOccupation x)*(remainingPotential x*
      (1+0.016*((remainingPotential x-cubicCenter)*(remainingPotential x-cubicCenter))))<1.001*x := by
    dyadic_interval +kernel [prec := 80]
  convert hm using 1; simp [scalarPartitionFunction,hx.ne',potential,cubicPotential,cubicCoefficient,pow_two]; norm_num

theorem scalar_box_0210 (x : ℝ) (hx : 0<x)
    (hq : scalarOccupation x∈Set.Icc 0.4512930908203125 0.45140673828125) :
    scalarPartitionFunction x<1.001*x := by
  have hc : 1-scalarOccupation x∈Set.Icc (((1123519/2048000) : ℚ) : ℝ) (((4495007/8192000) : ℚ) : ℝ) := by
    norm_num
    constructor <;> linarith [hq.1,hq.2]
  have hlx := logarithm_enclosure (1123519/2048000) (4495007/8192000) (-15009949581/25000000000) (-37511927693/62500000000) (1) (1) 14
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [scaledLogLower,logApproximation,logRemainder,Finset.sum_range_succ])
    (by norm_num [scaledLogUpper,logApproximation,logRemainder,Finset.sum_range_succ])
    (1-scalarOccupation x) (hc)
  have hxi : x∈Set.Icc 0.600190843088 0.60039798324 := by
    have he := occupation_log_identity x
    norm_num at hlx
    constructor <;> linarith [hlx.1,hlx.2]
  have hr := remaining_ratio_bounds ((3696993/8192000)) ((924481/2048000)) ((1567367648339/100000000000)) ((1567367648341/100000000000))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (scalarOccupation x) criticalActivity (by convert hq using 1; norm_num) (by convert criticalActivity_bounds using 1; norm_num)
  have hri : criticalActivity*(1-scalarOccupation x)/scalarOccupation x∈Set.Icc
      (((1760967332894184941/92448100000000000) : ℚ) : ℝ) (((7045328550866333387/369699300000000000) : ℚ) : ℝ) := by
    norm_num at hr ⊢
    exact hr
  have hly := logarithm_enclosure (1760967332894184941/92448100000000000) (7045328550866333387/369699300000000000) (736742788009/250000000000) (2947430086767/1000000000000) (-4) (-4) 14
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [scaledLogLower,logApproximation,logRemainder,Finset.sum_range_succ])
    (by norm_num [scaledLogUpper,logApproximation,logRemainder,Finset.sum_range_succ])
    (criticalActivity*(1-scalarOccupation x)/scalarOccupation x) (hri)
  have hyi : remainingPotential x∈Set.Icc (2.946971152036) (2.947430086767) := by
    rw [remainingPotential_eq_log_div x hx,occupation_remaining_ratio x hx]
    norm_num at hly ⊢
    exact hly
  have hz := cubicCenter_tight_bounds
  have hm : (scalarOccupation x)*(scalarOccupation x)*(remainingPotential x*
      (1+0.016*((remainingPotential x-cubicCenter)*(remainingPotential x-cubicCenter))))<1.001*x := by
    dyadic_interval +kernel [prec := 80]
  convert hm using 1; simp [scalarPartitionFunction,hx.ne',potential,cubicPotential,cubicCoefficient,pow_two]; norm_num

theorem scalar_box_0211 (x : ℝ) (hx : 0<x)
    (hq : scalarOccupation x∈Set.Icc 0.45140673828125 0.4515203857421875) :
    scalarPartitionFunction x<1.001*x := by
  have hc : 1-scalarOccupation x∈Set.Icc (((898629/1638400) : ℚ) : ℝ) (((1123519/2048000) : ℚ) : ℝ) := by
    norm_num
    constructor <;> linarith [hq.1,hq.2]
  have hlx := logarithm_enclosure (898629/1638400) (1123519/2048000) (-600605166307/1000000000000) (-600397983239/1000000000000) (1) (1) 14
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [scaledLogLower,logApproximation,logRemainder,Finset.sum_range_succ])
    (by norm_num [scaledLogUpper,logApproximation,logRemainder,Finset.sum_range_succ])
    (1-scalarOccupation x) (hc)
  have hxi : x∈Set.Icc 0.600397983239 0.600605166307 := by
    have he := occupation_log_identity x
    norm_num at hlx
    constructor <;> linarith [hlx.1,hlx.2]
  have hr := remaining_ratio_bounds ((924481/2048000)) ((739771/1638400)) ((1567367648339/100000000000)) ((1567367648341/100000000000))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (scalarOccupation x) criticalActivity (by convert hq using 1; norm_num) (by convert criticalActivity_bounds using 1; norm_num)
  have hri : criticalActivity*(1-scalarOccupation x)/scalarOccupation x∈Set.Icc
      (((1408482022459227231/73977100000000000) : ℚ) : ℝ) (((1760967332896431979/92448100000000000) : ℚ) : ℝ) := by
    norm_num at hr ⊢
    exact hr
  have hly := logarithm_enclosure (1408482022459227231/73977100000000000) (1760967332896431979/92448100000000000) (117860489511/40000000000) (1473485576019/500000000000) (-4) (-4) 14
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [scaledLogLower,logApproximation,logRemainder,Finset.sum_range_succ])
    (by norm_num [scaledLogUpper,logApproximation,logRemainder,Finset.sum_range_succ])
    (criticalActivity*(1-scalarOccupation x)/scalarOccupation x) (hri)
  have hyi : remainingPotential x∈Set.Icc (2.946512237775) (2.946971152038) := by
    rw [remainingPotential_eq_log_div x hx,occupation_remaining_ratio x hx]
    norm_num at hly ⊢
    exact hly
  have hz := cubicCenter_tight_bounds
  have hm : (scalarOccupation x)*(scalarOccupation x)*(remainingPotential x*
      (1+0.016*((remainingPotential x-cubicCenter)*(remainingPotential x-cubicCenter))))<1.001*x := by
    dyadic_interval +kernel [prec := 80]
  convert hm using 1; simp [scalarPartitionFunction,hx.ne',potential,cubicPotential,cubicCoefficient,pow_two]; norm_num

theorem scalar_box_0212 (x : ℝ) (hx : 0<x)
    (hq : scalarOccupation x∈Set.Icc 0.4515203857421875 0.451634033203125) :
    scalarPartitionFunction x<1.001*x := by
  have hc : 1-scalarOccupation x∈Set.Icc (((2246107/4096000) : ℚ) : ℝ) (((898629/1638400) : ℚ) : ℝ) := by
    norm_num
    constructor <;> linarith [hq.1,hq.2]
  have hlx := logarithm_enclosure (2246107/4096000) (898629/1638400) (-600812392307/1000000000000) (-300302583153/500000000000) (1) (1) 14
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [scaledLogLower,logApproximation,logRemainder,Finset.sum_range_succ])
    (by norm_num [scaledLogUpper,logApproximation,logRemainder,Finset.sum_range_succ])
    (1-scalarOccupation x) (hc)
  have hxi : x∈Set.Icc 0.600605166306 0.600812392307 := by
    have he := occupation_log_identity x
    norm_num at hlx
    constructor <;> linarith [hlx.1,hlx.2]
  have hr := remaining_ratio_bounds ((739771/1638400)) ((1849893/4096000)) ((1567367648339/100000000000)) ((1567367648341/100000000000))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (scalarOccupation x) criticalActivity (by convert hq using 1; norm_num) (by convert criticalActivity_bounds using 1; norm_num)
  have hri : criticalActivity*(1-scalarOccupation x)/scalarOccupation x∈Set.Icc
      (((3520475446507766273/184989300000000000) : ℚ) : ℝ) (((1408482022461024489/73977100000000000) : ℚ) : ℝ) := by
    norm_num at hr ⊢
    exact hr
  have hly := logarithm_enclosure (3520475446507766273/184989300000000000) (1408482022461024489/73977100000000000) (2946053343933/1000000000000) (2946512237777/1000000000000) (-4) (-4) 14
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [scaledLogLower,logApproximation,logRemainder,Finset.sum_range_succ])
    (by norm_num [scaledLogUpper,logApproximation,logRemainder,Finset.sum_range_succ])
    (criticalActivity*(1-scalarOccupation x)/scalarOccupation x) (hri)
  have hyi : remainingPotential x∈Set.Icc (2.946053343933) (2.946512237777) := by
    rw [remainingPotential_eq_log_div x hx,occupation_remaining_ratio x hx]
    norm_num at hly ⊢
    exact hly
  have hz := cubicCenter_tight_bounds
  have hm : (scalarOccupation x)*(scalarOccupation x)*(remainingPotential x*
      (1+0.016*((remainingPotential x-cubicCenter)*(remainingPotential x-cubicCenter))))<1.001*x := by
    dyadic_interval +kernel [prec := 80]
  convert hm using 1; simp [scalarPartitionFunction,hx.ne',potential,cubicPotential,cubicCoefficient,pow_two]; norm_num

theorem scalar_box_0213 (x : ℝ) (hx : 0<x)
    (hq : scalarOccupation x∈Set.Icc 0.451634033203125 0.4517476806640625) :
    scalarPartitionFunction x<1.001*x := by
  have hc : 1-scalarOccupation x∈Set.Icc (((4491283/8192000) : ℚ) : ℝ) (((2246107/4096000) : ℚ) : ℝ) := by
    norm_num
    constructor <;> linarith [hq.1,hq.2]
  have hlx := logarithm_enclosure (4491283/8192000) (2246107/4096000) (-601019661259/1000000000000) (-300406196153/500000000000) (1) (1) 14
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [scaledLogLower,logApproximation,logRemainder,Finset.sum_range_succ])
    (by norm_num [scaledLogUpper,logApproximation,logRemainder,Finset.sum_range_succ])
    (1-scalarOccupation x) (hc)
  have hxi : x∈Set.Icc 0.600812392306 0.601019661259 := by
    have he := occupation_log_identity x
    norm_num at hlx
    constructor <;> linarith [hlx.1,hlx.2]
  have hr := remaining_ratio_bounds ((1849893/4096000)) ((3700717/8192000)) ((1567367648339/100000000000)) ((1567367648341/100000000000))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (scalarOccupation x) criticalActivity (by convert hq using 1; norm_num) (by convert criticalActivity_bounds using 1; norm_num)
  have hri : criticalActivity*(1-scalarOccupation x)/scalarOccupation x∈Set.Icc
      (((7039491673734928937/370071700000000000) : ℚ) : ℝ) (((3520475446512258487/184989300000000000) : ℚ) : ℝ) := by
    norm_num at hr ⊢
    exact hr
  have hly := logarithm_enclosure (7039491673734928937/370071700000000000) (3520475446512258487/184989300000000000) (2945594470461/1000000000000) (46032083499/15625000000) (-4) (-4) 14
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [scaledLogLower,logApproximation,logRemainder,Finset.sum_range_succ])
    (by norm_num [scaledLogUpper,logApproximation,logRemainder,Finset.sum_range_succ])
    (criticalActivity*(1-scalarOccupation x)/scalarOccupation x) (hri)
  have hyi : remainingPotential x∈Set.Icc (2.945594470461) (2.946053343936) := by
    rw [remainingPotential_eq_log_div x hx,occupation_remaining_ratio x hx]
    norm_num at hly ⊢
    exact hly
  have hz := cubicCenter_tight_bounds
  have hm : (scalarOccupation x)*(scalarOccupation x)*(remainingPotential x*
      (1+0.016*((remainingPotential x-cubicCenter)*(remainingPotential x-cubicCenter))))<1.001*x := by
    dyadic_interval +kernel [prec := 80]
  convert hm using 1; simp [scalarPartitionFunction,hx.ne',potential,cubicPotential,cubicCoefficient,pow_two]; norm_num

theorem scalar_box_0214 (x : ℝ) (hx : 0<x)
    (hq : scalarOccupation x∈Set.Icc 0.4517476806640625 0.451861328125) :
    scalarPartitionFunction x<1.001*x := by
  have hc : 1-scalarOccupation x∈Set.Icc (((280647/512000) : ℚ) : ℝ) (((4491283/8192000) : ℚ) : ℝ) := by
    norm_num
    constructor <;> linarith [hq.1,hq.2]
  have hlx := logarithm_enclosure (280647/512000) (4491283/8192000) (-30061348659/50000000000) (-300509830629/500000000000) (1) (1) 14
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [scaledLogLower,logApproximation,logRemainder,Finset.sum_range_succ])
    (by norm_num [scaledLogUpper,logApproximation,logRemainder,Finset.sum_range_succ])
    (1-scalarOccupation x) (hc)
  have hxi : x∈Set.Icc 0.601019661258 0.60122697318 := by
    have he := occupation_log_identity x
    norm_num at hlx
    constructor <;> linarith [hlx.1,hlx.2]
  have hr := remaining_ratio_bounds ((3700717/8192000)) ((231353/512000)) ((1567367648339/100000000000)) ((1567367648341/100000000000))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (scalarOccupation x) criticalActivity (by convert hq using 1; norm_num) (by convert criticalActivity_bounds using 1; norm_num)
  have hri : criticalActivity*(1-scalarOccupation x)/scalarOccupation x∈Set.Icc
      (((439877028403395333/23135300000000000) : ℚ) : ℝ) (((7039491673743911503/370071700000000000) : ℚ) : ℝ) := by
    norm_num at hr ⊢
    exact hr
  have hly := logarithm_enclosure (439877028403395333/23135300000000000) (7039491673743911503/370071700000000000) (736283904327/250000000000) (2945594470463/1000000000000) (-4) (-4) 14
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [scaledLogLower,logApproximation,logRemainder,Finset.sum_range_succ])
    (by norm_num [scaledLogUpper,logApproximation,logRemainder,Finset.sum_range_succ])
    (criticalActivity*(1-scalarOccupation x)/scalarOccupation x) (hri)
  have hyi : remainingPotential x∈Set.Icc (2.945135617308) (2.945594470463) := by
    rw [remainingPotential_eq_log_div x hx,occupation_remaining_ratio x hx]
    norm_num at hly ⊢
    exact hly
  have hz := cubicCenter_tight_bounds
  have hm : (scalarOccupation x)*(scalarOccupation x)*(remainingPotential x*
      (1+0.016*((remainingPotential x-cubicCenter)*(remainingPotential x-cubicCenter))))<1.001*x := by
    dyadic_interval +kernel [prec := 80]
  convert hm using 1; simp [scalarPartitionFunction,hx.ne',potential,cubicPotential,cubicCoefficient,pow_two]; norm_num

theorem scalar_box_0215 (x : ℝ) (hx : 0<x)
    (hq : scalarOccupation x∈Set.Icc 0.451861328125 0.4519749755859375) :
    scalarPartitionFunction x<1.001*x := by
  have hc : 1-scalarOccupation x∈Set.Icc (((4489421/8192000) : ℚ) : ℝ) (((280647/512000) : ℚ) : ℝ) := by
    norm_num
    constructor <;> linarith [hq.1,hq.2]
  have hlx := logarithm_enclosure (4489421/8192000) (280647/512000) (-75179291011/125000000000) (-601226973179/1000000000000) (1) (1) 14
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [scaledLogLower,logApproximation,logRemainder,Finset.sum_range_succ])
    (by norm_num [scaledLogUpper,logApproximation,logRemainder,Finset.sum_range_succ])
    (1-scalarOccupation x) (hc)
  have hxi : x∈Set.Icc 0.601226973179 0.601434328088 := by
    have he := occupation_log_identity x
    norm_num at hlx
    constructor <;> linarith [hlx.1,hlx.2]
  have hr := remaining_ratio_bounds ((231353/512000)) ((3702579/8192000)) ((1567367648339/100000000000)) ((1567367648341/100000000000))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (scalarOccupation x) criticalActivity (by convert hq using 1; norm_num) (by convert criticalActivity_bounds using 1; norm_num)
  have hri : criticalActivity*(1-scalarOccupation x)/scalarOccupation x∈Set.Icc
      (((7036573235173721719/370257900000000000) : ℚ) : ℝ) (((439877028403956627/23135300000000000) : ℚ) : ℝ) := by
    norm_num at hr ⊢
    exact hr
  have hly := logarithm_enclosure (7036573235173721719/370257900000000000) (439877028403956627/23135300000000000) (117787071377/40000000000) (294513561731/100000000000) (-4) (-4) 14
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [scaledLogLower,logApproximation,logRemainder,Finset.sum_range_succ])
    (by norm_num [scaledLogUpper,logApproximation,logRemainder,Finset.sum_range_succ])
    (criticalActivity*(1-scalarOccupation x)/scalarOccupation x) (hri)
  have hyi : remainingPotential x∈Set.Icc (2.944676784425) (2.94513561731) := by
    rw [remainingPotential_eq_log_div x hx,occupation_remaining_ratio x hx]
    norm_num at hly ⊢
    exact hly
  have hz := cubicCenter_tight_bounds
  have hm : (scalarOccupation x)*(scalarOccupation x)*(remainingPotential x*
      (1+0.016*((remainingPotential x-cubicCenter)*(remainingPotential x-cubicCenter))))<1.001*x := by
    dyadic_interval +kernel [prec := 80]
  convert hm using 1; simp [scalarPartitionFunction,hx.ne',potential,cubicPotential,cubicCoefficient,pow_two]; norm_num

theorem scalar_box_0216 (x : ℝ) (hx : 0<x)
    (hq : scalarOccupation x∈Set.Icc 0.4519749755859375 0.452088623046875) :
    scalarPartitionFunction x<1.001*x := by
  have hc : 1-scalarOccupation x∈Set.Icc (((448849/819200) : ℚ) : ℝ) (((4489421/8192000) : ℚ) : ℝ) := by
    norm_num
    constructor <;> linarith [hq.1,hq.2]
  have hlx := logarithm_enclosure (448849/819200) (4489421/8192000) (-601641726001/1000000000000) (-601434328087/1000000000000) (1) (1) 14
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [scaledLogLower,logApproximation,logRemainder,Finset.sum_range_succ])
    (by norm_num [scaledLogUpper,logApproximation,logRemainder,Finset.sum_range_succ])
    (1-scalarOccupation x) (hc)
  have hxi : x∈Set.Icc 0.601434328087 0.601641726001 := by
    have he := occupation_log_identity x
    norm_num at hlx
    constructor <;> linarith [hlx.1,hlx.2]
  have hr := remaining_ratio_bounds ((3702579/8192000)) ((370351/819200)) ((1567367648339/100000000000)) ((1567367648341/100000000000))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (scalarOccupation x) criticalActivity (by convert hq using 1; norm_num) (by convert criticalActivity_bounds using 1; norm_num)
  have hri : criticalActivity*(1-scalarOccupation x)/scalarOccupation x∈Set.Icc
      (((703511401589311811/37035100000000000) : ℚ) : ℝ) (((7036573235182700561/370257900000000000) : ℚ) : ℝ) := by
    norm_num at hr ⊢
    exact hr
  have hly := logarithm_enclosure (703511401589311811/37035100000000000) (7036573235182700561/370257900000000000) (1472108985881/500000000000) (736169196107/250000000000) (-4) (-4) 14
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [scaledLogLower,logApproximation,logRemainder,Finset.sum_range_succ])
    (by norm_num [scaledLogUpper,logApproximation,logRemainder,Finset.sum_range_succ])
    (criticalActivity*(1-scalarOccupation x)/scalarOccupation x) (hri)
  have hyi : remainingPotential x∈Set.Icc (2.944217971762) (2.944676784428) := by
    rw [remainingPotential_eq_log_div x hx,occupation_remaining_ratio x hx]
    norm_num at hly ⊢
    exact hly
  have hz := cubicCenter_tight_bounds
  have hm : (scalarOccupation x)*(scalarOccupation x)*(remainingPotential x*
      (1+0.016*((remainingPotential x-cubicCenter)*(remainingPotential x-cubicCenter))))<1.001*x := by
    dyadic_interval +kernel [prec := 80]
  convert hm using 1; simp [scalarPartitionFunction,hx.ne',potential,cubicPotential,cubicCoefficient,pow_two]; norm_num

theorem scalar_box_0217 (x : ℝ) (hx : 0<x)
    (hq : scalarOccupation x∈Set.Icc 0.452088623046875 0.4522022705078125) :
    scalarPartitionFunction x<1.001*x := by
  have hc : 1-scalarOccupation x∈Set.Icc (((4487559/8192000) : ℚ) : ℝ) (((448849/819200) : ℚ) : ℝ) := by
    norm_num
    constructor <;> linarith [hq.1,hq.2]
  have hlx := logarithm_enclosure (4487559/8192000) (448849/819200) (-601849166937/1000000000000) (-300820863/500000000) (1) (1) 14
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [scaledLogLower,logApproximation,logRemainder,Finset.sum_range_succ])
    (by norm_num [scaledLogUpper,logApproximation,logRemainder,Finset.sum_range_succ])
    (1-scalarOccupation x) (hc)
  have hxi : x∈Set.Icc 0.601641726 0.601849166937 := by
    have he := occupation_log_identity x
    norm_num at hlx
    constructor <;> linarith [hlx.1,hlx.2]
  have hr := remaining_ratio_bounds ((370351/819200)) ((3704441/8192000)) ((1567367648339/100000000000)) ((1567367648341/100000000000))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (scalarOccupation x) criticalActivity (by convert hq using 1; norm_num) (by convert criticalActivity_bounds using 1; norm_num)
  have hri : criticalActivity*(1-scalarOccupation x)/scalarOccupation x∈Set.Icc
      (((7033654796612514501/370444100000000000) : ℚ) : ℝ) (((703511401590209509/37035100000000000) : ℚ) : ℝ) := by
    norm_num at hr ⊢
    exact hr
  have hly := logarithm_enclosure (7033654796612514501/370444100000000000) (703511401590209509/37035100000000000) (2943759179271/1000000000000) (588843594353/200000000000) (-4) (-4) 14
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [scaledLogLower,logApproximation,logRemainder,Finset.sum_range_succ])
    (by norm_num [scaledLogUpper,logApproximation,logRemainder,Finset.sum_range_succ])
    (criticalActivity*(1-scalarOccupation x)/scalarOccupation x) (hri)
  have hyi : remainingPotential x∈Set.Icc (2.943759179271) (2.944217971765) := by
    rw [remainingPotential_eq_log_div x hx,occupation_remaining_ratio x hx]
    norm_num at hly ⊢
    exact hly
  have hz := cubicCenter_tight_bounds
  have hm : (scalarOccupation x)*(scalarOccupation x)*(remainingPotential x*
      (1+0.016*((remainingPotential x-cubicCenter)*(remainingPotential x-cubicCenter))))<1.001*x := by
    dyadic_interval +kernel [prec := 80]
  convert hm using 1; simp [scalarPartitionFunction,hx.ne',potential,cubicPotential,cubicCoefficient,pow_two]; norm_num

theorem scalar_box_0218 (x : ℝ) (hx : 0<x)
    (hq : scalarOccupation x∈Set.Icc 0.4522022705078125 0.45231591796875) :
    scalarPartitionFunction x<1.001*x := by
  have hc : 1-scalarOccupation x∈Set.Icc (((1121657/2048000) : ℚ) : ℝ) (((4487559/8192000) : ℚ) : ℝ) := by
    norm_num
    constructor <;> linarith [hq.1,hq.2]
  have hlx := logarithm_enclosure (1121657/2048000) (4487559/8192000) (-301028325457/500000000000) (-75231145867/125000000000) (1) (1) 14
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [scaledLogLower,logApproximation,logRemainder,Finset.sum_range_succ])
    (by norm_num [scaledLogUpper,logApproximation,logRemainder,Finset.sum_range_succ])
    (1-scalarOccupation x) (hc)
  have hxi : x∈Set.Icc 0.601849166936 0.602056650914 := by
    have he := occupation_log_identity x
    norm_num at hlx
    constructor <;> linarith [hlx.1,hlx.2]
  have hr := remaining_ratio_bounds ((3704441/8192000)) ((926343/2048000)) ((1567367648339/100000000000)) ((1567367648341/100000000000))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (scalarOccupation x) criticalActivity (by convert hq using 1; norm_num) (by convert criticalActivity_bounds using 1; norm_num)
  have hri : criticalActivity*(1-scalarOccupation x)/scalarOccupation x∈Set.Icc
      (((1758048894332977723/92634300000000000) : ℚ) : ℝ) (((7033654796621489619/370444100000000000) : ℚ) : ℝ) := by
    norm_num at hr ⊢
    exact hr
  have hly := logarithm_enclosure (1758048894332977723/92634300000000000) (7033654796621489619/370444100000000000) (29433004069/10000000000) (2943759179273/1000000000000) (-4) (-4) 14
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [scaledLogLower,logApproximation,logRemainder,Finset.sum_range_succ])
    (by norm_num [scaledLogUpper,logApproximation,logRemainder,Finset.sum_range_succ])
    (criticalActivity*(1-scalarOccupation x)/scalarOccupation x) (hri)
  have hyi : remainingPotential x∈Set.Icc (2.9433004069) (2.943759179273) := by
    rw [remainingPotential_eq_log_div x hx,occupation_remaining_ratio x hx]
    norm_num at hly ⊢
    exact hly
  have hz := cubicCenter_tight_bounds
  have hm : (scalarOccupation x)*(scalarOccupation x)*(remainingPotential x*
      (1+0.016*((remainingPotential x-cubicCenter)*(remainingPotential x-cubicCenter))))<1.001*x := by
    dyadic_interval +kernel [prec := 80]
  convert hm using 1; simp [scalarPartitionFunction,hx.ne',potential,cubicPotential,cubicCoefficient,pow_two]; norm_num

theorem scalar_box_0219 (x : ℝ) (hx : 0<x)
    (hq : scalarOccupation x∈Set.Icc 0.45231591796875 0.4524295654296875) :
    scalarPartitionFunction x<1.001*x := by
  have hc : 1-scalarOccupation x∈Set.Icc (((4485697/8192000) : ℚ) : ℝ) (((1121657/2048000) : ℚ) : ℝ) := by
    norm_num
    constructor <;> linarith [hq.1,hq.2]
  have hlx := logarithm_enclosure (4485697/8192000) (1121657/2048000) (-602264177949/1000000000000) (-602056650913/1000000000000) (1) (1) 14
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [scaledLogLower,logApproximation,logRemainder,Finset.sum_range_succ])
    (by norm_num [scaledLogUpper,logApproximation,logRemainder,Finset.sum_range_succ])
    (1-scalarOccupation x) (hc)
  have hxi : x∈Set.Icc 0.602056650913 0.602264177949 := by
    have he := occupation_log_identity x
    norm_num at hlx
    constructor <;> linarith [hlx.1,hlx.2]
  have hr := remaining_ratio_bounds ((926343/2048000)) ((3706303/8192000)) ((1567367648339/100000000000)) ((1567367648341/100000000000))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (scalarOccupation x) criticalActivity (by convert hq using 1; norm_num) (by convert criticalActivity_bounds using 1; norm_num)
  have hri : criticalActivity*(1-scalarOccupation x)/scalarOccupation x∈Set.Icc
      (((7030736358051307283/370630300000000000) : ℚ) : ℝ) (((159822626757747367/8421300000000000) : ℚ) : ℝ) := by
    norm_num at hr ⊢
    exact hr
  have hly := logarithm_enclosure (7030736358051307283/370630300000000000) (159822626757747367/8421300000000000) (14714208273/5000000000) (1471650203451/500000000000) (-4) (-4) 14
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [scaledLogLower,logApproximation,logRemainder,Finset.sum_range_succ])
    (by norm_num [scaledLogUpper,logApproximation,logRemainder,Finset.sum_range_succ])
    (criticalActivity*(1-scalarOccupation x)/scalarOccupation x) (hri)
  have hyi : remainingPotential x∈Set.Icc (2.9428416546) (2.943300406902) := by
    rw [remainingPotential_eq_log_div x hx,occupation_remaining_ratio x hx]
    norm_num at hly ⊢
    exact hly
  have hz := cubicCenter_tight_bounds
  have hm : (scalarOccupation x)*(scalarOccupation x)*(remainingPotential x*
      (1+0.016*((remainingPotential x-cubicCenter)*(remainingPotential x-cubicCenter))))<1.001*x := by
    dyadic_interval +kernel [prec := 80]
  convert hm using 1; simp [scalarPartitionFunction,hx.ne',potential,cubicPotential,cubicCoefficient,pow_two]; norm_num

theorem scalar_box_0220 (x : ℝ) (hx : 0<x)
    (hq : scalarOccupation x∈Set.Icc 0.4524295654296875 0.452543212890625) :
    scalarPartitionFunction x<1.001*x := by
  have hc : 1-scalarOccupation x∈Set.Icc (((2242383/4096000) : ℚ) : ℝ) (((4485697/8192000) : ℚ) : ℝ) := by
    norm_num
    constructor <;> linarith [hq.1,hq.2]
  have hlx := logarithm_enclosure (2242383/4096000) (4485697/8192000) (-602471748061/1000000000000) (-150566044487/250000000000) (1) (1) 14
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [scaledLogLower,logApproximation,logRemainder,Finset.sum_range_succ])
    (by norm_num [scaledLogUpper,logApproximation,logRemainder,Finset.sum_range_succ])
    (1-scalarOccupation x) (hc)
  have hxi : x∈Set.Icc 0.602264177948 0.602471748061 := by
    have he := occupation_log_identity x
    norm_num at hlx
    constructor <;> linarith [hlx.1,hlx.2]
  have hr := remaining_ratio_bounds ((3706303/8192000)) ((1853617/4096000)) ((1567367648339/100000000000)) ((1567367648341/100000000000))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (scalarOccupation x) criticalActivity (by convert hq using 1; norm_num) (by convert criticalActivity_bounds using 1; norm_num)
  have hri : criticalActivity*(1-scalarOccupation x)/scalarOccupation x∈Set.Icc
      (((3514638569385351837/185361700000000000) : ℚ) : ℝ) (((7030736358060278677/370630300000000000) : ℚ) : ℝ) := by
    norm_num at hr ⊢
    exact hr
  have hly := logarithm_enclosure (3514638569385351837/185361700000000000) (7030736358060278677/370630300000000000) (2942382922323/1000000000000) (2942841654603/1000000000000) (-4) (-4) 14
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [scaledLogLower,logApproximation,logRemainder,Finset.sum_range_succ])
    (by norm_num [scaledLogUpper,logApproximation,logRemainder,Finset.sum_range_succ])
    (criticalActivity*(1-scalarOccupation x)/scalarOccupation x) (hri)
  have hyi : remainingPotential x∈Set.Icc (2.942382922323) (2.942841654603) := by
    rw [remainingPotential_eq_log_div x hx,occupation_remaining_ratio x hx]
    norm_num at hly ⊢
    exact hly
  have hz := cubicCenter_tight_bounds
  have hm : (scalarOccupation x)*(scalarOccupation x)*(remainingPotential x*
      (1+0.016*((remainingPotential x-cubicCenter)*(remainingPotential x-cubicCenter))))<1.001*x := by
    dyadic_interval +kernel [prec := 80]
  convert hm using 1; simp [scalarPartitionFunction,hx.ne',potential,cubicPotential,cubicCoefficient,pow_two]; norm_num

theorem scalar_box_0221 (x : ℝ) (hx : 0<x)
    (hq : scalarOccupation x∈Set.Icc 0.452543212890625 0.4526568603515625) :
    scalarPartitionFunction x<1.001*x := by
  have hc : 1-scalarOccupation x∈Set.Icc (((896767/1638400) : ℚ) : ℝ) (((2242383/4096000) : ℚ) : ℝ) := by
    norm_num
    constructor <;> linarith [hq.1,hq.2]
  have hlx := logarithm_enclosure (896767/1638400) (2242383/4096000) (-602679361267/1000000000000) (-30123587403/50000000000) (1) (1) 14
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [scaledLogLower,logApproximation,logRemainder,Finset.sum_range_succ])
    (by norm_num [scaledLogUpper,logApproximation,logRemainder,Finset.sum_range_succ])
    (1-scalarOccupation x) (hc)
  have hxi : x∈Set.Icc 0.60247174806 0.602679361267 := by
    have he := occupation_log_identity x
    norm_num at hlx
    constructor <;> linarith [hlx.1,hlx.2]
  have hr := remaining_ratio_bounds ((1853617/4096000)) ((741633/1638400)) ((1567367648339/100000000000)) ((1567367648341/100000000000))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (scalarOccupation x) criticalActivity (by convert hq using 1; norm_num) (by convert criticalActivity_bounds using 1; norm_num)
  have hri : criticalActivity*(1-scalarOccupation x)/scalarOccupation x∈Set.Icc
      (((1405563583898020013/74163300000000000) : ℚ) : ℝ) (((3514638569389836603/185361700000000000) : ℚ) : ℝ) := by
    norm_num at hr ⊢
    exact hr
  have hly := logarithm_enclosure (1405563583898020013/74163300000000000) (3514638569389836603/185361700000000000) (2941924210017/1000000000000) (117695316893/40000000000) (-4) (-4) 14
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [scaledLogLower,logApproximation,logRemainder,Finset.sum_range_succ])
    (by norm_num [scaledLogUpper,logApproximation,logRemainder,Finset.sum_range_succ])
    (criticalActivity*(1-scalarOccupation x)/scalarOccupation x) (hri)
  have hyi : remainingPotential x∈Set.Icc (2.941924210017) (2.942382922325) := by
    rw [remainingPotential_eq_log_div x hx,occupation_remaining_ratio x hx]
    norm_num at hly ⊢
    exact hly
  have hz := cubicCenter_tight_bounds
  have hm : (scalarOccupation x)*(scalarOccupation x)*(remainingPotential x*
      (1+0.016*((remainingPotential x-cubicCenter)*(remainingPotential x-cubicCenter))))<1.001*x := by
    dyadic_interval +kernel [prec := 80]
  convert hm using 1; simp [scalarPartitionFunction,hx.ne',potential,cubicPotential,cubicCoefficient,pow_two]; norm_num

theorem scalar_box_0222 (x : ℝ) (hx : 0<x)
    (hq : scalarOccupation x∈Set.Icc 0.4526568603515625 0.4527705078125) :
    scalarPartitionFunction x<1.001*x := by
  have hc : 1-scalarOccupation x∈Set.Icc (((560363/1024000) : ℚ) : ℝ) (((896767/1638400) : ℚ) : ℝ) := by
    norm_num
    constructor <;> linarith [hq.1,hq.2]
  have hlx := logarithm_enclosure (560363/1024000) (896767/1638400) (-120577403517/200000000000) (-301339680633/500000000000) (1) (1) 14
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [scaledLogLower,logApproximation,logRemainder,Finset.sum_range_succ])
    (by norm_num [scaledLogUpper,logApproximation,logRemainder,Finset.sum_range_succ])
    (1-scalarOccupation x) (hc)
  have hxi : x∈Set.Icc 0.602679361266 0.602887017585 := by
    have he := occupation_log_identity x
    norm_num at hlx
    constructor <;> linarith [hlx.1,hlx.2]
  have hr := remaining_ratio_bounds ((741633/1638400)) ((463637/1024000)) ((1567367648339/100000000000)) ((1567367648341/100000000000))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (scalarOccupation x) criticalActivity (by convert hq using 1; norm_num) (by convert criticalActivity_bounds using 1; norm_num)
  have hri : criticalActivity*(1-scalarOccupation x)/scalarOccupation x∈Set.Icc
      (((878294837526187057/46363700000000000) : ℚ) : ℝ) (((1405563583899813547/74163300000000000) : ℚ) : ℝ) := by
    norm_num at hr ⊢
    exact hr
  have hly := logarithm_enclosure (878294837526187057/46363700000000000) (1405563583899813547/74163300000000000) (588293103527/200000000000) (147096210501/50000000000) (-4) (-4) 14
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [scaledLogLower,logApproximation,logRemainder,Finset.sum_range_succ])
    (by norm_num [scaledLogUpper,logApproximation,logRemainder,Finset.sum_range_succ])
    (criticalActivity*(1-scalarOccupation x)/scalarOccupation x) (hri)
  have hyi : remainingPotential x∈Set.Icc (2.941465517635) (2.94192421002) := by
    rw [remainingPotential_eq_log_div x hx,occupation_remaining_ratio x hx]
    norm_num at hly ⊢
    exact hly
  have hz := cubicCenter_tight_bounds
  have hm : (scalarOccupation x)*(scalarOccupation x)*(remainingPotential x*
      (1+0.016*((remainingPotential x-cubicCenter)*(remainingPotential x-cubicCenter))))<1.001*x := by
    dyadic_interval +kernel [prec := 80]
  convert hm using 1; simp [scalarPartitionFunction,hx.ne',potential,cubicPotential,cubicCoefficient,pow_two]; norm_num

theorem scalar_box_0223 (x : ℝ) (hx : 0<x)
    (hq : scalarOccupation x∈Set.Icc 0.4527705078125 0.4528841552734375) :
    scalarPartitionFunction x<1.001*x := by
  have hc : 1-scalarOccupation x∈Set.Icc (((4481973/8192000) : ℚ) : ℝ) (((560363/1024000) : ℚ) : ℝ) := by
    norm_num
    constructor <;> linarith [hq.1,hq.2]
  have hlx := logarithm_enclosure (4481973/8192000) (560363/1024000) (-603094717033/1000000000000) (-37680438599/62500000000) (1) (1) 14
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [scaledLogLower,logApproximation,logRemainder,Finset.sum_range_succ])
    (by norm_num [scaledLogUpper,logApproximation,logRemainder,Finset.sum_range_succ])
    (1-scalarOccupation x) (hc)
  have hxi : x∈Set.Icc 0.602887017584 0.603094717033 := by
    have he := occupation_log_identity x
    norm_num at hlx
    constructor <;> linarith [hlx.1,hlx.2]
  have hr := remaining_ratio_bounds ((463637/1024000)) ((3710027/8192000)) ((1567367648339/100000000000)) ((1567367648341/100000000000))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (scalarOccupation x) criticalActivity (by convert hq using 1; norm_num) (by convert criticalActivity_bounds using 1; norm_num)
  have hri : criticalActivity*(1-scalarOccupation x)/scalarOccupation x∈Set.Icc
      (((7024899480928892847/371002700000000000) : ℚ) : ℝ) (((878294837527307783/46363700000000000) : ℚ) : ℝ) := by
    norm_num at hr ⊢
    exact hr
  have hly := logarithm_enclosure (7024899480928892847/371002700000000000) (878294837527307783/46363700000000000) (1470503422563/500000000000) (2941465517637/1000000000000) (-4) (-4) 14
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [scaledLogLower,logApproximation,logRemainder,Finset.sum_range_succ])
    (by norm_num [scaledLogUpper,logApproximation,logRemainder,Finset.sum_range_succ])
    (criticalActivity*(1-scalarOccupation x)/scalarOccupation x) (hri)
  have hyi : remainingPotential x∈Set.Icc (2.941006845126) (2.941465517637) := by
    rw [remainingPotential_eq_log_div x hx,occupation_remaining_ratio x hx]
    norm_num at hly ⊢
    exact hly
  have hz := cubicCenter_tight_bounds
  have hm : (scalarOccupation x)*(scalarOccupation x)*(remainingPotential x*
      (1+0.016*((remainingPotential x-cubicCenter)*(remainingPotential x-cubicCenter))))<1.001*x := by
    dyadic_interval +kernel [prec := 80]
  convert hm using 1; simp [scalarPartitionFunction,hx.ne',potential,cubicPotential,cubicCoefficient,pow_two]; norm_num

end HardCoreActivityThreshold
