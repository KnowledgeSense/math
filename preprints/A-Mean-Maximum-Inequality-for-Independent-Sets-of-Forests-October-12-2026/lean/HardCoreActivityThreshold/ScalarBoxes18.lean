import HardCoreActivityThreshold.ScalarCoordinates

namespace HardCoreActivityThreshold
set_option maxHeartbeats 4000000
set_option maxRecDepth 8192

theorem scalar_box_0288 (x : ℝ) (hx : 0<x)
    (hq : scalarOccupation x∈Set.Icc 0.4601575927734375 0.460271240234375) :
    scalarPartitionFunction x<1.001*x := by
  have hc : 1-scalarOccupation x∈Set.Icc (((2210729/4096000) : ℚ) : ℝ) (((4422389/8192000) : ℚ) : ℝ) := by
    norm_num
    constructor <;> linarith [hq.1,hq.2]
  have hlx := logarithm_enclosure (2210729/4096000) (4422389/8192000) (-154172140587/250000000000) (-308239010243/500000000000) (1) (1) 14
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [scaledLogLower,logApproximation,logRemainder,Finset.sum_range_succ])
    (by norm_num [scaledLogUpper,logApproximation,logRemainder,Finset.sum_range_succ])
    (1-scalarOccupation x) (hc)
  have hxi : x∈Set.Icc 0.616478020486 0.616688562348 := by
    have he := occupation_log_identity x
    norm_num at hlx
    constructor <;> linarith [hlx.1,hlx.2]
  have hr := remaining_ratio_bounds ((3769611/8192000)) ((1885271/4096000)) ((1567367648339/100000000000)) ((1567367648341/100000000000))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (scalarOccupation x) criticalActivity (by convert hq using 1; norm_num) (by convert criticalActivity_bounds using 1; norm_num)
  have hri : criticalActivity*(1-scalarOccupation x)/scalarOccupation x∈Set.Icc
      (((3465025113844829131/188527100000000000) : ℚ) : ℝ) (((6931509446979106649/376961100000000000) : ℚ) : ℝ) := by
    norm_num at hr ⊢
    exact hr
  have hly := logarithm_enclosure (3465025113844829131/188527100000000000) (6931509446979106649/376961100000000000) (2911233396327/1000000000000) (2911690882783/1000000000000) (-4) (-4) 14
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [scaledLogLower,logApproximation,logRemainder,Finset.sum_range_succ])
    (by norm_num [scaledLogUpper,logApproximation,logRemainder,Finset.sum_range_succ])
    (criticalActivity*(1-scalarOccupation x)/scalarOccupation x) (hri)
  have hyi : remainingPotential x∈Set.Icc (2.911233396327) (2.911690882783) := by
    rw [remainingPotential_eq_log_div x hx,occupation_remaining_ratio x hx]
    norm_num at hly ⊢
    exact hly
  have hz := cubicCenter_tight_bounds
  have hm : (scalarOccupation x)*(scalarOccupation x)*(remainingPotential x*
      (1+0.016*((remainingPotential x-cubicCenter)*(remainingPotential x-cubicCenter))))<1.001*x := by
    dyadic_interval +kernel [prec := 80]
  convert hm using 1; simp [scalarPartitionFunction,hx.ne',potential,cubicPotential,cubicCoefficient,pow_two]; norm_num

theorem scalar_box_0289 (x : ℝ) (hx : 0<x)
    (hq : scalarOccupation x∈Set.Icc 0.460271240234375 0.4603848876953125) :
    scalarPartitionFunction x<1.001*x := by
  have hc : 1-scalarOccupation x∈Set.Icc (((4420527/8192000) : ℚ) : ℝ) (((2210729/4096000) : ℚ) : ℝ) := by
    norm_num
    constructor <;> linarith [hq.1,hq.2]
  have hlx := logarithm_enclosure (4420527/8192000) (2210729/4096000) (-308449574273/500000000000) (-616688562347/1000000000000) (1) (1) 14
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [scaledLogLower,logApproximation,logRemainder,Finset.sum_range_succ])
    (by norm_num [scaledLogUpper,logApproximation,logRemainder,Finset.sum_range_succ])
    (1-scalarOccupation x) (hc)
  have hxi : x∈Set.Icc 0.616688562347 0.616899148546 := by
    have he := occupation_log_identity x
    norm_num at hlx
    constructor <;> linarith [hlx.1,hlx.2]
  have hr := remaining_ratio_bounds ((1885271/4096000)) ((3771473/8192000)) ((1567367648339/100000000000)) ((1567367648341/100000000000))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (scalarOccupation x) criticalActivity (by convert hq using 1; norm_num) (by convert criticalActivity_bounds using 1; norm_num)
  have hri : criticalActivity*(1-scalarOccupation x)/scalarOccupation x∈Set.Icc
      (((6928591008409054653/377147300000000000) : ℚ) : ℝ) (((3465025113849250589/188527100000000000) : ℚ) : ℝ) := by
    norm_num at hr ⊢
    exact hr
  have hly := logarithm_enclosure (6928591008409054653/377147300000000000) (3465025113849250589/188527100000000000) (2910775926503/1000000000000) (291123339633/100000000000) (-4) (-4) 14
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [scaledLogLower,logApproximation,logRemainder,Finset.sum_range_succ])
    (by norm_num [scaledLogUpper,logApproximation,logRemainder,Finset.sum_range_succ])
    (criticalActivity*(1-scalarOccupation x)/scalarOccupation x) (hri)
  have hyi : remainingPotential x∈Set.Icc (2.910775926503) (2.91123339633) := by
    rw [remainingPotential_eq_log_div x hx,occupation_remaining_ratio x hx]
    norm_num at hly ⊢
    exact hly
  have hz := cubicCenter_tight_bounds
  have hm : (scalarOccupation x)*(scalarOccupation x)*(remainingPotential x*
      (1+0.016*((remainingPotential x-cubicCenter)*(remainingPotential x-cubicCenter))))<1.001*x := by
    dyadic_interval +kernel [prec := 80]
  convert hm using 1; simp [scalarPartitionFunction,hx.ne',potential,cubicPotential,cubicCoefficient,pow_two]; norm_num

theorem scalar_box_0290 (x : ℝ) (hx : 0<x)
    (hq : scalarOccupation x∈Set.Icc 0.4603848876953125 0.46049853515625) :
    scalarPartitionFunction x<1.001*x := by
  have hc : 1-scalarOccupation x∈Set.Icc (((1104899/2048000) : ℚ) : ℝ) (((4420527/8192000) : ℚ) : ℝ) := by
    norm_num
    constructor <;> linarith [hq.1,hq.2]
  have hlx := logarithm_enclosure (1104899/2048000) (4420527/8192000) (-6171097791/10000000000) (-123379829709/200000000000) (1) (1) 14
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [scaledLogLower,logApproximation,logRemainder,Finset.sum_range_succ])
    (by norm_num [scaledLogUpper,logApproximation,logRemainder,Finset.sum_range_succ])
    (1-scalarOccupation x) (hc)
  have hxi : x∈Set.Icc 0.616899148545 0.6171097791 := by
    have he := occupation_log_identity x
    norm_num at hlx
    constructor <;> linarith [hlx.1,hlx.2]
  have hr := remaining_ratio_bounds ((3771473/8192000)) ((943101/2048000)) ((1567367648339/100000000000)) ((1567367648341/100000000000))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (scalarOccupation x) criticalActivity (by convert hq using 1; norm_num) (by convert criticalActivity_bounds using 1; norm_num)
  have hri : criticalActivity*(1-scalarOccupation x)/scalarOccupation x∈Set.Icc
      (((1731782947282112761/94310100000000000) : ℚ) : ℝ) (((6928591008417895707/377147300000000000) : ℚ) : ℝ) := by
    norm_num at hr ⊢
    exact hr
  have hly := logarithm_enclosure (1731782947282112761/94310100000000000) (6928591008417895707/377147300000000000) (2910318473259/1000000000000) (582155185301/200000000000) (-4) (-4) 14
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [scaledLogLower,logApproximation,logRemainder,Finset.sum_range_succ])
    (by norm_num [scaledLogUpper,logApproximation,logRemainder,Finset.sum_range_succ])
    (criticalActivity*(1-scalarOccupation x)/scalarOccupation x) (hri)
  have hyi : remainingPotential x∈Set.Icc (2.910318473259) (2.910775926505) := by
    rw [remainingPotential_eq_log_div x hx,occupation_remaining_ratio x hx]
    norm_num at hly ⊢
    exact hly
  have hz := cubicCenter_tight_bounds
  have hm : (scalarOccupation x)*(scalarOccupation x)*(remainingPotential x*
      (1+0.016*((remainingPotential x-cubicCenter)*(remainingPotential x-cubicCenter))))<1.001*x := by
    dyadic_interval +kernel [prec := 80]
  convert hm using 1; simp [scalarPartitionFunction,hx.ne',potential,cubicPotential,cubicCoefficient,pow_two]; norm_num

theorem scalar_box_0291 (x : ℝ) (hx : 0<x)
    (hq : scalarOccupation x∈Set.Icc 0.46049853515625 0.4606121826171875) :
    scalarPartitionFunction x<1.001*x := by
  have hc : 1-scalarOccupation x∈Set.Icc (((883733/1638400) : ℚ) : ℝ) (((1104899/2048000) : ℚ) : ℝ) := by
    norm_num
    constructor <;> linarith [hq.1,hq.2]
  have hlx := logarithm_enclosure (883733/1638400) (1104899/2048000) (-617320454029/1000000000000) (-617109779099/1000000000000) (1) (1) 14
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [scaledLogLower,logApproximation,logRemainder,Finset.sum_range_succ])
    (by norm_num [scaledLogUpper,logApproximation,logRemainder,Finset.sum_range_succ])
    (1-scalarOccupation x) (hc)
  have hxi : x∈Set.Icc 0.617109779099 0.617320454029 := by
    have he := occupation_log_identity x
    norm_num at hlx
    constructor <;> linarith [hlx.1,hlx.2]
  have hr := remaining_ratio_bounds ((943101/2048000)) ((754667/1638400)) ((1567367648339/100000000000)) ((1567367648341/100000000000))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (scalarOccupation x) criticalActivity (by convert hq using 1; norm_num) (by convert criticalActivity_bounds using 1; norm_num)
  have hri : criticalActivity*(1-scalarOccupation x)/scalarOccupation x∈Set.Icc
      (((1385134513969569487/75466700000000000) : ℚ) : ℝ) (((1731782947284322559/94310100000000000) : ℚ) : ℝ) := by
    norm_num at hr ⊢
    exact hr
  have hly := logarithm_enclosure (1385134513969569487/75466700000000000) (1731782947284322559/94310100000000000) (727465259137/250000000000) (1455159236631/500000000000) (-4) (-4) 14
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [scaledLogLower,logApproximation,logRemainder,Finset.sum_range_succ])
    (by norm_num [scaledLogUpper,logApproximation,logRemainder,Finset.sum_range_succ])
    (criticalActivity*(1-scalarOccupation x)/scalarOccupation x) (hri)
  have hyi : remainingPotential x∈Set.Icc (2.909861036548) (2.910318473262) := by
    rw [remainingPotential_eq_log_div x hx,occupation_remaining_ratio x hx]
    norm_num at hly ⊢
    exact hly
  have hz := cubicCenter_tight_bounds
  have hm : (scalarOccupation x)*(scalarOccupation x)*(remainingPotential x*
      (1+0.016*((remainingPotential x-cubicCenter)*(remainingPotential x-cubicCenter))))<1.001*x := by
    dyadic_interval +kernel [prec := 80]
  convert hm using 1; simp [scalarPartitionFunction,hx.ne',potential,cubicPotential,cubicCoefficient,pow_two]; norm_num

theorem scalar_box_0292 (x : ℝ) (hx : 0<x)
    (hq : scalarOccupation x∈Set.Icc 0.4606121826171875 0.460725830078125) :
    scalarPartitionFunction x<1.001*x := by
  have hc : 1-scalarOccupation x∈Set.Icc (((2208867/4096000) : ℚ) : ℝ) (((883733/1638400) : ℚ) : ℝ) := by
    norm_num
    constructor <;> linarith [hq.1,hq.2]
  have hlx := logarithm_enclosure (2208867/4096000) (883733/1638400) (-617531173351/1000000000000) (-154330113507/250000000000) (1) (1) 14
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [scaledLogLower,logApproximation,logRemainder,Finset.sum_range_succ])
    (by norm_num [scaledLogUpper,logApproximation,logRemainder,Finset.sum_range_succ])
    (1-scalarOccupation x) (hc)
  have hxi : x∈Set.Icc 0.617320454028 0.617531173351 := by
    have he := occupation_log_identity x
    norm_num at hlx
    constructor <;> linarith [hlx.1,hlx.2]
  have hr := remaining_ratio_bounds ((754667/1638400)) ((1887133/4096000)) ((1567367648339/100000000000)) ((1567367648341/100000000000))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (scalarOccupation x) criticalActivity (by convert hq using 1; norm_num) (by convert criticalActivity_bounds using 1; norm_num)
  have hri : criticalActivity*(1-scalarOccupation x)/scalarOccupation x∈Set.Icc
      (((3462106675283621913/188713300000000000) : ℚ) : ℝ) (((26134613471157301/1423900000000000) : ℚ) : ℝ) := by
    norm_num at hr ⊢
    exact hr
  have hly := logarithm_enclosure (3462106675283621913/188713300000000000) (26134613471157301/1423900000000000) (2909403616319/1000000000000) (58197220731/20000000000) (-4) (-4) 14
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [scaledLogLower,logApproximation,logRemainder,Finset.sum_range_succ])
    (by norm_num [scaledLogUpper,logApproximation,logRemainder,Finset.sum_range_succ])
    (criticalActivity*(1-scalarOccupation x)/scalarOccupation x) (hri)
  have hyi : remainingPotential x∈Set.Icc (2.909403616319) (2.90986103655) := by
    rw [remainingPotential_eq_log_div x hx,occupation_remaining_ratio x hx]
    norm_num at hly ⊢
    exact hly
  have hz := cubicCenter_tight_bounds
  have hm : (scalarOccupation x)*(scalarOccupation x)*(remainingPotential x*
      (1+0.016*((remainingPotential x-cubicCenter)*(remainingPotential x-cubicCenter))))<1.001*x := by
    dyadic_interval +kernel [prec := 80]
  convert hm using 1; simp [scalarPartitionFunction,hx.ne',potential,cubicPotential,cubicCoefficient,pow_two]; norm_num

theorem scalar_box_0293 (x : ℝ) (hx : 0<x)
    (hq : scalarOccupation x∈Set.Icc 0.460725830078125 0.4608394775390625) :
    scalarPartitionFunction x<1.001*x := by
  have hc : 1-scalarOccupation x∈Set.Icc (((4416803/8192000) : ℚ) : ℝ) (((2208867/4096000) : ℚ) : ℝ) := by
    norm_num
    constructor <;> linarith [hq.1,hq.2]
  have hlx := logarithm_enclosure (4416803/8192000) (2208867/4096000) (-123548387417/200000000000) (-12350623467/20000000000) (1) (1) 14
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [scaledLogLower,logApproximation,logRemainder,Finset.sum_range_succ])
    (by norm_num [scaledLogUpper,logApproximation,logRemainder,Finset.sum_range_succ])
    (1-scalarOccupation x) (hc)
  have hxi : x∈Set.Icc 0.61753117335 0.617741937085 := by
    have he := occupation_log_identity x
    norm_num at hlx
    constructor <;> linarith [hlx.1,hlx.2]
  have hr := remaining_ratio_bounds ((1887133/4096000)) ((3775197/8192000)) ((1567367648339/100000000000)) ((1567367648341/100000000000))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (scalarOccupation x) criticalActivity (by convert hq using 1; norm_num) (by convert criticalActivity_bounds using 1; norm_num)
  have hri : criticalActivity*(1-scalarOccupation x)/scalarOccupation x∈Set.Icc
      (((300989310055940879/16413900000000000) : ℚ) : ℝ) (((3462106675288039647/188713300000000000) : ℚ) : ℝ) := by
    norm_num at hr ⊢
    exact hr
  have hly := logarithm_enclosure (300989310055940879/16413900000000000) (3462106675288039647/188713300000000000) (116357848501/40000000000) (2909403616321/1000000000000) (-4) (-4) 14
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [scaledLogLower,logApproximation,logRemainder,Finset.sum_range_succ])
    (by norm_num [scaledLogUpper,logApproximation,logRemainder,Finset.sum_range_succ])
    (criticalActivity*(1-scalarOccupation x)/scalarOccupation x) (hri)
  have hyi : remainingPotential x∈Set.Icc (2.908946212525) (2.909403616321) := by
    rw [remainingPotential_eq_log_div x hx,occupation_remaining_ratio x hx]
    norm_num at hly ⊢
    exact hly
  have hz := cubicCenter_tight_bounds
  have hm : (scalarOccupation x)*(scalarOccupation x)*(remainingPotential x*
      (1+0.016*((remainingPotential x-cubicCenter)*(remainingPotential x-cubicCenter))))<1.001*x := by
    dyadic_interval +kernel [prec := 80]
  convert hm using 1; simp [scalarPartitionFunction,hx.ne',potential,cubicPotential,cubicCoefficient,pow_two]; norm_num

theorem scalar_box_0294 (x : ℝ) (hx : 0<x)
    (hq : scalarOccupation x∈Set.Icc 0.4608394775390625 0.460953125) :
    scalarPartitionFunction x<1.001*x := by
  have hc : 1-scalarOccupation x∈Set.Icc (((34499/64000) : ℚ) : ℝ) (((4416803/8192000) : ℚ) : ℝ) := by
    norm_num
    constructor <;> linarith [hq.1,hq.2]
  have hlx := logarithm_enclosure (34499/64000) (4416803/8192000) (-2471810981/4000000000) (-154435484271/250000000000) (1) (1) 14
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [scaledLogLower,logApproximation,logRemainder,Finset.sum_range_succ])
    (by norm_num [scaledLogUpper,logApproximation,logRemainder,Finset.sum_range_succ])
    (1-scalarOccupation x) (hc)
  have hxi : x∈Set.Icc 0.617741937084 0.61795274525 := by
    have he := occupation_log_identity x
    norm_num at hlx
    constructor <;> linarith [hlx.1,hlx.2]
  have hr := remaining_ratio_bounds ((3775197/8192000)) ((29501/64000)) ((1567367648339/100000000000)) ((1567367648341/100000000000))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (scalarOccupation x) criticalActivity (by convert hq using 1; norm_num) (by convert criticalActivity_bounds using 1; norm_num)
  have hri : criticalActivity*(1-scalarOccupation x)/scalarOccupation x∈Set.Icc
      (((54072616500047161/2950100000000000) : ℚ) : ℝ) (((6922754131295473823/377519700000000000) : ℚ) : ℝ) := by
    norm_num at hr ⊢
    exact hr
  have hly := logarithm_enclosure (54072616500047161/2950100000000000) (6922754131295473823/377519700000000000) (727122206279/250000000000) (2908946212527/1000000000000) (-4) (-4) 14
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [scaledLogLower,logApproximation,logRemainder,Finset.sum_range_succ])
    (by norm_num [scaledLogUpper,logApproximation,logRemainder,Finset.sum_range_succ])
    (criticalActivity*(1-scalarOccupation x)/scalarOccupation x) (hri)
  have hyi : remainingPotential x∈Set.Icc (2.908488825116) (2.908946212527) := by
    rw [remainingPotential_eq_log_div x hx,occupation_remaining_ratio x hx]
    norm_num at hly ⊢
    exact hly
  have hz := cubicCenter_tight_bounds
  have hm : (scalarOccupation x)*(scalarOccupation x)*(remainingPotential x*
      (1+0.016*((remainingPotential x-cubicCenter)*(remainingPotential x-cubicCenter))))<1.001*x := by
    dyadic_interval +kernel [prec := 80]
  convert hm using 1; simp [scalarPartitionFunction,hx.ne',potential,cubicPotential,cubicCoefficient,pow_two]; norm_num

theorem scalar_box_0295 (x : ℝ) (hx : 0<x)
    (hq : scalarOccupation x∈Set.Icc 0.460953125 0.4610667724609375) :
    scalarPartitionFunction x<1.001*x := by
  have hc : 1-scalarOccupation x∈Set.Icc (((4414941/8192000) : ℚ) : ℝ) (((34499/64000) : ℚ) : ℝ) := by
    norm_num
    constructor <;> linarith [hq.1,hq.2]
  have hlx := logarithm_enclosure (4414941/8192000) (34499/64000) (-77270449733/125000000000) (-617952745249/1000000000000) (1) (1) 14
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [scaledLogLower,logApproximation,logRemainder,Finset.sum_range_succ])
    (by norm_num [scaledLogUpper,logApproximation,logRemainder,Finset.sum_range_succ])
    (1-scalarOccupation x) (hc)
  have hxi : x∈Set.Icc 0.617952745249 0.618163597864 := by
    have he := occupation_log_identity x
    norm_num at hlx
    constructor <;> linarith [hlx.1,hlx.2]
  have hr := remaining_ratio_bounds ((29501/64000)) ((3777059/8192000)) ((1567367648339/100000000000)) ((1567367648341/100000000000))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (scalarOccupation x) criticalActivity (by convert hq using 1; norm_num) (by convert criticalActivity_bounds using 1; norm_num)
  have hri : criticalActivity*(1-scalarOccupation x)/scalarOccupation x∈Set.Icc
      (((6919835692725432999/377705900000000000) : ℚ) : ℝ) (((54072616500116159/2950100000000000) : ℚ) : ℝ) := by
    norm_num at hr ⊢
    exact hr
  have hly := logarithm_enclosure (6919835692725432999/377705900000000000) (54072616500116159/2950100000000000) (727007863511/250000000000) (1454244412559/500000000000) (-4) (-4) 14
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [scaledLogLower,logApproximation,logRemainder,Finset.sum_range_succ])
    (by norm_num [scaledLogUpper,logApproximation,logRemainder,Finset.sum_range_succ])
    (criticalActivity*(1-scalarOccupation x)/scalarOccupation x) (hri)
  have hyi : remainingPotential x∈Set.Icc (2.908031454044) (2.908488825118) := by
    rw [remainingPotential_eq_log_div x hx,occupation_remaining_ratio x hx]
    norm_num at hly ⊢
    exact hly
  have hz := cubicCenter_tight_bounds
  have hm : (scalarOccupation x)*(scalarOccupation x)*(remainingPotential x*
      (1+0.016*((remainingPotential x-cubicCenter)*(remainingPotential x-cubicCenter))))<1.001*x := by
    dyadic_interval +kernel [prec := 80]
  convert hm using 1; simp [scalarPartitionFunction,hx.ne',potential,cubicPotential,cubicCoefficient,pow_two]; norm_num

theorem scalar_box_0296 (x : ℝ) (hx : 0<x)
    (hq : scalarOccupation x∈Set.Icc 0.4610667724609375 0.461180419921875) :
    scalarPartitionFunction x<1.001*x := by
  have hc : 1-scalarOccupation x∈Set.Icc (((441401/819200) : ℚ) : ℝ) (((4414941/8192000) : ℚ) : ℝ) := by
    norm_num
    constructor <;> linarith [hq.1,hq.2]
  have hlx := logarithm_enclosure (441401/819200) (4414941/8192000) (-618374494947/1000000000000) (-618163597863/1000000000000) (1) (1) 14
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [scaledLogLower,logApproximation,logRemainder,Finset.sum_range_succ])
    (by norm_num [scaledLogUpper,logApproximation,logRemainder,Finset.sum_range_succ])
    (1-scalarOccupation x) (hc)
  have hxi : x∈Set.Icc 0.618163597863 0.618374494947 := by
    have he := occupation_log_identity x
    norm_num at hlx
    constructor <;> linarith [hlx.1,hlx.2]
  have hr := remaining_ratio_bounds ((3777059/8192000)) ((377799/819200)) ((1567367648339/100000000000)) ((1567367648341/100000000000))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (scalarOccupation x) criticalActivity (by convert hq using 1; norm_num) (by convert criticalActivity_bounds using 1; norm_num)
  have hri : criticalActivity*(1-scalarOccupation x)/scalarOccupation x∈Set.Icc
      (((691837647344482939/37779900000000000) : ℚ) : ℝ) (((629075972066751171/34336900000000000) : ℚ) : ℝ) := by
    norm_num at hr ⊢
    exact hr
  have hly := logarithm_enclosure (691837647344482939/37779900000000000) (629075972066751171/34336900000000000) (145378704963/50000000000) (1454015727023/500000000000) (-4) (-4) 14
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [scaledLogLower,logApproximation,logRemainder,Finset.sum_range_succ])
    (by norm_num [scaledLogUpper,logApproximation,logRemainder,Finset.sum_range_succ])
    (criticalActivity*(1-scalarOccupation x)/scalarOccupation x) (hri)
  have hyi : remainingPotential x∈Set.Icc (2.90757409926) (2.908031454046) := by
    rw [remainingPotential_eq_log_div x hx,occupation_remaining_ratio x hx]
    norm_num at hly ⊢
    exact hly
  have hz := cubicCenter_tight_bounds
  have hm : (scalarOccupation x)*(scalarOccupation x)*(remainingPotential x*
      (1+0.016*((remainingPotential x-cubicCenter)*(remainingPotential x-cubicCenter))))<1.001*x := by
    dyadic_interval +kernel [prec := 80]
  convert hm using 1; simp [scalarPartitionFunction,hx.ne',potential,cubicPotential,cubicCoefficient,pow_two]; norm_num

theorem scalar_box_0297 (x : ℝ) (hx : 0<x)
    (hq : scalarOccupation x∈Set.Icc 0.461180419921875 0.4612940673828125) :
    scalarPartitionFunction x<1.001*x := by
  have hc : 1-scalarOccupation x∈Set.Icc (((4413079/8192000) : ℚ) : ℝ) (((441401/819200) : ℚ) : ℝ) := by
    norm_num
    constructor <;> linarith [hq.1,hq.2]
  have hlx := logarithm_enclosure (4413079/8192000) (441401/819200) (-154646359129/250000000000) (-309187247473/500000000000) (1) (1) 14
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [scaledLogLower,logApproximation,logRemainder,Finset.sum_range_succ])
    (by norm_num [scaledLogUpper,logApproximation,logRemainder,Finset.sum_range_succ])
    (1-scalarOccupation x) (hc)
  have hxi : x∈Set.Icc 0.618374494946 0.618585436516 := by
    have he := occupation_log_identity x
    norm_num at hlx
    constructor <;> linarith [hlx.1,hlx.2]
  have hr := remaining_ratio_bounds ((377799/819200)) ((3778921/8192000)) ((1567367648339/100000000000)) ((1567367648341/100000000000))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (scalarOccupation x) criticalActivity (by convert hq using 1; norm_num) (by convert criticalActivity_bounds using 1; norm_num)
  have hri : criticalActivity*(1-scalarOccupation x)/scalarOccupation x∈Set.Icc
      (((6916917254164225781/377892100000000000) : ℚ) : ℝ) (((691837647345365741/37779900000000000) : ℚ) : ℝ) := by
    norm_num at hr ⊢
    exact hr
  have hly := logarithm_enclosure (6916917254164225781/377892100000000000) (691837647345365741/37779900000000000) (726779190179/250000000000) (2907574099263/1000000000000) (-4) (-4) 14
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [scaledLogLower,logApproximation,logRemainder,Finset.sum_range_succ])
    (by norm_num [scaledLogUpper,logApproximation,logRemainder,Finset.sum_range_succ])
    (criticalActivity*(1-scalarOccupation x)/scalarOccupation x) (hri)
  have hyi : remainingPotential x∈Set.Icc (2.907116760716) (2.907574099263) := by
    rw [remainingPotential_eq_log_div x hx,occupation_remaining_ratio x hx]
    norm_num at hly ⊢
    exact hly
  have hz := cubicCenter_tight_bounds
  have hm : (scalarOccupation x)*(scalarOccupation x)*(remainingPotential x*
      (1+0.016*((remainingPotential x-cubicCenter)*(remainingPotential x-cubicCenter))))<1.001*x := by
    dyadic_interval +kernel [prec := 80]
  convert hm using 1; simp [scalarPartitionFunction,hx.ne',potential,cubicPotential,cubicCoefficient,pow_two]; norm_num

theorem scalar_box_0298 (x : ℝ) (hx : 0<x)
    (hq : scalarOccupation x∈Set.Icc 0.4612940673828125 0.46140771484375) :
    scalarPartitionFunction x<1.001*x := by
  have hc : 1-scalarOccupation x∈Set.Icc (((1103037/2048000) : ℚ) : ℝ) (((4413079/8192000) : ℚ) : ℝ) := by
    norm_num
    constructor <;> linarith [hq.1,hq.2]
  have hlx := logarithm_enclosure (1103037/2048000) (4413079/8192000) (-618796422591/1000000000000) (-123717087303/200000000000) (1) (1) 14
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [scaledLogLower,logApproximation,logRemainder,Finset.sum_range_succ])
    (by norm_num [scaledLogUpper,logApproximation,logRemainder,Finset.sum_range_succ])
    (1-scalarOccupation x) (hc)
  have hxi : x∈Set.Icc 0.618585436515 0.618796422591 := by
    have he := occupation_log_identity x
    norm_num at hlx
    constructor <;> linarith [hlx.1,hlx.2]
  have hr := remaining_ratio_bounds ((3778921/8192000)) ((944963/2048000)) ((1567367648339/100000000000)) ((1567367648341/100000000000))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (scalarOccupation x) criticalActivity (by convert hq using 1; norm_num) (by convert criticalActivity_bounds using 1; norm_num)
  have hri : criticalActivity*(1-scalarOccupation x)/scalarOccupation x∈Set.Icc
      (((1728864508720905543/94496300000000000) : ℚ) : ℝ) (((186943709572244647/10213300000000000) : ℚ) : ℝ) := by
    norm_num at hr ⊢
    exact hr
  have hly := logarithm_enclosure (1728864508720905543/94496300000000000) (186943709572244647/10213300000000000) (2906659438363/1000000000000) (1453558380359/500000000000) (-4) (-4) 14
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [scaledLogLower,logApproximation,logRemainder,Finset.sum_range_succ])
    (by norm_num [scaledLogUpper,logApproximation,logRemainder,Finset.sum_range_succ])
    (criticalActivity*(1-scalarOccupation x)/scalarOccupation x) (hri)
  have hyi : remainingPotential x∈Set.Icc (2.906659438363) (2.907116760718) := by
    rw [remainingPotential_eq_log_div x hx,occupation_remaining_ratio x hx]
    norm_num at hly ⊢
    exact hly
  have hz := cubicCenter_tight_bounds
  have hm : (scalarOccupation x)*(scalarOccupation x)*(remainingPotential x*
      (1+0.016*((remainingPotential x-cubicCenter)*(remainingPotential x-cubicCenter))))<1.001*x := by
    dyadic_interval +kernel [prec := 80]
  convert hm using 1; simp [scalarPartitionFunction,hx.ne',potential,cubicPotential,cubicCoefficient,pow_two]; norm_num

theorem scalar_box_0299 (x : ℝ) (hx : 0<x)
    (hq : scalarOccupation x∈Set.Icc 0.46140771484375 0.4615213623046875) :
    scalarPartitionFunction x<1.001*x := by
  have hc : 1-scalarOccupation x∈Set.Icc (((4411217/8192000) : ℚ) : ℝ) (((1103037/2048000) : ℚ) : ℝ) := by
    norm_num
    constructor <;> linarith [hq.1,hq.2]
  have hlx := logarithm_enclosure (4411217/8192000) (1103037/2048000) (-619007453191/1000000000000) (-61879642259/100000000000) (1) (1) 14
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [scaledLogLower,logApproximation,logRemainder,Finset.sum_range_succ])
    (by norm_num [scaledLogUpper,logApproximation,logRemainder,Finset.sum_range_succ])
    (1-scalarOccupation x) (hc)
  have hxi : x∈Set.Icc 0.61879642259 0.619007453191 := by
    have he := occupation_log_identity x
    norm_num at hlx
    constructor <;> linarith [hlx.1,hlx.2]
  have hr := remaining_ratio_bounds ((944963/2048000)) ((3780783/8192000)) ((1567367648339/100000000000)) ((1567367648341/100000000000))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (scalarOccupation x) criticalActivity (by convert hq using 1; norm_num) (by convert criticalActivity_bounds using 1; norm_num)
  have hri : criticalActivity*(1-scalarOccupation x)/scalarOccupation x∈Set.Icc
      (((6913998815603018563/378078300000000000) : ℚ) : ℝ) (((1728864508723111617/94496300000000000) : ℚ) : ℝ) := by
    norm_num at hr ⊢
    exact hr
  have hly := logarithm_enclosure (6913998815603018563/378078300000000000) (1728864508723111617/94496300000000000) (2906202132151/1000000000000) (581331887673/200000000000) (-4) (-4) 14
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [scaledLogLower,logApproximation,logRemainder,Finset.sum_range_succ])
    (by norm_num [scaledLogUpper,logApproximation,logRemainder,Finset.sum_range_succ])
    (criticalActivity*(1-scalarOccupation x)/scalarOccupation x) (hri)
  have hyi : remainingPotential x∈Set.Icc (2.906202132151) (2.906659438365) := by
    rw [remainingPotential_eq_log_div x hx,occupation_remaining_ratio x hx]
    norm_num at hly ⊢
    exact hly
  have hz := cubicCenter_tight_bounds
  have hm : (scalarOccupation x)*(scalarOccupation x)*(remainingPotential x*
      (1+0.016*((remainingPotential x-cubicCenter)*(remainingPotential x-cubicCenter))))<1.001*x := by
    dyadic_interval +kernel [prec := 80]
  convert hm using 1; simp [scalarPartitionFunction,hx.ne',potential,cubicPotential,cubicCoefficient,pow_two]; norm_num

theorem scalar_box_0300 (x : ℝ) (hx : 0<x)
    (hq : scalarOccupation x∈Set.Icc 0.4615213623046875 0.461635009765625) :
    scalarPartitionFunction x<1.001*x := by
  have hc : 1-scalarOccupation x∈Set.Icc (((2205143/4096000) : ℚ) : ℝ) (((4411217/8192000) : ℚ) : ℝ) := by
    norm_num
    constructor <;> linarith [hq.1,hq.2]
  have hlx := logarithm_enclosure (2205143/4096000) (4411217/8192000) (-309609264167/500000000000) (-61900745319/100000000000) (1) (1) 14
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [scaledLogLower,logApproximation,logRemainder,Finset.sum_range_succ])
    (by norm_num [scaledLogUpper,logApproximation,logRemainder,Finset.sum_range_succ])
    (1-scalarOccupation x) (hc)
  have hxi : x∈Set.Icc 0.61900745319 0.619218528334 := by
    have he := occupation_log_identity x
    norm_num at hlx
    constructor <;> linarith [hlx.1,hlx.2]
  have hr := remaining_ratio_bounds ((3780783/8192000)) ((1890857/4096000)) ((1567367648339/100000000000)) ((1567367648341/100000000000))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (scalarOccupation x) criticalActivity (by convert hq using 1; norm_num) (by convert criticalActivity_bounds using 1; norm_num)
  have hri : criticalActivity*(1-scalarOccupation x)/scalarOccupation x∈Set.Icc
      (((73537655280025691/4023100000000000) : ℚ) : ℝ) (((6913998815611840997/378078300000000000) : ℚ) : ℝ) := by
    norm_num at hr ⊢
    exact hr
  have hly := logarithm_enclosure (73537655280025691/4023100000000000) (6913998815611840997/378078300000000000) (2905744842033/1000000000000) (1453101066077/500000000000) (-4) (-4) 14
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [scaledLogLower,logApproximation,logRemainder,Finset.sum_range_succ])
    (by norm_num [scaledLogUpper,logApproximation,logRemainder,Finset.sum_range_succ])
    (criticalActivity*(1-scalarOccupation x)/scalarOccupation x) (hri)
  have hyi : remainingPotential x∈Set.Icc (2.905744842033) (2.906202132154) := by
    rw [remainingPotential_eq_log_div x hx,occupation_remaining_ratio x hx]
    norm_num at hly ⊢
    exact hly
  have hz := cubicCenter_tight_bounds
  have hm : (scalarOccupation x)*(scalarOccupation x)*(remainingPotential x*
      (1+0.016*((remainingPotential x-cubicCenter)*(remainingPotential x-cubicCenter))))<1.001*x := by
    dyadic_interval +kernel [prec := 80]
  convert hm using 1; simp [scalarPartitionFunction,hx.ne',potential,cubicPotential,cubicCoefficient,pow_two]; norm_num

theorem scalar_box_0301 (x : ℝ) (hx : 0<x)
    (hq : scalarOccupation x∈Set.Icc 0.461635009765625 0.4617486572265625) :
    scalarPartitionFunction x<1.001*x := by
  have hc : 1-scalarOccupation x∈Set.Icc (((881871/1638400) : ℚ) : ℝ) (((2205143/4096000) : ℚ) : ℝ) := by
    norm_num
    constructor <;> linarith [hq.1,hq.2]
  have hlx := logarithm_enclosure (881871/1638400) (2205143/4096000) (-619429648039/1000000000000) (-619218528333/1000000000000) (1) (1) 14
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [scaledLogLower,logApproximation,logRemainder,Finset.sum_range_succ])
    (by norm_num [scaledLogUpper,logApproximation,logRemainder,Finset.sum_range_succ])
    (1-scalarOccupation x) (hc)
  have hxi : x∈Set.Icc 0.619218528333 0.619429648039 := by
    have he := occupation_log_identity x
    norm_num at hlx
    constructor <;> linarith [hlx.1,hlx.2]
  have hr := remaining_ratio_bounds ((1890857/4096000)) ((756529/1638400)) ((1567367648339/100000000000)) ((1567367648341/100000000000))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (scalarOccupation x) criticalActivity (by convert hq using 1; norm_num) (by convert criticalActivity_bounds using 1; norm_num)
  have hri : criticalActivity*(1-scalarOccupation x)/scalarOccupation x∈Set.Icc
      (((1382216075408362269/75652900000000000) : ℚ) : ℝ) (((3456269798165617763/189085700000000000) : ℚ) : ℝ) := by
    norm_num at hr ⊢
    exact hr
  have hly := logarithm_enclosure (1382216075408362269/75652900000000000) (3456269798165617763/189085700000000000) (72632189199/25000000000) (726436210509/250000000000) (-4) (-4) 14
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [scaledLogLower,logApproximation,logRemainder,Finset.sum_range_succ])
    (by norm_num [scaledLogUpper,logApproximation,logRemainder,Finset.sum_range_succ])
    (criticalActivity*(1-scalarOccupation x)/scalarOccupation x) (hri)
  have hyi : remainingPotential x∈Set.Icc (2.90528756796) (2.905744842036) := by
    rw [remainingPotential_eq_log_div x hx,occupation_remaining_ratio x hx]
    norm_num at hly ⊢
    exact hly
  have hz := cubicCenter_tight_bounds
  have hm : (scalarOccupation x)*(scalarOccupation x)*(remainingPotential x*
      (1+0.016*((remainingPotential x-cubicCenter)*(remainingPotential x-cubicCenter))))<1.001*x := by
    dyadic_interval +kernel [prec := 80]
  convert hm using 1; simp [scalarPartitionFunction,hx.ne',potential,cubicPotential,cubicCoefficient,pow_two]; norm_num

theorem scalar_box_0302 (x : ℝ) (hx : 0<x)
    (hq : scalarOccupation x∈Set.Icc 0.4617486572265625 0.4618623046875) :
    scalarPartitionFunction x<1.001*x := by
  have hc : 1-scalarOccupation x∈Set.Icc (((551053/1024000) : ℚ) : ℝ) (((881871/1638400) : ℚ) : ℝ) := by
    norm_num
    constructor <;> linarith [hq.1,hq.2]
  have hlx := logarithm_enclosure (551053/1024000) (881871/1638400) (-24785632493/40000000000) (-309714824019/500000000000) (1) (1) 14
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [scaledLogLower,logApproximation,logRemainder,Finset.sum_range_succ])
    (by norm_num [scaledLogUpper,logApproximation,logRemainder,Finset.sum_range_succ])
    (1-scalarOccupation x) (hc)
  have hxi : x∈Set.Icc 0.619429648038 0.619640812325 := by
    have he := occupation_log_identity x
    norm_num at hlx
    constructor <;> linarith [hlx.1,hlx.2]
  have hr := remaining_ratio_bounds ((756529/1638400)) ((472947/1024000)) ((1567367648339/100000000000)) ((1567367648341/100000000000))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (scalarOccupation x) criticalActivity (by convert hq using 1; norm_num) (by convert criticalActivity_bounds using 1; norm_num)
  have hri : criticalActivity*(1-scalarOccupation x)/scalarOccupation x∈Set.Icc
      (((863702644720150967/47294700000000000) : ℚ) : ℝ) (((1382216075410126011/75652900000000000) : ℚ) : ℝ) := by
    norm_num at hr ⊢
    exact hr
  have hly := logarithm_enclosure (863702644720150967/47294700000000000) (1382216075410126011/75652900000000000) (2904830309883/1000000000000) (2905287567963/1000000000000) (-4) (-4) 14
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [scaledLogLower,logApproximation,logRemainder,Finset.sum_range_succ])
    (by norm_num [scaledLogUpper,logApproximation,logRemainder,Finset.sum_range_succ])
    (criticalActivity*(1-scalarOccupation x)/scalarOccupation x) (hri)
  have hyi : remainingPotential x∈Set.Icc (2.904830309883) (2.905287567963) := by
    rw [remainingPotential_eq_log_div x hx,occupation_remaining_ratio x hx]
    norm_num at hly ⊢
    exact hly
  have hz := cubicCenter_tight_bounds
  have hm : (scalarOccupation x)*(scalarOccupation x)*(remainingPotential x*
      (1+0.016*((remainingPotential x-cubicCenter)*(remainingPotential x-cubicCenter))))<1.001*x := by
    dyadic_interval +kernel [prec := 80]
  convert hm using 1; simp [scalarPartitionFunction,hx.ne',potential,cubicPotential,cubicCoefficient,pow_two]; norm_num

theorem scalar_box_0303 (x : ℝ) (hx : 0<x)
    (hq : scalarOccupation x∈Set.Icc 0.4618623046875 0.4619759521484375) :
    scalarPartitionFunction x<1.001*x := by
  have hc : 1-scalarOccupation x∈Set.Icc (((4407493/8192000) : ℚ) : ℝ) (((551053/1024000) : ℚ) : ℝ) := by
    norm_num
    constructor <;> linarith [hq.1,hq.2]
  have hlx := logarithm_enclosure (4407493/8192000) (551053/1024000) (-619852021211/1000000000000) (-154910203081/250000000000) (1) (1) 14
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [scaledLogLower,logApproximation,logRemainder,Finset.sum_range_succ])
    (by norm_num [scaledLogUpper,logApproximation,logRemainder,Finset.sum_range_succ])
    (1-scalarOccupation x) (hc)
  have hxi : x∈Set.Icc 0.619640812324 0.619852021211 := by
    have he := occupation_log_identity x
    norm_num at hlx
    constructor <;> linarith [hlx.1,hlx.2]
  have hr := remaining_ratio_bounds ((472947/1024000)) ((3784507/8192000)) ((1567367648339/100000000000)) ((1567367648341/100000000000))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (scalarOccupation x) criticalActivity (by convert hq using 1; norm_num) (by convert criticalActivity_bounds using 1; norm_num)
  have hri : criticalActivity*(1-scalarOccupation x)/scalarOccupation x∈Set.Icc
      (((6908161938480604127/378450700000000000) : ℚ) : ℝ) (((863702644721253073/47294700000000000) : ℚ) : ℝ) := by
    norm_num at hr ⊢
    exact hr
  have hly := logarithm_enclosure (6908161938480604127/378450700000000000) (863702644721253073/47294700000000000) (1452186533877/500000000000) (1452415154943/500000000000) (-4) (-4) 14
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [scaledLogLower,logApproximation,logRemainder,Finset.sum_range_succ])
    (by norm_num [scaledLogUpper,logApproximation,logRemainder,Finset.sum_range_succ])
    (criticalActivity*(1-scalarOccupation x)/scalarOccupation x) (hri)
  have hyi : remainingPotential x∈Set.Icc (2.904373067754) (2.904830309886) := by
    rw [remainingPotential_eq_log_div x hx,occupation_remaining_ratio x hx]
    norm_num at hly ⊢
    exact hly
  have hz := cubicCenter_tight_bounds
  have hm : (scalarOccupation x)*(scalarOccupation x)*(remainingPotential x*
      (1+0.016*((remainingPotential x-cubicCenter)*(remainingPotential x-cubicCenter))))<1.001*x := by
    dyadic_interval +kernel [prec := 80]
  convert hm using 1; simp [scalarPartitionFunction,hx.ne',potential,cubicPotential,cubicCoefficient,pow_two]; norm_num

end HardCoreActivityThreshold
