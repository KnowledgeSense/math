import HardCoreActivityThreshold.ScalarCoordinates

namespace HardCoreActivityThreshold
set_option maxHeartbeats 4000000
set_option maxRecDepth 8192

theorem scalar_box_0480 (x : ℝ) (hx : 0<x)
    (hq : scalarOccupation x∈Set.Icc 0.404453125 0.406) :
    scalarPartitionFunction x<1*x := by
  have hc : 1-scalarOccupation x∈Set.Icc (((297/500) : ℚ) : ℝ) (((7623/12800) : ℚ) : ℝ) := by
    norm_num
    constructor <;> linarith [hq.1,hq.2]
  have hlx := logarithm_enclosure (297/500) (7623/12800) (-26043797981/50000000000) (-518275177919/1000000000000) (1) (1) 14
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [scaledLogLower,logApproximation,logRemainder,Finset.sum_range_succ])
    (by norm_num [scaledLogUpper,logApproximation,logRemainder,Finset.sum_range_succ])
    (1-scalarOccupation x) (hc)
  have hxi : x∈Set.Icc 0.518275177919 0.52087595962 := by
    have he := occupation_log_identity x
    norm_num at hlx
    constructor <;> linarith [hlx.1,hlx.2]
  have hr := remaining_ratio_bounds ((5177/12800)) ((203/500)) ((1567367648339/100000000000)) ((1567367648341/100000000000))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (scalarOccupation x) criticalActivity (by convert hq using 1; norm_num) (by convert criticalActivity_bounds using 1; norm_num)
  have hri : criticalActivity*(1-scalarOccupation x)/scalarOccupation x∈Set.Icc
      (((465508191556683/20300000000000) : ℚ) : ℝ) (((11948043583303443/517700000000000) : ℚ) : ℝ) := by
    norm_num at hr ⊢
    exact hr
  have hly := logarithm_enclosure (465508191556683/20300000000000) (11948043583303443/517700000000000) (3132508807843/1000000000000) (3138926903171/1000000000000) (-4) (-4) 14
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [scaledLogLower,logApproximation,logRemainder,Finset.sum_range_succ])
    (by norm_num [scaledLogUpper,logApproximation,logRemainder,Finset.sum_range_succ])
    (criticalActivity*(1-scalarOccupation x)/scalarOccupation x) (hri)
  have hyi : remainingPotential x∈Set.Icc (3.132508807843) (3.138926903171) := by
    rw [remainingPotential_eq_log_div x hx,occupation_remaining_ratio x hx]
    norm_num at hly ⊢
    exact hly
  have hz := cubicCenter_tight_bounds
  have hm : (scalarOccupation x)*(scalarOccupation x)*(remainingPotential x*
      (1+0.016*((remainingPotential x-cubicCenter)*(remainingPotential x-cubicCenter))))<1*x := by
    dyadic_interval +kernel [prec := 80]
  convert hm using 1; simp [scalarPartitionFunction,hx.ne',potential,cubicPotential,cubicCoefficient,pow_two]; norm_num

theorem scalar_box_0481 (x : ℝ) (hx : 0<x)
    (hq : scalarOccupation x∈Set.Icc 0.4647 0.4647145355224609375) :
    scalarPartitionFunction x<1*x := by
  have hc : 1-scalarOccupation x∈Set.Icc (((175402341/327680000) : ℚ) : ℝ) (((5353/10000) : ℚ) : ℝ) := by
    norm_num
    constructor <;> linarith [hq.1,hq.2]
  have hlx := logarithm_enclosure (175402341/327680000) (5353/10000) (-312477547963/500000000000) (-312463970791/500000000000) (1) (1) 14
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [scaledLogLower,logApproximation,logRemainder,Finset.sum_range_succ])
    (by norm_num [scaledLogUpper,logApproximation,logRemainder,Finset.sum_range_succ])
    (1-scalarOccupation x) (hc)
  have hxi : x∈Set.Icc 0.624927941582 0.624955095926 := by
    have he := occupation_log_identity x
    norm_num at hlx
    constructor <;> linarith [hlx.1,hlx.2]
  have hr := remaining_ratio_bounds ((4647/10000)) ((152277659/327680000)) ((1567367648339/100000000000)) ((1567367648341/100000000000))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (scalarOccupation x) criticalActivity (by convert hq using 1; norm_num) (by convert criticalActivity_bounds using 1; norm_num)
  have hri : criticalActivity*(1-scalarOccupation x)/scalarOccupation x∈Set.Icc
      (((274919954726325361599/15227765900000000000) : ℚ) : ℝ) (((8390119021569373/464700000000000) : ℚ) : ℝ) := by
    norm_num at hr ⊢
    exact hr
  have hly := logarithm_enclosure (274919954726325361599/15227765900000000000) (8390119021569373/464700000000000) (361669939521/125000000000) (2893417949393/1000000000000) (-4) (-4) 14
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [scaledLogLower,logApproximation,logRemainder,Finset.sum_range_succ])
    (by norm_num [scaledLogUpper,logApproximation,logRemainder,Finset.sum_range_succ])
    (criticalActivity*(1-scalarOccupation x)/scalarOccupation x) (hri)
  have hyi : remainingPotential x∈Set.Icc (2.893359516168) (2.893417949393) := by
    rw [remainingPotential_eq_log_div x hx,occupation_remaining_ratio x hx]
    norm_num at hly ⊢
    exact hly
  have hz := cubicCenter_tight_bounds
  have hm : (scalarOccupation x)*(scalarOccupation x)*(remainingPotential x*
      (1+0.016*((remainingPotential x-cubicCenter)*(remainingPotential x-cubicCenter))))<1*x := by
    dyadic_interval +kernel [prec := 80]
  convert hm using 1; simp [scalarPartitionFunction,hx.ne',potential,cubicPotential,cubicCoefficient,pow_two]; norm_num

theorem scalar_box_0482 (x : ℝ) (hx : 0<x)
    (hq : scalarOccupation x∈Set.Icc 0.4647145355224609375 0.464729071044921875) :
    scalarPartitionFunction x<1*x := by
  have hc : 1-scalarOccupation x∈Set.Icc (((87698789/163840000) : ℚ) : ℝ) (((175402341/327680000) : ℚ) : ℝ) := by
    norm_num
    constructor <;> linarith [hq.1,hq.2]
  have hlx := logarithm_enclosure (87698789/163840000) (175402341/327680000) (-624982251007/1000000000000) (-24998203837/40000000000) (1) (1) 14
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [scaledLogLower,logApproximation,logRemainder,Finset.sum_range_succ])
    (by norm_num [scaledLogUpper,logApproximation,logRemainder,Finset.sum_range_succ])
    (1-scalarOccupation x) (hc)
  have hxi : x∈Set.Icc 0.624955095925 0.624982251007 := by
    have he := occupation_log_identity x
    norm_num at hlx
    constructor <;> linarith [hlx.1,hlx.2]
  have hr := remaining_ratio_bounds ((152277659/327680000)) ((76141211/163840000)) ((1567367648339/100000000000)) ((1567367648341/100000000000))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (scalarOccupation x) criticalActivity (by convert hq using 1; norm_num) (by convert criticalActivity_bounds using 1; norm_num)
  have hri : criticalActivity*(1-scalarOccupation x)/scalarOccupation x∈Set.Icc
      (((137456244677108161471/7614121100000000000) : ℚ) : ℝ) (((274919954726676166281/15227765900000000000) : ℚ) : ℝ) := by
    norm_num at hr ⊢
    exact hr
  have hly := logarithm_enclosure (137456244677108161471/7614121100000000000) (274919954726676166281/15227765900000000000) (2893301083187/1000000000000) (2893359516171/1000000000000) (-4) (-4) 14
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [scaledLogLower,logApproximation,logRemainder,Finset.sum_range_succ])
    (by norm_num [scaledLogUpper,logApproximation,logRemainder,Finset.sum_range_succ])
    (criticalActivity*(1-scalarOccupation x)/scalarOccupation x) (hri)
  have hyi : remainingPotential x∈Set.Icc (2.893301083187) (2.893359516171) := by
    rw [remainingPotential_eq_log_div x hx,occupation_remaining_ratio x hx]
    norm_num at hly ⊢
    exact hly
  have hz := cubicCenter_tight_bounds
  have hm : (scalarOccupation x)*(scalarOccupation x)*(remainingPotential x*
      (1+0.016*((remainingPotential x-cubicCenter)*(remainingPotential x-cubicCenter))))<1*x := by
    dyadic_interval +kernel [prec := 80]
  convert hm using 1; simp [scalarPartitionFunction,hx.ne',potential,cubicPotential,cubicCoefficient,pow_two]; norm_num

theorem scalar_box_0483 (x : ℝ) (hx : 0<x)
    (hq : scalarOccupation x∈Set.Icc 0.464729071044921875 0.4647436065673828125) :
    scalarPartitionFunction x<1*x := by
  have hc : 1-scalarOccupation x∈Set.Icc (((35078563/65536000) : ℚ) : ℝ) (((87698789/163840000) : ℚ) : ℝ) := by
    norm_num
    constructor <;> linarith [hq.1,hq.2]
  have hlx := logarithm_enclosure (35078563/65536000) (87698789/163840000) (-25000376273/40000000000) (-312491125503/500000000000) (1) (1) 14
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [scaledLogLower,logApproximation,logRemainder,Finset.sum_range_succ])
    (by norm_num [scaledLogUpper,logApproximation,logRemainder,Finset.sum_range_succ])
    (1-scalarOccupation x) (hc)
  have hxi : x∈Set.Icc 0.624982251006 0.625009406825 := by
    have he := occupation_log_identity x
    norm_num at hlx
    constructor <;> linarith [hlx.1,hlx.2]
  have hr := remaining_ratio_bounds ((76141211/163840000)) ((30457437/65536000)) ((1567367648339/100000000000)) ((1567367648341/100000000000))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (scalarOccupation x) criticalActivity (by convert hq using 1; norm_num) (by convert criticalActivity_bounds using 1; norm_num)
  have hri : criticalActivity*(1-scalarOccupation x)/scalarOccupation x∈Set.Icc
      (((54981004796421456857/3045743700000000000) : ℚ) : ℝ) (((137456244677283559049/7614121100000000000) : ℚ) : ℝ) := by
    norm_num at hr ⊢
    exact hr
  have hly := logarithm_enclosure (54981004796421456857/3045743700000000000) (137456244677283559049/7614121100000000000) (2893242650447/1000000000000) (289330108319/100000000000) (-4) (-4) 14
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [scaledLogLower,logApproximation,logRemainder,Finset.sum_range_succ])
    (by norm_num [scaledLogUpper,logApproximation,logRemainder,Finset.sum_range_succ])
    (criticalActivity*(1-scalarOccupation x)/scalarOccupation x) (hri)
  have hyi : remainingPotential x∈Set.Icc (2.893242650447) (2.89330108319) := by
    rw [remainingPotential_eq_log_div x hx,occupation_remaining_ratio x hx]
    norm_num at hly ⊢
    exact hly
  have hz := cubicCenter_tight_bounds
  have hm : (scalarOccupation x)*(scalarOccupation x)*(remainingPotential x*
      (1+0.016*((remainingPotential x-cubicCenter)*(remainingPotential x-cubicCenter))))<1*x := by
    dyadic_interval +kernel [prec := 80]
  convert hm using 1; simp [scalarPartitionFunction,hx.ne',potential,cubicPotential,cubicCoefficient,pow_two]; norm_num

theorem scalar_box_0484 (x : ℝ) (hx : 0<x)
    (hq : scalarOccupation x∈Set.Icc 0.4647436065673828125 0.46475814208984375) :
    scalarPartitionFunction x<1*x := by
  have hc : 1-scalarOccupation x∈Set.Icc (((43847013/81920000) : ℚ) : ℝ) (((35078563/65536000) : ℚ) : ℝ) := by
    norm_num
    constructor <;> linarith [hq.1,hq.2]
  have hlx := logarithm_enclosure (43847013/81920000) (35078563/65536000) (-31251828169/50000000000) (-78126175853/125000000000) (1) (1) 14
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [scaledLogLower,logApproximation,logRemainder,Finset.sum_range_succ])
    (by norm_num [scaledLogUpper,logApproximation,logRemainder,Finset.sum_range_succ])
    (1-scalarOccupation x) (hc)
  have hxi : x∈Set.Icc 0.625009406824 0.62503656338 := by
    have he := occupation_log_identity x
    norm_num at hlx
    constructor <;> linarith [hlx.1,hlx.2]
  have hr := remaining_ratio_bounds ((30457437/65536000)) ((38072987/81920000)) ((1567367648339/100000000000)) ((1567367648341/100000000000))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (scalarOccupation x) criticalActivity (by convert hq using 1; norm_num) (by convert criticalActivity_bounds using 1; norm_num)
  have hri : criticalActivity*(1-scalarOccupation x)/scalarOccupation x∈Set.Icc
      (((68724389652499561407/3807298700000000000) : ℚ) : ℝ) (((54981004796491613983/3045743700000000000) : ℚ) : ℝ) := by
    norm_num at hr ⊢
    exact hr
  have hly := logarithm_enclosure (68724389652499561407/3807298700000000000) (54981004796491613983/3045743700000000000) (2893184217947/1000000000000) (2893242650449/1000000000000) (-4) (-4) 14
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [scaledLogLower,logApproximation,logRemainder,Finset.sum_range_succ])
    (by norm_num [scaledLogUpper,logApproximation,logRemainder,Finset.sum_range_succ])
    (criticalActivity*(1-scalarOccupation x)/scalarOccupation x) (hri)
  have hyi : remainingPotential x∈Set.Icc (2.893184217947) (2.893242650449) := by
    rw [remainingPotential_eq_log_div x hx,occupation_remaining_ratio x hx]
    norm_num at hly ⊢
    exact hly
  have hz := cubicCenter_tight_bounds
  have hm : (scalarOccupation x)*(scalarOccupation x)*(remainingPotential x*
      (1+0.016*((remainingPotential x-cubicCenter)*(remainingPotential x-cubicCenter))))<1*x := by
    dyadic_interval +kernel [prec := 80]
  convert hm using 1; simp [scalarPartitionFunction,hx.ne',potential,cubicPotential,cubicCoefficient,pow_two]; norm_num

theorem scalar_box_0485 (x : ℝ) (hx : 0<x)
    (hq : scalarOccupation x∈Set.Icc 0.46475814208984375 0.4647726776123046875) :
    scalarPartitionFunction x<1*x := by
  have hc : 1-scalarOccupation x∈Set.Icc (((175383289/327680000) : ℚ) : ℝ) (((43847013/81920000) : ℚ) : ℝ) := by
    norm_num
    constructor <;> linarith [hq.1,hq.2]
  have hlx := logarithm_enclosure (175383289/327680000) (43847013/81920000) (-625063720673/1000000000000) (-625036563379/1000000000000) (1) (1) 14
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [scaledLogLower,logApproximation,logRemainder,Finset.sum_range_succ])
    (by norm_num [scaledLogUpper,logApproximation,logRemainder,Finset.sum_range_succ])
    (1-scalarOccupation x) (hc)
  have hxi : x∈Set.Icc 0.625036563379 0.625063720673 := by
    have he := occupation_log_identity x
    norm_num at hlx
    constructor <;> linarith [hlx.1,hlx.2]
  have hr := remaining_ratio_bounds ((38072987/81920000)) ((152296711/327680000)) ((1567367648339/100000000000)) ((1567367648341/100000000000))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (scalarOccupation x) criticalActivity (by convert hq using 1; norm_num) (by convert criticalActivity_bounds using 1; norm_num)
  have hri : criticalActivity*(1-scalarOccupation x)/scalarOccupation x∈Set.Icc
      (((274890093237889206971/15229671100000000000) : ℚ) : ℝ) (((68724389652587255433/3807298700000000000) : ℚ) : ℝ) := by
    norm_num at hr ⊢
    exact hr
  have hly := logarithm_enclosure (274890093237889206971/15229671100000000000) (68724389652587255433/3807298700000000000) (361640723211/125000000000) (57863684359/20000000000) (-4) (-4) 14
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [scaledLogLower,logApproximation,logRemainder,Finset.sum_range_succ])
    (by norm_num [scaledLogUpper,logApproximation,logRemainder,Finset.sum_range_succ])
    (criticalActivity*(1-scalarOccupation x)/scalarOccupation x) (hri)
  have hyi : remainingPotential x∈Set.Icc (2.893125785688) (2.89318421795) := by
    rw [remainingPotential_eq_log_div x hx,occupation_remaining_ratio x hx]
    norm_num at hly ⊢
    exact hly
  have hz := cubicCenter_tight_bounds
  have hm : (scalarOccupation x)*(scalarOccupation x)*(remainingPotential x*
      (1+0.016*((remainingPotential x-cubicCenter)*(remainingPotential x-cubicCenter))))<1*x := by
    dyadic_interval +kernel [prec := 80]
  convert hm using 1; simp [scalarPartitionFunction,hx.ne',potential,cubicPotential,cubicCoefficient,pow_two]; norm_num

theorem scalar_box_0486 (x : ℝ) (hx : 0<x)
    (hq : scalarOccupation x∈Set.Icc 0.4647726776123046875 0.464787213134765625) :
    scalarPartitionFunction x<1*x := by
  have hc : 1-scalarOccupation x∈Set.Icc (((87689263/163840000) : ℚ) : ℝ) (((175383289/327680000) : ℚ) : ℝ) := by
    norm_num
    constructor <;> linarith [hq.1,hq.2]
  have hlx := logarithm_enclosure (87689263/163840000) (175383289/327680000) (-625090878703/1000000000000) (-19533241271/31250000000) (1) (1) 14
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [scaledLogLower,logApproximation,logRemainder,Finset.sum_range_succ])
    (by norm_num [scaledLogUpper,logApproximation,logRemainder,Finset.sum_range_succ])
    (1-scalarOccupation x) (hc)
  have hxi : x∈Set.Icc 0.625063720672 0.625090878703 := by
    have he := occupation_log_identity x
    norm_num at hlx
    constructor <;> linarith [hlx.1,hlx.2]
  have hr := remaining_ratio_bounds ((152296711/327680000)) ((76150737/163840000)) ((1567367648339/100000000000)) ((1567367648341/100000000000))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (scalarOccupation x) criticalActivity (by convert hq using 1; norm_num) (by convert criticalActivity_bounds using 1; norm_num)
  have hri : criticalActivity*(1-scalarOccupation x)/scalarOccupation x∈Set.Icc
      (((137441313932890084157/7615073700000000000) : ℚ) : ℝ) (((274890093238239973549/15229671100000000000) : ℚ) : ℝ) := by
    norm_num at hr ⊢
    exact hr
  have hly := logarithm_enclosure (137441313932890084157/7615073700000000000) (274890093238239973549/15229671100000000000) (289306735367/100000000000) (2893125785691/1000000000000) (-4) (-4) 14
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [scaledLogLower,logApproximation,logRemainder,Finset.sum_range_succ])
    (by norm_num [scaledLogUpper,logApproximation,logRemainder,Finset.sum_range_succ])
    (criticalActivity*(1-scalarOccupation x)/scalarOccupation x) (hri)
  have hyi : remainingPotential x∈Set.Icc (2.89306735367) (2.893125785691) := by
    rw [remainingPotential_eq_log_div x hx,occupation_remaining_ratio x hx]
    norm_num at hly ⊢
    exact hly
  have hz := cubicCenter_tight_bounds
  have hm : (scalarOccupation x)*(scalarOccupation x)*(remainingPotential x*
      (1+0.016*((remainingPotential x-cubicCenter)*(remainingPotential x-cubicCenter))))<1*x := by
    dyadic_interval +kernel [prec := 80]
  convert hm using 1; simp [scalarPartitionFunction,hx.ne',potential,cubicPotential,cubicCoefficient,pow_two]; norm_num

theorem scalar_box_0487 (x : ℝ) (hx : 0<x)
    (hq : scalarOccupation x∈Set.Icc 0.464787213134765625 0.4648017486572265625) :
    scalarPartitionFunction x<1*x := by
  have hc : 1-scalarOccupation x∈Set.Icc (((175373763/327680000) : ℚ) : ℝ) (((87689263/163840000) : ℚ) : ℝ) := by
    norm_num
    constructor <;> linarith [hq.1,hq.2]
  have hlx := logarithm_enclosure (175373763/327680000) (87689263/163840000) (-625118037471/1000000000000) (-312545439351/500000000000) (1) (1) 14
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [scaledLogLower,logApproximation,logRemainder,Finset.sum_range_succ])
    (by norm_num [scaledLogUpper,logApproximation,logRemainder,Finset.sum_range_succ])
    (1-scalarOccupation x) (hc)
  have hxi : x∈Set.Icc 0.625090878702 0.625118037471 := by
    have he := occupation_log_identity x
    norm_num at hlx
    constructor <;> linarith [hlx.1,hlx.2]
  have hr := remaining_ratio_bounds ((76150737/163840000)) ((152306237/327680000)) ((1567367648339/100000000000)) ((1567367648341/100000000000))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (scalarOccupation x) criticalActivity (by convert hq using 1; norm_num) (by convert criticalActivity_bounds using 1; norm_num)
  have hri : criticalActivity*(1-scalarOccupation x)/scalarOccupation x∈Set.Icc
      (((274875162493671129657/15230623700000000000) : ℚ) : ℝ) (((137441313933065462683/7615073700000000000) : ℚ) : ℝ) := by
    norm_num at hr ⊢
    exact hr
  have hly := logarithm_enclosure (274875162493671129657/15230623700000000000) (137441313933065462683/7615073700000000000) (723252230473/250000000000) (2893067353673/1000000000000) (-4) (-4) 14
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [scaledLogLower,logApproximation,logRemainder,Finset.sum_range_succ])
    (by norm_num [scaledLogUpper,logApproximation,logRemainder,Finset.sum_range_succ])
    (criticalActivity*(1-scalarOccupation x)/scalarOccupation x) (hri)
  have hyi : remainingPotential x∈Set.Icc (2.893008921892) (2.893067353673) := by
    rw [remainingPotential_eq_log_div x hx,occupation_remaining_ratio x hx]
    norm_num at hly ⊢
    exact hly
  have hz := cubicCenter_tight_bounds
  have hm : (scalarOccupation x)*(scalarOccupation x)*(remainingPotential x*
      (1+0.016*((remainingPotential x-cubicCenter)*(remainingPotential x-cubicCenter))))<1*x := by
    dyadic_interval +kernel [prec := 80]
  convert hm using 1; simp [scalarPartitionFunction,hx.ne',potential,cubicPotential,cubicCoefficient,pow_two]; norm_num

theorem scalar_box_0488 (x : ℝ) (hx : 0<x)
    (hq : scalarOccupation x∈Set.Icc 0.4648017486572265625 0.4648162841796875) :
    scalarPartitionFunction x<1*x := by
  have hc : 1-scalarOccupation x∈Set.Icc (((175369/327680) : ℚ) : ℝ) (((175373763/327680000) : ℚ) : ℝ) := by
    norm_num
    constructor <;> linarith [hq.1,hq.2]
  have hlx := logarithm_enclosure (175369/327680) (175373763/327680000) (-39071574811/62500000000) (-62511803747/100000000000) (1) (1) 14
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [scaledLogLower,logApproximation,logRemainder,Finset.sum_range_succ])
    (by norm_num [scaledLogUpper,logApproximation,logRemainder,Finset.sum_range_succ])
    (1-scalarOccupation x) (hc)
  have hxi : x∈Set.Icc 0.62511803747 0.625145196976 := by
    have he := occupation_log_identity x
    norm_num at hlx
    constructor <;> linarith [hlx.1,hlx.2]
  have hr := remaining_ratio_bounds ((152306237/327680000)) ((152311/327680)) ((1567367648339/100000000000)) ((1567367648341/100000000000))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (scalarOccupation x) criticalActivity (by convert hq using 1; norm_num) (by convert criticalActivity_bounds using 1; norm_num)
  have hri : criticalActivity*(1-scalarOccupation x)/scalarOccupation x∈Set.Icc
      (((274867697121562091/15231100000000000) : ℚ) : ℝ) (((274875162494021877183/15230623700000000000) : ℚ) : ℝ) := by
    norm_num at hr ⊢
    exact hr
  have hly := logarithm_enclosure (274867697121562091/15231100000000000) (274875162494021877183/15230623700000000000) (578590098071/200000000000) (578601784379/200000000000) (-4) (-4) 14
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [scaledLogLower,logApproximation,logRemainder,Finset.sum_range_succ])
    (by norm_num [scaledLogUpper,logApproximation,logRemainder,Finset.sum_range_succ])
    (criticalActivity*(1-scalarOccupation x)/scalarOccupation x) (hri)
  have hyi : remainingPotential x∈Set.Icc (2.892950490355) (2.893008921895) := by
    rw [remainingPotential_eq_log_div x hx,occupation_remaining_ratio x hx]
    norm_num at hly ⊢
    exact hly
  have hz := cubicCenter_tight_bounds
  have hm : (scalarOccupation x)*(scalarOccupation x)*(remainingPotential x*
      (1+0.016*((remainingPotential x-cubicCenter)*(remainingPotential x-cubicCenter))))<1*x := by
    dyadic_interval +kernel [prec := 80]
  convert hm using 1; simp [scalarPartitionFunction,hx.ne',potential,cubicPotential,cubicCoefficient,pow_two]; norm_num

theorem scalar_box_0489 (x : ℝ) (hx : 0<x)
    (hq : scalarOccupation x∈Set.Icc 0.4648162841796875 0.4648308197021484375) :
    scalarPartitionFunction x<1*x := by
  have hc : 1-scalarOccupation x∈Set.Icc (((175364237/327680000) : ℚ) : ℝ) (((175369/327680) : ℚ) : ℝ) := by
    norm_num
    constructor <;> linarith [hq.1,hq.2]
  have hlx := logarithm_enclosure (175364237/327680000) (175369/327680) (-625172357219/1000000000000) (-25005807879/40000000000) (1) (1) 14
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [scaledLogLower,logApproximation,logRemainder,Finset.sum_range_succ])
    (by norm_num [scaledLogUpper,logApproximation,logRemainder,Finset.sum_range_succ])
    (1-scalarOccupation x) (hc)
  have hxi : x∈Set.Icc 0.625145196975 0.625172357219 := by
    have he := occupation_log_identity x
    norm_num at hlx
    constructor <;> linarith [hlx.1,hlx.2]
  have hr := remaining_ratio_bounds ((152311/327680)) ((152315763/327680000)) ((1567367648339/100000000000)) ((1567367648341/100000000000))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (scalarOccupation x) criticalActivity (by convert hq using 1; norm_num) (by convert criticalActivity_bounds using 1; norm_num)
  have hri : criticalActivity*(1-scalarOccupation x)/scalarOccupation x∈Set.Icc
      (((274860231749453052343/15231576300000000000) : ℚ) : ℝ) (((274867697121912829/15231100000000000) : ℚ) : ℝ) := by
    norm_num at hr ⊢
    exact hr
  have hly := logarithm_enclosure (274860231749453052343/15231576300000000000) (274867697121912829/15231100000000000) (2892892059057/1000000000000) (2892950490357/1000000000000) (-4) (-4) 14
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [scaledLogLower,logApproximation,logRemainder,Finset.sum_range_succ])
    (by norm_num [scaledLogUpper,logApproximation,logRemainder,Finset.sum_range_succ])
    (criticalActivity*(1-scalarOccupation x)/scalarOccupation x) (hri)
  have hyi : remainingPotential x∈Set.Icc (2.892892059057) (2.892950490357) := by
    rw [remainingPotential_eq_log_div x hx,occupation_remaining_ratio x hx]
    norm_num at hly ⊢
    exact hly
  have hz := cubicCenter_tight_bounds
  have hm : (scalarOccupation x)*(scalarOccupation x)*(remainingPotential x*
      (1+0.016*((remainingPotential x-cubicCenter)*(remainingPotential x-cubicCenter))))<1*x := by
    dyadic_interval +kernel [prec := 80]
  convert hm using 1; simp [scalarPartitionFunction,hx.ne',potential,cubicPotential,cubicCoefficient,pow_two]; norm_num

theorem scalar_box_0490 (x : ℝ) (hx : 0<x)
    (hq : scalarOccupation x∈Set.Icc 0.4648308197021484375 0.464845355224609375) :
    scalarPartitionFunction x<1*x := by
  have hc : 1-scalarOccupation x∈Set.Icc (((87679737/163840000) : ℚ) : ℝ) (((175364237/327680000) : ℚ) : ℝ) := by
    norm_num
    constructor <;> linarith [hq.1,hq.2]
  have hlx := logarithm_enclosure (87679737/163840000) (175364237/327680000) (-3125997591/5000000000) (-312586178609/500000000000) (1) (1) 14
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [scaledLogLower,logApproximation,logRemainder,Finset.sum_range_succ])
    (by norm_num [scaledLogUpper,logApproximation,logRemainder,Finset.sum_range_succ])
    (1-scalarOccupation x) (hc)
  have hxi : x∈Set.Icc 0.625172357218 0.6251995182 := by
    have he := occupation_log_identity x
    norm_num at hlx
    constructor <;> linarith [hlx.1,hlx.2]
  have hr := remaining_ratio_bounds ((152315763/327680000)) ((76160263/163840000)) ((1567367648339/100000000000)) ((1567367648341/100000000000))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (scalarOccupation x) criticalActivity (by convert hq using 1; norm_num) (by convert criticalActivity_bounds using 1; norm_num)
  have hri : criticalActivity*(1-scalarOccupation x)/scalarOccupation x∈Set.Icc
      (((137426383188672006843/7616026300000000000) : ℚ) : ℝ) (((274860231749803780817/15231576300000000000) : ℚ) : ℝ) := by
    norm_num at hr ⊢
    exact hr
  have hly := logarithm_enclosure (137426383188672006843/7616026300000000000) (274860231749803780817/15231576300000000000) (723208407/250000000) (144644602953/50000000000) (-4) (-4) 14
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [scaledLogLower,logApproximation,logRemainder,Finset.sum_range_succ])
    (by norm_num [scaledLogUpper,logApproximation,logRemainder,Finset.sum_range_succ])
    (criticalActivity*(1-scalarOccupation x)/scalarOccupation x) (hri)
  have hyi : remainingPotential x∈Set.Icc (2.892833628) (2.89289205906) := by
    rw [remainingPotential_eq_log_div x hx,occupation_remaining_ratio x hx]
    norm_num at hly ⊢
    exact hly
  have hz := cubicCenter_tight_bounds
  have hm : (scalarOccupation x)*(scalarOccupation x)*(remainingPotential x*
      (1+0.016*((remainingPotential x-cubicCenter)*(remainingPotential x-cubicCenter))))<1*x := by
    dyadic_interval +kernel [prec := 80]
  convert hm using 1; simp [scalarPartitionFunction,hx.ne',potential,cubicPotential,cubicCoefficient,pow_two]; norm_num

theorem scalar_box_0491 (x : ℝ) (hx : 0<x)
    (hq : scalarOccupation x∈Set.Icc 0.464845355224609375 0.4648598907470703125) :
    scalarPartitionFunction x<1*x := by
  have hc : 1-scalarOccupation x∈Set.Icc (((175354711/327680000) : ℚ) : ℝ) (((87679737/163840000) : ℚ) : ℝ) := by
    norm_num
    constructor <;> linarith [hq.1,hq.2]
  have hlx := logarithm_enclosure (175354711/327680000) (87679737/163840000) (-625226679919/1000000000000) (-625199518199/1000000000000) (1) (1) 14
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [scaledLogLower,logApproximation,logRemainder,Finset.sum_range_succ])
    (by norm_num [scaledLogUpper,logApproximation,logRemainder,Finset.sum_range_succ])
    (1-scalarOccupation x) (hc)
  have hxi : x∈Set.Icc 0.625199518199 0.625226679919 := by
    have he := occupation_log_identity x
    norm_num at hlx
    constructor <;> linarith [hlx.1,hlx.2]
  have hr := remaining_ratio_bounds ((76160263/163840000)) ((152325289/327680000)) ((1567367648339/100000000000)) ((1567367648341/100000000000))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (scalarOccupation x) criticalActivity (by convert hq using 1; norm_num) (by convert criticalActivity_bounds using 1; norm_num)
  have hri : criticalActivity*(1-scalarOccupation x)/scalarOccupation x∈Set.Icc
      (((274845301005234975029/15232528900000000000) : ℚ) : ℝ) (((137426383188847366317/7616026300000000000) : ℚ) : ℝ) := by
    norm_num at hr ⊢
    exact hr
  have hly := logarithm_enclosure (274845301005234975029/15232528900000000000) (137426383188847366317/7616026300000000000) (2892775197183/1000000000000) (2892833628003/1000000000000) (-4) (-4) 14
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [scaledLogLower,logApproximation,logRemainder,Finset.sum_range_succ])
    (by norm_num [scaledLogUpper,logApproximation,logRemainder,Finset.sum_range_succ])
    (criticalActivity*(1-scalarOccupation x)/scalarOccupation x) (hri)
  have hyi : remainingPotential x∈Set.Icc (2.892775197183) (2.892833628003) := by
    rw [remainingPotential_eq_log_div x hx,occupation_remaining_ratio x hx]
    norm_num at hly ⊢
    exact hly
  have hz := cubicCenter_tight_bounds
  have hm : (scalarOccupation x)*(scalarOccupation x)*(remainingPotential x*
      (1+0.016*((remainingPotential x-cubicCenter)*(remainingPotential x-cubicCenter))))<1*x := by
    dyadic_interval +kernel [prec := 80]
  convert hm using 1; simp [scalarPartitionFunction,hx.ne',potential,cubicPotential,cubicCoefficient,pow_two]; norm_num

theorem scalar_box_0492 (x : ℝ) (hx : 0<x)
    (hq : scalarOccupation x∈Set.Icc 0.4648598907470703125 0.46487442626953125) :
    scalarPartitionFunction x<1*x := by
  have hc : 1-scalarOccupation x∈Set.Icc (((43837487/81920000) : ℚ) : ℝ) (((175354711/327680000) : ℚ) : ℝ) := by
    norm_num
    constructor <;> linarith [hq.1,hq.2]
  have hlx := logarithm_enclosure (43837487/81920000) (175354711/327680000) (-5002030739/8000000000) (-312613339959/500000000000) (1) (1) 14
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [scaledLogLower,logApproximation,logRemainder,Finset.sum_range_succ])
    (by norm_num [scaledLogUpper,logApproximation,logRemainder,Finset.sum_range_succ])
    (1-scalarOccupation x) (hc)
  have hxi : x∈Set.Icc 0.625226679918 0.625253842375 := by
    have he := occupation_log_identity x
    norm_num at hlx
    constructor <;> linarith [hlx.1,hlx.2]
  have hr := remaining_ratio_bounds ((152325289/327680000)) ((38082513/81920000)) ((1567367648339/100000000000)) ((1567367648341/100000000000))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (scalarOccupation x) criticalActivity (by convert hq using 1; norm_num) (by convert criticalActivity_bounds using 1; norm_num)
  have hri : criticalActivity*(1-scalarOccupation x)/scalarOccupation x∈Set.Icc
      (((68709458908281484093/3808251300000000000) : ℚ) : ℝ) (((274845301005585684451/15232528900000000000) : ℚ) : ℝ) := by
    norm_num at hr ⊢
    exact hr
  have hly := logarithm_enclosure (68709458908281484093/3808251300000000000) (274845301005585684451/15232528900000000000) (1446358383303/500000000000) (578555039437/200000000000) (-4) (-4) 14
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [scaledLogLower,logApproximation,logRemainder,Finset.sum_range_succ])
    (by norm_num [scaledLogUpper,logApproximation,logRemainder,Finset.sum_range_succ])
    (criticalActivity*(1-scalarOccupation x)/scalarOccupation x) (hri)
  have hyi : remainingPotential x∈Set.Icc (2.892716766606) (2.892775197185) := by
    rw [remainingPotential_eq_log_div x hx,occupation_remaining_ratio x hx]
    norm_num at hly ⊢
    exact hly
  have hz := cubicCenter_tight_bounds
  have hm : (scalarOccupation x)*(scalarOccupation x)*(remainingPotential x*
      (1+0.016*((remainingPotential x-cubicCenter)*(remainingPotential x-cubicCenter))))<1*x := by
    dyadic_interval +kernel [prec := 80]
  convert hm using 1; simp [scalarPartitionFunction,hx.ne',potential,cubicPotential,cubicCoefficient,pow_two]; norm_num

theorem scalar_box_0493 (x : ℝ) (hx : 0<x)
    (hq : scalarOccupation x∈Set.Icc 0.46487442626953125 0.4648889617919921875) :
    scalarPartitionFunction x<1*x := by
  have hc : 1-scalarOccupation x∈Set.Icc (((35069037/65536000) : ℚ) : ℝ) (((43837487/81920000) : ℚ) : ℝ) := by
    norm_num
    constructor <;> linarith [hq.1,hq.2]
  have hlx := logarithm_enclosure (35069037/65536000) (43837487/81920000) (-625281005569/1000000000000) (-312626921187/500000000000) (1) (1) 14
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [scaledLogLower,logApproximation,logRemainder,Finset.sum_range_succ])
    (by norm_num [scaledLogUpper,logApproximation,logRemainder,Finset.sum_range_succ])
    (1-scalarOccupation x) (hc)
  have hxi : x∈Set.Icc 0.625253842374 0.625281005569 := by
    have he := occupation_log_identity x
    norm_num at hlx
    constructor <;> linarith [hlx.1,hlx.2]
  have hr := remaining_ratio_bounds ((38082513/81920000)) ((30466963/65536000)) ((1567367648339/100000000000)) ((1567367648341/100000000000))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (scalarOccupation x) criticalActivity (by convert hq using 1; norm_num) (by convert criticalActivity_bounds using 1; norm_num)
  have hri : criticalActivity*(1-scalarOccupation x)/scalarOccupation x∈Set.Icc
      (((54966074052203379543/3046696300000000000) : ℚ) : ℝ) (((68709458908369159067/3808251300000000000) : ℚ) : ℝ) := by
    norm_num at hr ⊢
    exact hr
  have hly := logarithm_enclosure (54966074052203379543/3046696300000000000) (68709458908369159067/3808251300000000000) (2892658336269/1000000000000) (180794797913/62500000000) (-4) (-4) 14
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [scaledLogLower,logApproximation,logRemainder,Finset.sum_range_succ])
    (by norm_num [scaledLogUpper,logApproximation,logRemainder,Finset.sum_range_succ])
    (criticalActivity*(1-scalarOccupation x)/scalarOccupation x) (hri)
  have hyi : remainingPotential x∈Set.Icc (2.892658336269) (2.892716766608) := by
    rw [remainingPotential_eq_log_div x hx,occupation_remaining_ratio x hx]
    norm_num at hly ⊢
    exact hly
  have hz := cubicCenter_tight_bounds
  have hm : (scalarOccupation x)*(scalarOccupation x)*(remainingPotential x*
      (1+0.016*((remainingPotential x-cubicCenter)*(remainingPotential x-cubicCenter))))<1*x := by
    dyadic_interval +kernel [prec := 80]
  convert hm using 1; simp [scalarPartitionFunction,hx.ne',potential,cubicPotential,cubicCoefficient,pow_two]; norm_num

theorem scalar_box_0494 (x : ℝ) (hx : 0<x)
    (hq : scalarOccupation x∈Set.Icc 0.4648889617919921875 0.464903497314453125) :
    scalarPartitionFunction x<1*x := by
  have hc : 1-scalarOccupation x∈Set.Icc (((87670211/163840000) : ℚ) : ℝ) (((35069037/65536000) : ℚ) : ℝ) := by
    norm_num
    constructor <;> linarith [hq.1,hq.2]
  have hlx := logarithm_enclosure (87670211/163840000) (35069037/65536000) (-625308169501/1000000000000) (-305312991/488281250) (1) (1) 14
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [scaledLogLower,logApproximation,logRemainder,Finset.sum_range_succ])
    (by norm_num [scaledLogUpper,logApproximation,logRemainder,Finset.sum_range_succ])
    (1-scalarOccupation x) (hc)
  have hxi : x∈Set.Icc 0.625281005568 0.625308169501 := by
    have he := occupation_log_identity x
    norm_num at hlx
    constructor <;> linarith [hlx.1,hlx.2]
  have hr := remaining_ratio_bounds ((30466963/65536000)) ((76169789/163840000)) ((1567367648339/100000000000)) ((1567367648341/100000000000))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (scalarOccupation x) criticalActivity (by convert hq using 1; norm_num) (by convert criticalActivity_bounds using 1; norm_num)
  have hri : criticalActivity*(1-scalarOccupation x)/scalarOccupation x∈Set.Icc
      (((137411452444453929529/7616978900000000000) : ℚ) : ℝ) (((54966074052273517617/3046696300000000000) : ℚ) : ℝ) := by
    norm_num at hr ⊢
    exact hr
  have hly := logarithm_enclosure (137411452444453929529/7616978900000000000) (54966074052273517617/3046696300000000000) (2892599906171/1000000000000) (2892658336271/1000000000000) (-4) (-4) 14
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [scaledLogLower,logApproximation,logRemainder,Finset.sum_range_succ])
    (by norm_num [scaledLogUpper,logApproximation,logRemainder,Finset.sum_range_succ])
    (criticalActivity*(1-scalarOccupation x)/scalarOccupation x) (hri)
  have hyi : remainingPotential x∈Set.Icc (2.892599906171) (2.892658336271) := by
    rw [remainingPotential_eq_log_div x hx,occupation_remaining_ratio x hx]
    norm_num at hly ⊢
    exact hly
  have hz := cubicCenter_tight_bounds
  have hm : (scalarOccupation x)*(scalarOccupation x)*(remainingPotential x*
      (1+0.016*((remainingPotential x-cubicCenter)*(remainingPotential x-cubicCenter))))<1*x := by
    dyadic_interval +kernel [prec := 80]
  convert hm using 1; simp [scalarPartitionFunction,hx.ne',potential,cubicPotential,cubicCoefficient,pow_two]; norm_num

theorem scalar_box_0495 (x : ℝ) (hx : 0<x)
    (hq : scalarOccupation x∈Set.Icc 0.464903497314453125 0.4649180328369140625) :
    scalarPartitionFunction x<1*x := by
  have hc : 1-scalarOccupation x∈Set.Icc (((175335659/327680000) : ℚ) : ℝ) (((87670211/163840000) : ℚ) : ℝ) := by
    norm_num
    constructor <;> linarith [hq.1,hq.2]
  have hlx := logarithm_enclosure (175335659/327680000) (87670211/163840000) (-625335334171/1000000000000) (-1250616339/2000000000) (1) (1) 14
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [scaledLogLower,logApproximation,logRemainder,Finset.sum_range_succ])
    (by norm_num [scaledLogUpper,logApproximation,logRemainder,Finset.sum_range_succ])
    (1-scalarOccupation x) (hc)
  have hxi : x∈Set.Icc 0.6253081695 0.625335334171 := by
    have he := occupation_log_identity x
    norm_num at hlx
    constructor <;> linarith [hlx.1,hlx.2]
  have hr := remaining_ratio_bounds ((76169789/163840000)) ((152344341/327680000)) ((1567367648339/100000000000)) ((1567367648341/100000000000))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (scalarOccupation x) criticalActivity (by convert hq using 1; norm_num) (by convert criticalActivity_bounds using 1; norm_num)
  have hri : criticalActivity*(1-scalarOccupation x)/scalarOccupation x∈Set.Icc
      (((11948497370295600887/662366700000000000) : ℚ) : ℝ) (((137411452444629269951/7616978900000000000) : ℚ) : ℝ) := by
    norm_num at hr ⊢
    exact hr
  have hly := logarithm_enclosure (11948497370295600887/662366700000000000) (137411452444629269951/7616978900000000000) (2892541476313/1000000000000) (2892599906173/1000000000000) (-4) (-4) 14
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [scaledLogLower,logApproximation,logRemainder,Finset.sum_range_succ])
    (by norm_num [scaledLogUpper,logApproximation,logRemainder,Finset.sum_range_succ])
    (criticalActivity*(1-scalarOccupation x)/scalarOccupation x) (hri)
  have hyi : remainingPotential x∈Set.Icc (2.892541476313) (2.892599906173) := by
    rw [remainingPotential_eq_log_div x hx,occupation_remaining_ratio x hx]
    norm_num at hly ⊢
    exact hly
  have hz := cubicCenter_tight_bounds
  have hm : (scalarOccupation x)*(scalarOccupation x)*(remainingPotential x*
      (1+0.016*((remainingPotential x-cubicCenter)*(remainingPotential x-cubicCenter))))<1*x := by
    dyadic_interval +kernel [prec := 80]
  convert hm using 1; simp [scalarPartitionFunction,hx.ne',potential,cubicPotential,cubicCoefficient,pow_two]; norm_num

end HardCoreActivityThreshold
