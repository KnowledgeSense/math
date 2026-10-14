import HardCoreActivityThreshold.ScalarCoordinates

namespace HardCoreActivityThreshold
set_option maxHeartbeats 4000000
set_option maxRecDepth 8192

theorem scalar_box_0032 (x : ℝ) (hx : 0<x)
    (hq : scalarOccupation x∈Set.Icc 0.386400390625 0.38821875) :
    scalarPartitionFunction x<1.001*x := by
  have hc : 1-scalarOccupation x∈Set.Icc (((19577/32000) : ℚ) : ℝ) (((314163/512000) : ℚ) : ℝ) := by
    norm_num
    constructor <;> linarith [hq.1,hq.2]
  have hlx := logarithm_enclosure (19577/32000) (314163/512000) (-245690247503/500000000000) (-488412665541/1000000000000) (1) (1) 14
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [scaledLogLower,logApproximation,logRemainder,Finset.sum_range_succ])
    (by norm_num [scaledLogUpper,logApproximation,logRemainder,Finset.sum_range_succ])
    (1-scalarOccupation x) (hc)
  have hxi : x∈Set.Icc 0.488412665541 0.491380495006 := by
    have he := occupation_log_identity x
    norm_num at hlx
    constructor <;> linarith [hlx.1,hlx.2]
  have hr := remaining_ratio_bounds ((197837/512000)) ((12423/32000)) ((1567367648339/100000000000)) ((1567367648341/100000000000))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (scalarOccupation x) criticalActivity (by convert hq using 1; norm_num) (by convert criticalActivity_bounds using 1; norm_num)
  have hri : criticalActivity*(1-scalarOccupation x)/scalarOccupation x∈Set.Icc
      (((30684356451532603/1242300000000000) : ℚ) : ℝ) (((492408922505753583/19783700000000000) : ℚ) : ℝ) := by
    norm_num at hr ⊢
    exact hr
  have hly := logarithm_enclosure (30684356451532603/1242300000000000) (492408922505753583/19783700000000000) (641357692529/200000000000) (1607225574127/500000000000) (-4) (-4) 14
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [scaledLogLower,logApproximation,logRemainder,Finset.sum_range_succ])
    (by norm_num [scaledLogUpper,logApproximation,logRemainder,Finset.sum_range_succ])
    (criticalActivity*(1-scalarOccupation x)/scalarOccupation x) (hri)
  have hyi : remainingPotential x∈Set.Icc (3.206788462645) (3.214451148254) := by
    rw [remainingPotential_eq_log_div x hx,occupation_remaining_ratio x hx]
    norm_num at hly ⊢
    exact hly
  have hz := cubicCenter_tight_bounds
  have hm : (scalarOccupation x)*(scalarOccupation x)*(remainingPotential x*
      (1+0.016*((remainingPotential x-cubicCenter)*(remainingPotential x-cubicCenter))))<1.001*x := by
    dyadic_interval +kernel [prec := 80]
  convert hm using 1; simp [scalarPartitionFunction,hx.ne',potential,cubicPotential,cubicCoefficient,pow_two]; norm_num

theorem scalar_box_0033 (x : ℝ) (hx : 0<x)
    (hq : scalarOccupation x∈Set.Icc 0.38821875 0.390037109375) :
    scalarPartitionFunction x<1.001*x := by
  have hc : 1-scalarOccupation x∈Set.Icc (((312301/512000) : ℚ) : ℝ) (((19577/32000) : ℚ) : ℝ) := by
    norm_num
    constructor <;> linarith [hq.1,hq.2]
  have hlx := logarithm_enclosure (312301/512000) (19577/32000) (-494357158707/1000000000000) (-98276099001/200000000000) (1) (1) 14
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [scaledLogLower,logApproximation,logRemainder,Finset.sum_range_succ])
    (by norm_num [scaledLogUpper,logApproximation,logRemainder,Finset.sum_range_succ])
    (1-scalarOccupation x) (hc)
  have hxi : x∈Set.Icc 0.491380495005 0.494357158707 := by
    have he := occupation_log_identity x
    norm_num at hlx
    constructor <;> linarith [hlx.1,hlx.2]
  have hr := remaining_ratio_bounds ((12423/32000)) ((199699/512000)) ((1567367648339/100000000000)) ((1567367648341/100000000000))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (scalarOccupation x) criticalActivity (by convert hq using 1; norm_num) (by convert criticalActivity_bounds using 1; norm_num)
  have hri : criticalActivity*(1-scalarOccupation x)/scalarOccupation x∈Set.Icc
      (((489490483943918039/19969900000000000) : ℚ) : ℝ) (((30684356451571757/1242300000000000) : ℚ) : ℝ) := by
    norm_num at hr ⊢
    exact hr
  have hly := logarithm_enclosure (489490483943918039/19969900000000000) (30684356451571757/1242300000000000) (3199138881517/1000000000000) (3206788462647/1000000000000) (-4) (-4) 14
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [scaledLogLower,logApproximation,logRemainder,Finset.sum_range_succ])
    (by norm_num [scaledLogUpper,logApproximation,logRemainder,Finset.sum_range_succ])
    (criticalActivity*(1-scalarOccupation x)/scalarOccupation x) (hri)
  have hyi : remainingPotential x∈Set.Icc (3.199138881517) (3.206788462647) := by
    rw [remainingPotential_eq_log_div x hx,occupation_remaining_ratio x hx]
    norm_num at hly ⊢
    exact hly
  have hz := cubicCenter_tight_bounds
  have hm : (scalarOccupation x)*(scalarOccupation x)*(remainingPotential x*
      (1+0.016*((remainingPotential x-cubicCenter)*(remainingPotential x-cubicCenter))))<1.001*x := by
    dyadic_interval +kernel [prec := 80]
  convert hm using 1; simp [scalarPartitionFunction,hx.ne',potential,cubicPotential,cubicCoefficient,pow_two]; norm_num

theorem scalar_box_0034 (x : ℝ) (hx : 0<x)
    (hq : scalarOccupation x∈Set.Icc 0.390037109375 0.39185546875) :
    scalarPartitionFunction x<1.001*x := by
  have hc : 1-scalarOccupation x∈Set.Icc (((31137/51200) : ℚ) : ℝ) (((312301/512000) : ℚ) : ℝ) := by
    norm_num
    constructor <;> linarith [hq.1,hq.2]
  have hlx := logarithm_enclosure (31137/51200) (312301/512000) (-99468541879/200000000000) (-247178579353/500000000000) (1) (1) 14
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [scaledLogLower,logApproximation,logRemainder,Finset.sum_range_succ])
    (by norm_num [scaledLogUpper,logApproximation,logRemainder,Finset.sum_range_succ])
    (1-scalarOccupation x) (hc)
  have hxi : x∈Set.Icc 0.494357158706 0.497342709395 := by
    have he := occupation_log_identity x
    norm_num at hlx
    constructor <;> linarith [hlx.1,hlx.2]
  have hr := remaining_ratio_bounds ((199699/512000)) ((20063/51200)) ((1567367648339/100000000000)) ((1567367648341/100000000000))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (scalarOccupation x) criticalActivity (by convert hq using 1; norm_num) (by convert criticalActivity_bounds using 1; norm_num)
  have hri : criticalActivity*(1-scalarOccupation x)/scalarOccupation x∈Set.Icc
      (((48803126466331443/2006300000000000) : ℚ) : ℝ) (((489490483944542641/19969900000000000) : ℚ) : ℝ) := by
    norm_num at hr ⊢
    exact hr
  have hly := logarithm_enclosure (48803126466331443/2006300000000000) (489490483944542641/19969900000000000) (638300429607/200000000000) (39989236019/12500000000) (-4) (-4) 14
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [scaledLogLower,logApproximation,logRemainder,Finset.sum_range_succ])
    (by norm_num [scaledLogUpper,logApproximation,logRemainder,Finset.sum_range_succ])
    (criticalActivity*(1-scalarOccupation x)/scalarOccupation x) (hri)
  have hyi : remainingPotential x∈Set.Icc (3.191502148035) (3.19913888152) := by
    rw [remainingPotential_eq_log_div x hx,occupation_remaining_ratio x hx]
    norm_num at hly ⊢
    exact hly
  have hz := cubicCenter_tight_bounds
  have hm : (scalarOccupation x)*(scalarOccupation x)*(remainingPotential x*
      (1+0.016*((remainingPotential x-cubicCenter)*(remainingPotential x-cubicCenter))))<1.001*x := by
    dyadic_interval +kernel [prec := 80]
  convert hm using 1; simp [scalarPartitionFunction,hx.ne',potential,cubicPotential,cubicCoefficient,pow_two]; norm_num

theorem scalar_box_0035 (x : ℝ) (hx : 0<x)
    (hq : scalarOccupation x∈Set.Icc 0.39185546875 0.393673828125) :
    scalarPartitionFunction x<1.001*x := by
  have hc : 1-scalarOccupation x∈Set.Icc (((310439/512000) : ℚ) : ℝ) (((31137/51200) : ℚ) : ℝ) := by
    norm_num
    constructor <;> linarith [hq.1,hq.2]
  have hlx := logarithm_enclosure (310439/512000) (31137/51200) (-250168600147/500000000000) (-248671354697/500000000000) (1) (1) 14
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [scaledLogLower,logApproximation,logRemainder,Finset.sum_range_succ])
    (by norm_num [scaledLogUpper,logApproximation,logRemainder,Finset.sum_range_succ])
    (1-scalarOccupation x) (hc)
  have hxi : x∈Set.Icc 0.497342709394 0.500337200294 := by
    have he := occupation_log_identity x
    norm_num at hlx
    constructor <;> linarith [hlx.1,hlx.2]
  have hr := remaining_ratio_bounds ((20063/51200)) ((201561/512000)) ((1567367648339/100000000000)) ((1567367648341/100000000000))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (scalarOccupation x) criticalActivity (by convert hq using 1; norm_num) (by convert criticalActivity_bounds using 1; norm_num)
  have hri : criticalActivity*(1-scalarOccupation x)/scalarOccupation x∈Set.Icc
      (((486572045382710821/20156100000000000) : ℚ) : ℝ) (((48803126466393717/2006300000000000) : ℚ) : ℝ) := by
    norm_num at hr ⊢
    exact hr
  have hly := logarithm_enclosure (486572045382710821/20156100000000000) (48803126466393717/2006300000000000) (3183878007727/1000000000000) (1595751074019/500000000000) (-4) (-4) 14
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [scaledLogLower,logApproximation,logRemainder,Finset.sum_range_succ])
    (by norm_num [scaledLogUpper,logApproximation,logRemainder,Finset.sum_range_succ])
    (criticalActivity*(1-scalarOccupation x)/scalarOccupation x) (hri)
  have hyi : remainingPotential x∈Set.Icc (3.183878007727) (3.191502148038) := by
    rw [remainingPotential_eq_log_div x hx,occupation_remaining_ratio x hx]
    norm_num at hly ⊢
    exact hly
  have hz := cubicCenter_tight_bounds
  have hm : (scalarOccupation x)*(scalarOccupation x)*(remainingPotential x*
      (1+0.016*((remainingPotential x-cubicCenter)*(remainingPotential x-cubicCenter))))<1.001*x := by
    dyadic_interval +kernel [prec := 80]
  convert hm using 1; simp [scalarPartitionFunction,hx.ne',potential,cubicPotential,cubicCoefficient,pow_two]; norm_num

theorem scalar_box_0036 (x : ℝ) (hx : 0<x)
    (hq : scalarOccupation x∈Set.Icc 0.393673828125 0.3954921875) :
    scalarPartitionFunction x<1.001*x := by
  have hc : 1-scalarOccupation x∈Set.Icc (((77377/128000) : ℚ) : ℝ) (((310439/512000) : ℚ) : ℝ) := by
    norm_num
    constructor <;> linarith [hq.1,hq.2]
  have hlx := logarithm_enclosure (77377/128000) (310439/512000) (-503340685107/1000000000000) (-500337200293/1000000000000) (1) (1) 14
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [scaledLogLower,logApproximation,logRemainder,Finset.sum_range_succ])
    (by norm_num [scaledLogUpper,logApproximation,logRemainder,Finset.sum_range_succ])
    (1-scalarOccupation x) (hc)
  have hxi : x∈Set.Icc 0.500337200293 0.503340685107 := by
    have he := occupation_log_identity x
    norm_num at hlx
    constructor <;> linarith [hlx.1,hlx.2]
  have hr := remaining_ratio_bounds ((201561/512000)) ((50623/128000)) ((1567367648339/100000000000)) ((1567367648341/100000000000))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (scalarOccupation x) criticalActivity (by convert hq using 1; norm_num) (by convert criticalActivity_bounds using 1; norm_num)
  have hri : criticalActivity*(1-scalarOccupation x)/scalarOccupation x∈Set.Icc
      (((5272965501109861/220100000000000) : ℚ) : ℝ) (((486572045383331699/20156100000000000) : ℚ) : ℝ) := by
    norm_num at hr ⊢
    exact hr
  have hly := logarithm_enclosure (5272965501109861/220100000000000) (486572045383331699/20156100000000000) (1588133104211/500000000000) (3183878007729/1000000000000) (-4) (-4) 14
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [scaledLogLower,logApproximation,logRemainder,Finset.sum_range_succ])
    (by norm_num [scaledLogUpper,logApproximation,logRemainder,Finset.sum_range_succ])
    (criticalActivity*(1-scalarOccupation x)/scalarOccupation x) (hri)
  have hyi : remainingPotential x∈Set.Icc (3.176266208422) (3.183878007729) := by
    rw [remainingPotential_eq_log_div x hx,occupation_remaining_ratio x hx]
    norm_num at hly ⊢
    exact hly
  have hz := cubicCenter_tight_bounds
  have hm : (scalarOccupation x)*(scalarOccupation x)*(remainingPotential x*
      (1+0.016*((remainingPotential x-cubicCenter)*(remainingPotential x-cubicCenter))))<1.001*x := by
    dyadic_interval +kernel [prec := 80]
  convert hm using 1; simp [scalarPartitionFunction,hx.ne',potential,cubicPotential,cubicCoefficient,pow_two]; norm_num

theorem scalar_box_0037 (x : ℝ) (hx : 0<x)
    (hq : scalarOccupation x∈Set.Icc 0.3954921875 0.397310546875) :
    scalarPartitionFunction x<1.001*x := by
  have hc : 1-scalarOccupation x∈Set.Icc (((308577/512000) : ℚ) : ℝ) (((77377/128000) : ℚ) : ℝ) := by
    norm_num
    constructor <;> linarith [hq.1,hq.2]
  have hlx := logarithm_enclosure (308577/512000) (77377/128000) (-20254128721/40000000000) (-251670342553/500000000000) (1) (1) 14
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [scaledLogLower,logApproximation,logRemainder,Finset.sum_range_succ])
    (by norm_num [scaledLogUpper,logApproximation,logRemainder,Finset.sum_range_succ])
    (1-scalarOccupation x) (hc)
  have hxi : x∈Set.Icc 0.503340685106 0.506353218025 := by
    have he := occupation_log_identity x
    norm_num at hlx
    constructor <;> linarith [hlx.1,hlx.2]
  have hr := remaining_ratio_bounds ((50623/128000)) ((203423/512000)) ((1567367648339/100000000000)) ((1567367648341/100000000000))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (scalarOccupation x) criticalActivity (by convert hq using 1; norm_num) (by convert criticalActivity_bounds using 1; norm_num)
  have hri : criticalActivity*(1-scalarOccupation x)/scalarOccupation x∈Set.Icc
      (((483653606821503603/20342300000000000) : ℚ) : ℝ) (((121278206525681557/5062300000000000) : ℚ) : ℝ) := by
    norm_num at hr ⊢
    exact hr
  have hly := logarithm_enclosure (483653606821503603/20342300000000000) (121278206525681557/5062300000000000) (3168666500197/1000000000000) (397033276053/125000000000) (-4) (-4) 14
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [scaledLogLower,logApproximation,logRemainder,Finset.sum_range_succ])
    (by norm_num [scaledLogUpper,logApproximation,logRemainder,Finset.sum_range_succ])
    (criticalActivity*(1-scalarOccupation x)/scalarOccupation x) (hri)
  have hyi : remainingPotential x∈Set.Icc (3.168666500197) (3.176266208424) := by
    rw [remainingPotential_eq_log_div x hx,occupation_remaining_ratio x hx]
    norm_num at hly ⊢
    exact hly
  have hz := cubicCenter_tight_bounds
  have hm : (scalarOccupation x)*(scalarOccupation x)*(remainingPotential x*
      (1+0.016*((remainingPotential x-cubicCenter)*(remainingPotential x-cubicCenter))))<1.001*x := by
    dyadic_interval +kernel [prec := 80]
  convert hm using 1; simp [scalarPartitionFunction,hx.ne',potential,cubicPotential,cubicCoefficient,pow_two]; norm_num

theorem scalar_box_0038 (x : ℝ) (hx : 0<x)
    (hq : scalarOccupation x∈Set.Icc 0.397310546875 0.39912890625) :
    scalarPartitionFunction x<1.001*x := by
  have hc : 1-scalarOccupation x∈Set.Icc (((153823/256000) : ℚ) : ℝ) (((308577/512000) : ℚ) : ℝ) := by
    norm_num
    constructor <;> linarith [hq.1,hq.2]
  have hlx := logarithm_enclosure (153823/256000) (308577/512000) (-254687426863/500000000000) (-63294152253/125000000000) (1) (1) 14
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [scaledLogLower,logApproximation,logRemainder,Finset.sum_range_succ])
    (by norm_num [scaledLogUpper,logApproximation,logRemainder,Finset.sum_range_succ])
    (1-scalarOccupation x) (hc)
  have hxi : x∈Set.Icc 0.506353218024 0.509374853726 := by
    have he := occupation_log_identity x
    norm_num at hlx
    constructor <;> linarith [hlx.1,hlx.2]
  have hr := remaining_ratio_bounds ((203423/512000)) ((102177/256000)) ((1567367648339/100000000000)) ((1567367648341/100000000000))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (scalarOccupation x) criticalActivity (by convert hq using 1; norm_num) (by convert criticalActivity_bounds using 1; norm_num)
  have hri : criticalActivity*(1-scalarOccupation x)/scalarOccupation x∈Set.Icc
      (((241097193770449997/10217700000000000) : ℚ) : ℝ) (((43968509711101887/1849300000000000) : ℚ) : ℝ) := by
    norm_num at hr ⊢
    exact hr
  have hly := logarithm_enclosure (241097193770449997/10217700000000000) (43968509711101887/1849300000000000) (1580539317659/500000000000) (3168666500199/1000000000000) (-4) (-4) 14
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [scaledLogLower,logApproximation,logRemainder,Finset.sum_range_succ])
    (by norm_num [scaledLogUpper,logApproximation,logRemainder,Finset.sum_range_succ])
    (criticalActivity*(1-scalarOccupation x)/scalarOccupation x) (hri)
  have hyi : remainingPotential x∈Set.Icc (3.161078635318) (3.168666500199) := by
    rw [remainingPotential_eq_log_div x hx,occupation_remaining_ratio x hx]
    norm_num at hly ⊢
    exact hly
  have hz := cubicCenter_tight_bounds
  have hm : (scalarOccupation x)*(scalarOccupation x)*(remainingPotential x*
      (1+0.016*((remainingPotential x-cubicCenter)*(remainingPotential x-cubicCenter))))<1.001*x := by
    dyadic_interval +kernel [prec := 80]
  convert hm using 1; simp [scalarPartitionFunction,hx.ne',potential,cubicPotential,cubicCoefficient,pow_two]; norm_num

theorem scalar_box_0039 (x : ℝ) (hx : 0<x)
    (hq : scalarOccupation x∈Set.Icc 0.39912890625 0.400947265625) :
    scalarPartitionFunction x<1.001*x := by
  have hc : 1-scalarOccupation x∈Set.Icc (((61343/102400) : ℚ) : ℝ) (((153823/256000) : ℚ) : ℝ) := by
    norm_num
    constructor <;> linarith [hq.1,hq.2]
  have hlx := logarithm_enclosure (61343/102400) (153823/256000) (-128101411847/250000000000) (-20374994149/40000000000) (1) (1) 14
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [scaledLogLower,logApproximation,logRemainder,Finset.sum_range_succ])
    (by norm_num [scaledLogUpper,logApproximation,logRemainder,Finset.sum_range_succ])
    (1-scalarOccupation x) (hc)
  have hxi : x∈Set.Icc 0.509374853725 0.512405647388 := by
    have he := occupation_log_identity x
    norm_num at hlx
    constructor <;> linarith [hlx.1,hlx.2]
  have hr := remaining_ratio_bounds ((102177/256000)) ((41057/102400)) ((1567367648339/100000000000)) ((1567367648341/100000000000))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (scalarOccupation x) criticalActivity (by convert hq using 1; norm_num) (by convert criticalActivity_bounds using 1; norm_num)
  have hri : criticalActivity*(1-scalarOccupation x)/scalarOccupation x∈Set.Icc
      (((96147033652059277/4105700000000000) : ℚ) : ℝ) (((241097193770757643/10217700000000000) : ℚ) : ℝ) := by
    norm_num at hr ⊢
    exact hr
  have hly := logarithm_enclosure (96147033652059277/4105700000000000) (241097193770757643/10217700000000000) (3153502368187/1000000000000) (79026965883/25000000000) (-4) (-4) 14
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [scaledLogLower,logApproximation,logRemainder,Finset.sum_range_succ])
    (by norm_num [scaledLogUpper,logApproximation,logRemainder,Finset.sum_range_succ])
    (criticalActivity*(1-scalarOccupation x)/scalarOccupation x) (hri)
  have hyi : remainingPotential x∈Set.Icc (3.153502368187) (3.16107863532) := by
    rw [remainingPotential_eq_log_div x hx,occupation_remaining_ratio x hx]
    norm_num at hly ⊢
    exact hly
  have hz := cubicCenter_tight_bounds
  have hm : (scalarOccupation x)*(scalarOccupation x)*(remainingPotential x*
      (1+0.016*((remainingPotential x-cubicCenter)*(remainingPotential x-cubicCenter))))<1.001*x := by
    dyadic_interval +kernel [prec := 80]
  convert hm using 1; simp [scalarPartitionFunction,hx.ne',potential,cubicPotential,cubicCoefficient,pow_two]; norm_num

theorem scalar_box_0040 (x : ℝ) (hx : 0<x)
    (hq : scalarOccupation x∈Set.Icc 0.400947265625 0.402765625) :
    scalarPartitionFunction x<1.001*x := by
  have hc : 1-scalarOccupation x∈Set.Icc (((38223/64000) : ℚ) : ℝ) (((61343/102400) : ℚ) : ℝ) := by
    norm_num
    constructor <;> linarith [hq.1,hq.2]
  have hlx := logarithm_enclosure (38223/64000) (61343/102400) (-515445654693/1000000000000) (-512405647387/1000000000000) (1) (1) 14
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [scaledLogLower,logApproximation,logRemainder,Finset.sum_range_succ])
    (by norm_num [scaledLogUpper,logApproximation,logRemainder,Finset.sum_range_succ])
    (1-scalarOccupation x) (hc)
  have hxi : x∈Set.Icc 0.512405647387 0.515445654693 := by
    have he := occupation_log_identity x
    norm_num at hlx
    constructor <;> linarith [hlx.1,hlx.2]
  have hr := remaining_ratio_bounds ((41057/102400)) ((25777/64000)) ((1567367648339/100000000000)) ((1567367648341/100000000000))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (scalarOccupation x) criticalActivity (by convert hq using 1; norm_num) (by convert criticalActivity_bounds using 1; norm_num)
  have hri : criticalActivity*(1-scalarOccupation x)/scalarOccupation x∈Set.Icc
      (((59909493622461597/2577700000000000) : ℚ) : ℝ) (((96147033652181963/4105700000000000) : ℚ) : ℝ) := by
    norm_num at hr ⊢
    exact hr
  have hly := logarithm_enclosure (59909493622461597/2577700000000000) (96147033652181963/4105700000000000) (393242181911/125000000000) (315350236819/100000000000) (-4) (-4) 14
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [scaledLogLower,logApproximation,logRemainder,Finset.sum_range_succ])
    (by norm_num [scaledLogUpper,logApproximation,logRemainder,Finset.sum_range_succ])
    (criticalActivity*(1-scalarOccupation x)/scalarOccupation x) (hri)
  have hyi : remainingPotential x∈Set.Icc (3.145937455288) (3.15350236819) := by
    rw [remainingPotential_eq_log_div x hx,occupation_remaining_ratio x hx]
    norm_num at hly ⊢
    exact hly
  have hz := cubicCenter_tight_bounds
  have hm : (scalarOccupation x)*(scalarOccupation x)*(remainingPotential x*
      (1+0.016*((remainingPotential x-cubicCenter)*(remainingPotential x-cubicCenter))))<1.001*x := by
    dyadic_interval +kernel [prec := 80]
  convert hm using 1; simp [scalarPartitionFunction,hx.ne',potential,cubicPotential,cubicCoefficient,pow_two]; norm_num

theorem scalar_box_0041 (x : ℝ) (hx : 0<x)
    (hq : scalarOccupation x∈Set.Icc 0.402765625 0.404583984375) :
    scalarPartitionFunction x<1.001*x := by
  have hc : 1-scalarOccupation x∈Set.Icc (((304853/512000) : ℚ) : ℝ) (((38223/64000) : ℚ) : ℝ) := by
    norm_num
    constructor <;> linarith [hq.1,hq.2]
  have hlx := logarithm_enclosure (304853/512000) (38223/64000) (-518494931829/1000000000000) (-128861413673/250000000000) (1) (1) 14
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [scaledLogLower,logApproximation,logRemainder,Finset.sum_range_succ])
    (by norm_num [scaledLogUpper,logApproximation,logRemainder,Finset.sum_range_succ])
    (1-scalarOccupation x) (hc)
  have hxi : x∈Set.Icc 0.515445654692 0.518494931829 := by
    have he := occupation_log_identity x
    norm_num at hlx
    constructor <;> linarith [hlx.1,hlx.2]
  have hr := remaining_ratio_bounds ((25777/64000)) ((207147/512000)) ((1567367648339/100000000000)) ((1567367648341/100000000000))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (scalarOccupation x) criticalActivity (by convert hq using 1; norm_num) (by convert criticalActivity_bounds using 1; norm_num)
  have hri : criticalActivity*(1-scalarOccupation x)/scalarOccupation x∈Set.Icc
      (((477816729699089167/20714700000000000) : ℚ) : ℝ) (((59909493622538043/2577700000000000) : ℚ) : ℝ) := by
    norm_num at hr ⊢
    exact hr
  have hly := logarithm_enclosure (477816729699089167/20714700000000000) (59909493622538043/2577700000000000) (1569191827567/500000000000) (3145937455291/1000000000000) (-4) (-4) 14
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [scaledLogLower,logApproximation,logRemainder,Finset.sum_range_succ])
    (by norm_num [scaledLogUpper,logApproximation,logRemainder,Finset.sum_range_succ])
    (criticalActivity*(1-scalarOccupation x)/scalarOccupation x) (hri)
  have hyi : remainingPotential x∈Set.Icc (3.138383655134) (3.145937455291) := by
    rw [remainingPotential_eq_log_div x hx,occupation_remaining_ratio x hx]
    norm_num at hly ⊢
    exact hly
  have hz := cubicCenter_tight_bounds
  have hm : (scalarOccupation x)*(scalarOccupation x)*(remainingPotential x*
      (1+0.016*((remainingPotential x-cubicCenter)*(remainingPotential x-cubicCenter))))<1.001*x := by
    dyadic_interval +kernel [prec := 80]
  convert hm using 1; simp [scalarPartitionFunction,hx.ne',potential,cubicPotential,cubicCoefficient,pow_two]; norm_num

theorem scalar_box_0042 (x : ℝ) (hx : 0<x)
    (hq : scalarOccupation x∈Set.Icc 0.404583984375 0.4054931640625) :
    scalarPartitionFunction x<1.001*x := by
  have hc : 1-scalarOccupation x∈Set.Icc (((24351/40960) : ℚ) : ℝ) (((304853/512000) : ℚ) : ℝ) := by
    norm_num
    constructor <;> linarith [hq.1,hq.2]
  have hlx := logarithm_enclosure (24351/40960) (304853/512000) (-104004612857/200000000000) (-129623732957/250000000000) (1) (1) 14
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [scaledLogLower,logApproximation,logRemainder,Finset.sum_range_succ])
    (by norm_num [scaledLogUpper,logApproximation,logRemainder,Finset.sum_range_succ])
    (1-scalarOccupation x) (hc)
  have hxi : x∈Set.Icc 0.518494931828 0.520023064285 := by
    have he := occupation_log_identity x
    norm_num at hlx
    constructor <;> linarith [hlx.1,hlx.2]
  have hr := remaining_ratio_bounds ((207147/512000)) ((16609/40960)) ((1567367648339/100000000000)) ((1567367648341/100000000000))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (scalarOccupation x) criticalActivity (by convert hq using 1; norm_num) (by convert criticalActivity_bounds using 1; norm_num)
  have hri : criticalActivity*(1-scalarOccupation x)/scalarOccupation x∈Set.Icc
      (((38166969604702989/1660900000000000) : ℚ) : ℝ) (((477816729699698873/20714700000000000) : ℚ) : ℝ) := by
    norm_num at hr ⊢
    exact hr
  have hly := logarithm_enclosure (38166969604702989/1660900000000000) (477816729699698873/20714700000000000) (783652711853/250000000000) (98074489223/31250000000) (-4) (-4) 14
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [scaledLogLower,logApproximation,logRemainder,Finset.sum_range_succ])
    (by norm_num [scaledLogUpper,logApproximation,logRemainder,Finset.sum_range_succ])
    (criticalActivity*(1-scalarOccupation x)/scalarOccupation x) (hri)
  have hyi : remainingPotential x∈Set.Icc (3.134610847412) (3.138383655136) := by
    rw [remainingPotential_eq_log_div x hx,occupation_remaining_ratio x hx]
    norm_num at hly ⊢
    exact hly
  have hz := cubicCenter_tight_bounds
  have hm : (scalarOccupation x)*(scalarOccupation x)*(remainingPotential x*
      (1+0.016*((remainingPotential x-cubicCenter)*(remainingPotential x-cubicCenter))))<1.001*x := by
    dyadic_interval +kernel [prec := 80]
  convert hm using 1; simp [scalarPartitionFunction,hx.ne',potential,cubicPotential,cubicCoefficient,pow_two]; norm_num

theorem scalar_box_0043 (x : ℝ) (hx : 0<x)
    (hq : scalarOccupation x∈Set.Icc 0.4054931640625 0.40640234375) :
    scalarPartitionFunction x<1.001*x := by
  have hc : 1-scalarOccupation x∈Set.Icc (((151961/256000) : ℚ) : ℝ) (((24351/40960) : ℚ) : ℝ) := by
    norm_num
    constructor <;> linarith [hq.1,hq.2]
  have hlx := logarithm_enclosure (151961/256000) (24351/40960) (-521553535503/1000000000000) (-130005766071/250000000000) (1) (1) 14
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [scaledLogLower,logApproximation,logRemainder,Finset.sum_range_succ])
    (by norm_num [scaledLogUpper,logApproximation,logRemainder,Finset.sum_range_succ])
    (1-scalarOccupation x) (hc)
  have hxi : x∈Set.Icc 0.520023064284 0.521553535503 := by
    have he := occupation_log_identity x
    norm_num at hlx
    constructor <;> linarith [hlx.1,hlx.2]
  have hr := remaining_ratio_bounds ((16609/40960)) ((104039/256000)) ((1567367648339/100000000000)) ((1567367648341/100000000000))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (scalarOccupation x) criticalActivity (by convert hq using 1; norm_num) (by convert criticalActivity_bounds using 1; norm_num)
  have hri : criticalActivity*(1-scalarOccupation x)/scalarOccupation x∈Set.Icc
      (((238178755209242779/10403900000000000) : ℚ) : ℝ) (((38166969604751691/1660900000000000) : ℚ) : ℝ) := by
    norm_num at hr ⊢
    exact hr
  have hly := logarithm_enclosure (238178755209242779/10403900000000000) (38166969604751691/1660900000000000) (3130840728213/1000000000000) (626922169483/200000000000) (-4) (-4) 14
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [scaledLogLower,logApproximation,logRemainder,Finset.sum_range_succ])
    (by norm_num [scaledLogUpper,logApproximation,logRemainder,Finset.sum_range_succ])
    (criticalActivity*(1-scalarOccupation x)/scalarOccupation x) (hri)
  have hyi : remainingPotential x∈Set.Icc (3.130840728213) (3.134610847415) := by
    rw [remainingPotential_eq_log_div x hx,occupation_remaining_ratio x hx]
    norm_num at hly ⊢
    exact hly
  have hz := cubicCenter_tight_bounds
  have hm : (scalarOccupation x)*(scalarOccupation x)*(remainingPotential x*
      (1+0.016*((remainingPotential x-cubicCenter)*(remainingPotential x-cubicCenter))))<1.001*x := by
    dyadic_interval +kernel [prec := 80]
  convert hm using 1; simp [scalarPartitionFunction,hx.ne',potential,cubicPotential,cubicCoefficient,pow_two]; norm_num

theorem scalar_box_0044 (x : ℝ) (hx : 0<x)
    (hq : scalarOccupation x∈Set.Icc 0.40640234375 0.4073115234375) :
    scalarPartitionFunction x<1.001*x := by
  have hc : 1-scalarOccupation x∈Set.Icc (((606913/1024000) : ℚ) : ℝ) (((151961/256000) : ℚ) : ℝ) := by
    norm_num
    constructor <;> linarith [hq.1,hq.2]
  have hlx := logarithm_enclosure (606913/1024000) (151961/256000) (-104617270531/200000000000) (-260776767751/500000000000) (1) (1) 14
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [scaledLogLower,logApproximation,logRemainder,Finset.sum_range_succ])
    (by norm_num [scaledLogUpper,logApproximation,logRemainder,Finset.sum_range_succ])
    (1-scalarOccupation x) (hc)
  have hxi : x∈Set.Icc 0.521553535502 0.523086352655 := by
    have he := occupation_log_identity x
    norm_num at hlx
    constructor <;> linarith [hlx.1,hlx.2]
  have hr := remaining_ratio_bounds ((104039/256000)) ((417087/1024000)) ((1567367648339/100000000000)) ((1567367648341/100000000000))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (scalarOccupation x) criticalActivity (by convert hq using 1; norm_num) (by convert criticalActivity_bounds using 1; norm_num)
  have hri : criticalActivity*(1-scalarOccupation x)/scalarOccupation x∈Set.Icc
      (((951255801556367507/41708700000000000) : ℚ) : ℝ) (((4493938777538617/196300000000000) : ℚ) : ℝ) := by
    norm_num at hr ⊢
    exact hr
  have hly := logarithm_enclosure (951255801556367507/41708700000000000) (4493938777538617/196300000000000) (390884158487/125000000000) (626168145643/200000000000) (-4) (-4) 14
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [scaledLogLower,logApproximation,logRemainder,Finset.sum_range_succ])
    (by norm_num [scaledLogUpper,logApproximation,logRemainder,Finset.sum_range_succ])
    (criticalActivity*(1-scalarOccupation x)/scalarOccupation x) (hri)
  have hyi : remainingPotential x∈Set.Icc (3.127073267896) (3.130840728215) := by
    rw [remainingPotential_eq_log_div x hx,occupation_remaining_ratio x hx]
    norm_num at hly ⊢
    exact hly
  have hz := cubicCenter_tight_bounds
  have hm : (scalarOccupation x)*(scalarOccupation x)*(remainingPotential x*
      (1+0.016*((remainingPotential x-cubicCenter)*(remainingPotential x-cubicCenter))))<1.001*x := by
    dyadic_interval +kernel [prec := 80]
  convert hm using 1; simp [scalarPartitionFunction,hx.ne',potential,cubicPotential,cubicCoefficient,pow_two]; norm_num

theorem scalar_box_0045 (x : ℝ) (hx : 0<x)
    (hq : scalarOccupation x∈Set.Icc 0.4073115234375 0.408220703125) :
    scalarPartitionFunction x<1.001*x := by
  have hc : 1-scalarOccupation x∈Set.Icc (((302991/512000) : ℚ) : ℝ) (((606913/1024000) : ℚ) : ℝ) := by
    norm_num
    constructor <;> linarith [hq.1,hq.2]
  have hlx := logarithm_enclosure (302991/512000) (606913/1024000) (-262310761471/500000000000) (-261543176327/500000000000) (1) (1) 14
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [scaledLogLower,logApproximation,logRemainder,Finset.sum_range_succ])
    (by norm_num [scaledLogUpper,logApproximation,logRemainder,Finset.sum_range_succ])
    (1-scalarOccupation x) (hc)
  have hxi : x∈Set.Icc 0.523086352654 0.524621522942 := by
    have he := occupation_log_identity x
    norm_num at hlx
    constructor <;> linarith [hlx.1,hlx.2]
  have hr := remaining_ratio_bounds ((417087/1024000)) ((209009/512000)) ((1567367648339/100000000000)) ((1567367648341/100000000000))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (scalarOccupation x) criticalActivity (by convert hq using 1; norm_num) (by convert criticalActivity_bounds using 1; norm_num)
  have hri : criticalActivity*(1-scalarOccupation x)/scalarOccupation x∈Set.Icc
      (((10104218960380467/444700000000000) : ℚ) : ℝ) (((86477800141598303/3791700000000000) : ℚ) : ℝ) := by
    norm_num at hr ⊢
    exact hr
  have hly := logarithm_enclosure (10104218960380467/444700000000000) (86477800141598303/3791700000000000) (1561654218471/500000000000) (1563536633949/500000000000) (-4) (-4) 14
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [scaledLogLower,logApproximation,logRemainder,Finset.sum_range_succ])
    (by norm_num [scaledLogUpper,logApproximation,logRemainder,Finset.sum_range_succ])
    (criticalActivity*(1-scalarOccupation x)/scalarOccupation x) (hri)
  have hyi : remainingPotential x∈Set.Icc (3.123308436942) (3.127073267898) := by
    rw [remainingPotential_eq_log_div x hx,occupation_remaining_ratio x hx]
    norm_num at hly ⊢
    exact hly
  have hz := cubicCenter_tight_bounds
  have hm : (scalarOccupation x)*(scalarOccupation x)*(remainingPotential x*
      (1+0.016*((remainingPotential x-cubicCenter)*(remainingPotential x-cubicCenter))))<1.001*x := by
    dyadic_interval +kernel [prec := 80]
  convert hm using 1; simp [scalarPartitionFunction,hx.ne',potential,cubicPotential,cubicCoefficient,pow_two]; norm_num

theorem scalar_box_0046 (x : ℝ) (hx : 0<x)
    (hq : scalarOccupation x∈Set.Icc 0.408220703125 0.4091298828125) :
    scalarPartitionFunction x<1.001*x := by
  have hc : 1-scalarOccupation x∈Set.Icc (((605051/1024000) : ℚ) : ℝ) (((302991/512000) : ℚ) : ℝ) := by
    norm_num
    constructor <;> linarith [hq.1,hq.2]
  have hlx := logarithm_enclosure (605051/1024000) (302991/512000) (-526159053601/1000000000000) (-524621522941/1000000000000) (1) (1) 14
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [scaledLogLower,logApproximation,logRemainder,Finset.sum_range_succ])
    (by norm_num [scaledLogUpper,logApproximation,logRemainder,Finset.sum_range_succ])
    (1-scalarOccupation x) (hc)
  have hxi : x∈Set.Icc 0.524621522941 0.526159053601 := by
    have he := occupation_log_identity x
    norm_num at hlx
    constructor <;> linarith [hlx.1,hlx.2]
  have hr := remaining_ratio_bounds ((209009/512000)) ((418949/1024000)) ((1567367648339/100000000000)) ((1567367648341/100000000000))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (scalarOccupation x) criticalActivity (by convert hq using 1; norm_num) (by convert criticalActivity_bounds using 1; norm_num)
  have hri : criticalActivity*(1-scalarOccupation x)/scalarOccupation x∈Set.Icc
      (((948337362995160289/41894900000000000) : ℚ) : ℝ) (((474898291138487931/20900900000000000) : ℚ) : ℝ) := by
    norm_num at hr ⊢
    exact hr
  have hly := logarithm_enclosure (948337362995160289/41894900000000000) (474898291138487931/20900900000000000) (389943275743/125000000000) (195206777309/62500000000) (-4) (-4) 14
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [scaledLogLower,logApproximation,logRemainder,Finset.sum_range_succ])
    (by norm_num [scaledLogUpper,logApproximation,logRemainder,Finset.sum_range_succ])
    (criticalActivity*(1-scalarOccupation x)/scalarOccupation x) (hri)
  have hyi : remainingPotential x∈Set.Icc (3.119546205944) (3.123308436944) := by
    rw [remainingPotential_eq_log_div x hx,occupation_remaining_ratio x hx]
    norm_num at hly ⊢
    exact hly
  have hz := cubicCenter_tight_bounds
  have hm : (scalarOccupation x)*(scalarOccupation x)*(remainingPotential x*
      (1+0.016*((remainingPotential x-cubicCenter)*(remainingPotential x-cubicCenter))))<1.001*x := by
    dyadic_interval +kernel [prec := 80]
  convert hm using 1; simp [scalarPartitionFunction,hx.ne',potential,cubicPotential,cubicCoefficient,pow_two]; norm_num

theorem scalar_box_0047 (x : ℝ) (hx : 0<x)
    (hq : scalarOccupation x∈Set.Icc 0.4091298828125 0.4100390625) :
    scalarPartitionFunction x<1.001*x := by
  have hc : 1-scalarOccupation x∈Set.Icc (((15103/25600) : ℚ) : ℝ) (((605051/1024000) : ℚ) : ℝ) := by
    norm_num
    constructor <;> linarith [hq.1,hq.2]
  have hlx := logarithm_enclosure (15103/25600) (605051/1024000) (-263849475951/500000000000) (-657698817/1250000000) (1) (1) 14
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [scaledLogLower,logApproximation,logRemainder,Finset.sum_range_succ])
    (by norm_num [scaledLogUpper,logApproximation,logRemainder,Finset.sum_range_succ])
    (1-scalarOccupation x) (hc)
  have hxi : x∈Set.Icc 0.5261590536 0.527698951902 := by
    have he := occupation_log_identity x
    norm_num at hlx
    constructor <;> linarith [hlx.1,hlx.2]
  have hr := remaining_ratio_bounds ((418949/1024000)) ((10497/25600)) ((1567367648339/100000000000)) ((1567367648341/100000000000))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (scalarOccupation x) criticalActivity (by convert hq using 1; norm_num) (by convert criticalActivity_bounds using 1; norm_num)
  have hri : criticalActivity*(1-scalarOccupation x)/scalarOccupation x∈Set.Icc
      (((23671953592863917/1049700000000000) : ℚ) : ℝ) (((948337362996370391/41894900000000000) : ℚ) : ℝ) := by
    norm_num at hr ⊢
    exact hr
  have hly := logarithm_enclosure (23671953592863917/1049700000000000) (948337362996370391/41894900000000000) (3115786545613/1000000000000) (3119546205947/1000000000000) (-4) (-4) 14
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [scaledLogLower,logApproximation,logRemainder,Finset.sum_range_succ])
    (by norm_num [scaledLogUpper,logApproximation,logRemainder,Finset.sum_range_succ])
    (criticalActivity*(1-scalarOccupation x)/scalarOccupation x) (hri)
  have hyi : remainingPotential x∈Set.Icc (3.115786545613) (3.119546205947) := by
    rw [remainingPotential_eq_log_div x hx,occupation_remaining_ratio x hx]
    norm_num at hly ⊢
    exact hly
  have hz := cubicCenter_tight_bounds
  have hm : (scalarOccupation x)*(scalarOccupation x)*(remainingPotential x*
      (1+0.016*((remainingPotential x-cubicCenter)*(remainingPotential x-cubicCenter))))<1.001*x := by
    dyadic_interval +kernel [prec := 80]
  convert hm using 1; simp [scalarPartitionFunction,hx.ne',potential,cubicPotential,cubicCoefficient,pow_two]; norm_num

end HardCoreActivityThreshold
