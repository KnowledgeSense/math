import HardCoreActivityThreshold.ScalarCoordinates

namespace HardCoreActivityThreshold
set_option maxHeartbeats 4000000
set_option maxRecDepth 8192

theorem scalar_box_0528 (x : ℝ) (hx : 0<x)
    (hq : scalarOccupation x∈Set.Icc 0.465833770751953125 0.465862841796875) :
    scalarPartitionFunction x<1*x := by
  have hc : 1-scalarOccupation x∈Set.Icc (((10939129/20480000) : ℚ) : ℝ) (((17503559/32768000) : ℚ) : ℝ) := by
    norm_num
    constructor <;> linarith [hq.1,hq.2]
  have hlx := logarithm_enclosure (10939129/20480000) (17503559/32768000) (-125420524487/200000000000) (-78381024717/125000000000) (1) (1) 14
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [scaledLogLower,logApproximation,logRemainder,Finset.sum_range_succ])
    (by norm_num [scaledLogUpper,logApproximation,logRemainder,Finset.sum_range_succ])
    (1-scalarOccupation x) (hc)
  have hxi : x∈Set.Icc 0.627048197736 0.627102622435 := by
    have he := occupation_log_identity x
    norm_num at hlx
    constructor <;> linarith [hlx.1,hlx.2]
  have hr := remaining_ratio_bounds ((15264441/32768000)) ((9540871/20480000)) ((1567367648339/100000000000)) ((1567367648341/100000000000))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (scalarOccupation x) criticalActivity (by convert hq using 1; norm_num) (by convert criticalActivity_bounds using 1; norm_num)
  have hri : criticalActivity*(1-scalarOccupation x)/scalarOccupation x∈Set.Icc
      (((17145636895606956731/954087100000000000) : ℚ) : ℝ) (((27434512107427945619/1526444100000000000) : ℚ) : ℝ) := by
    norm_num at hr ⊢
    exact hr
  have hly := logarithm_enclosure (17145636895606956731/954087100000000000) (27434512107427945619/1526444100000000000) (45136625699/15625000000) (2888860873967/1000000000000) (-4) (-4) 14
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [scaledLogLower,logApproximation,logRemainder,Finset.sum_range_succ])
    (by norm_num [scaledLogUpper,logApproximation,logRemainder,Finset.sum_range_succ])
    (criticalActivity*(1-scalarOccupation x)/scalarOccupation x) (hri)
  have hyi : remainingPotential x∈Set.Icc (2.888744044736) (2.888860873967) := by
    rw [remainingPotential_eq_log_div x hx,occupation_remaining_ratio x hx]
    norm_num at hly ⊢
    exact hly
  have hz := cubicCenter_tight_bounds
  have hm : (scalarOccupation x)*(scalarOccupation x)*(remainingPotential x*
      (1+0.016*((remainingPotential x-cubicCenter)*(remainingPotential x-cubicCenter))))<1*x := by
    dyadic_interval +kernel [prec := 80]
  convert hm using 1; simp [scalarPartitionFunction,hx.ne',potential,cubicPotential,cubicCoefficient,pow_two]; norm_num

theorem scalar_box_0529 (x : ℝ) (hx : 0<x)
    (hq : scalarOccupation x∈Set.Icc 0.465862841796875 0.465891912841796875) :
    scalarPartitionFunction x<1*x := by
  have hc : 1-scalarOccupation x∈Set.Icc (((87508269/163840000) : ℚ) : ℝ) (((10939129/20480000) : ℚ) : ℝ) := by
    norm_num
    constructor <;> linarith [hq.1,hq.2]
  have hlx := logarithm_enclosure (87508269/163840000) (10939129/20480000) (-39197315631/62500000000) (-313551311217/500000000000) (1) (1) 14
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [scaledLogLower,logApproximation,logRemainder,Finset.sum_range_succ])
    (by norm_num [scaledLogUpper,logApproximation,logRemainder,Finset.sum_range_succ])
    (1-scalarOccupation x) (hc)
  have hxi : x∈Set.Icc 0.627102622434 0.627157050096 := by
    have he := occupation_log_identity x
    norm_num at hlx
    constructor <;> linarith [hlx.1,hlx.2]
  have hr := remaining_ratio_bounds ((9540871/20480000)) ((76331731/163840000)) ((1567367648339/100000000000)) ((1567367648341/100000000000))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (scalarOccupation x) criticalActivity (by convert hq using 1; norm_num) (by convert criticalActivity_bounds using 1; norm_num)
  have hri : criticalActivity*(1-scalarOccupation x)/scalarOccupation x∈Set.Icc
      (((137157629792746615191/7633173100000000000) : ℚ) : ℝ) (((17145636895628834989/954087100000000000) : ℚ) : ℝ) := by
    norm_num at hr ⊢
    exact hr
  have hly := logarithm_enclosure (137157629792746615191/7633173100000000000) (17145636895628834989/954087100000000000) (1444313608219/500000000000) (1444372022369/500000000000) (-4) (-4) 14
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [scaledLogLower,logApproximation,logRemainder,Finset.sum_range_succ])
    (by norm_num [scaledLogUpper,logApproximation,logRemainder,Finset.sum_range_succ])
    (criticalActivity*(1-scalarOccupation x)/scalarOccupation x) (hri)
  have hyi : remainingPotential x∈Set.Icc (2.888627216438) (2.888744044738) := by
    rw [remainingPotential_eq_log_div x hx,occupation_remaining_ratio x hx]
    norm_num at hly ⊢
    exact hly
  have hz := cubicCenter_tight_bounds
  have hm : (scalarOccupation x)*(scalarOccupation x)*(remainingPotential x*
      (1+0.016*((remainingPotential x-cubicCenter)*(remainingPotential x-cubicCenter))))<1*x := by
    dyadic_interval +kernel [prec := 80]
  convert hm using 1; simp [scalarPartitionFunction,hx.ne',potential,cubicPotential,cubicCoefficient,pow_two]; norm_num

theorem scalar_box_0530 (x : ℝ) (hx : 0<x)
    (hq : scalarOccupation x∈Set.Icc 0.465891912841796875 0.46592098388671875) :
    scalarPartitionFunction x<1*x := by
  have hc : 1-scalarOccupation x∈Set.Icc (((43751753/81920000) : ℚ) : ℝ) (((87508269/163840000) : ℚ) : ℝ) := by
    norm_num
    constructor <;> linarith [hq.1,hq.2]
  have hlx := logarithm_enclosure (43751753/81920000) (87508269/163840000) (-627211480719/1000000000000) (-125431410019/200000000000) (1) (1) 14
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [scaledLogLower,logApproximation,logRemainder,Finset.sum_range_succ])
    (by norm_num [scaledLogUpper,logApproximation,logRemainder,Finset.sum_range_succ])
    (1-scalarOccupation x) (hc)
  have hxi : x∈Set.Icc 0.627157050095 0.627211480719 := by
    have he := occupation_log_identity x
    norm_num at hlx
    constructor <;> linarith [hlx.1,hlx.2]
  have hr := remaining_ratio_bounds ((76331731/163840000)) ((38168247/81920000)) ((1567367648339/100000000000)) ((1567367648341/100000000000))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (scalarOccupation x) criticalActivity (by convert hq using 1; norm_num) (by convert criticalActivity_bounds using 1; norm_num)
  have hri : criticalActivity*(1-scalarOccupation x)/scalarOccupation x∈Set.Icc
      (((2981525313492121229/165948900000000000) : ℚ) : ℝ) (((137157629792921631729/7633173100000000000) : ℚ) : ℝ) := by
    norm_num at hr ⊢
    exact hr
  have hly := logarithm_enclosure (2981525313492121229/165948900000000000) (137157629792921631729/7633173100000000000) (180531899317/62500000000) (2888627216441/1000000000000) (-4) (-4) 14
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [scaledLogLower,logApproximation,logRemainder,Finset.sum_range_succ])
    (by norm_num [scaledLogUpper,logApproximation,logRemainder,Finset.sum_range_succ])
    (criticalActivity*(1-scalarOccupation x)/scalarOccupation x) (hri)
  have hyi : remainingPotential x∈Set.Icc (2.888510389072) (2.888627216441) := by
    rw [remainingPotential_eq_log_div x hx,occupation_remaining_ratio x hx]
    norm_num at hly ⊢
    exact hly
  have hz := cubicCenter_tight_bounds
  have hm : (scalarOccupation x)*(scalarOccupation x)*(remainingPotential x*
      (1+0.016*((remainingPotential x-cubicCenter)*(remainingPotential x-cubicCenter))))<1*x := by
    dyadic_interval +kernel [prec := 80]
  convert hm using 1; simp [scalarPartitionFunction,hx.ne',potential,cubicPotential,cubicCoefficient,pow_two]; norm_num

theorem scalar_box_0531 (x : ℝ) (hx : 0<x)
    (hq : scalarOccupation x∈Set.Icc 0.46592098388671875 0.465950054931640625) :
    scalarPartitionFunction x<1*x := by
  have hc : 1-scalarOccupation x∈Set.Icc (((87498743/163840000) : ℚ) : ℝ) (((43751753/81920000) : ℚ) : ℝ) := by
    norm_num
    constructor <;> linarith [hq.1,hq.2]
  have hlx := logarithm_enclosure (87498743/163840000) (43751753/81920000) (-313632957153/500000000000) (-313605740359/500000000000) (1) (1) 14
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [scaledLogLower,logApproximation,logRemainder,Finset.sum_range_succ])
    (by norm_num [scaledLogUpper,logApproximation,logRemainder,Finset.sum_range_succ])
    (1-scalarOccupation x) (hc)
  have hxi : x∈Set.Icc 0.627211480718 0.627265914306 := by
    have he := occupation_log_identity x
    norm_num at hlx
    constructor <;> linarith [hlx.1,hlx.2]
  have hr := remaining_ratio_bounds ((38168247/81920000)) ((76341257/163840000)) ((1567367648339/100000000000)) ((1567367648341/100000000000))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (scalarOccupation x) criticalActivity (by convert hq using 1; norm_num) (by convert criticalActivity_bounds using 1; norm_num)
  have hri : criticalActivity*(1-scalarOccupation x)/scalarOccupation x∈Set.Icc
      (((137142699048528537877/7634125700000000000) : ℚ) : ℝ) (((68575082210406291773/3816824700000000000) : ℚ) : ℝ) := by
    norm_num at hr ⊢
    exact hr
  have hly := logarithm_enclosure (137142699048528537877/7634125700000000000) (68575082210406291773/3816824700000000000) (722098390659/250000000000) (1444255194537/500000000000) (-4) (-4) 14
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [scaledLogLower,logApproximation,logRemainder,Finset.sum_range_succ])
    (by norm_num [scaledLogUpper,logApproximation,logRemainder,Finset.sum_range_succ])
    (criticalActivity*(1-scalarOccupation x)/scalarOccupation x) (hri)
  have hyi : remainingPotential x∈Set.Icc (2.888393562636) (2.888510389074) := by
    rw [remainingPotential_eq_log_div x hx,occupation_remaining_ratio x hx]
    norm_num at hly ⊢
    exact hly
  have hz := cubicCenter_tight_bounds
  have hm : (scalarOccupation x)*(scalarOccupation x)*(remainingPotential x*
      (1+0.016*((remainingPotential x-cubicCenter)*(remainingPotential x-cubicCenter))))<1*x := by
    dyadic_interval +kernel [prec := 80]
  convert hm using 1; simp [scalarPartitionFunction,hx.ne',potential,cubicPotential,cubicCoefficient,pow_two]; norm_num

theorem scalar_box_0532 (x : ℝ) (hx : 0<x)
    (hq : scalarOccupation x∈Set.Icc 0.465950054931640625 0.4659791259765625) :
    scalarPartitionFunction x<1*x := by
  have hc : 1-scalarOccupation x∈Set.Icc (((4374699/8192000) : ℚ) : ℝ) (((87498743/163840000) : ℚ) : ℝ) := by
    norm_num
    constructor <;> linarith [hq.1,hq.2]
  have hlx := logarithm_enclosure (4374699/8192000) (87498743/163840000) (-125464070171/200000000000) (-125453182861/200000000000) (1) (1) 14
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [scaledLogLower,logApproximation,logRemainder,Finset.sum_range_succ])
    (by norm_num [scaledLogUpper,logApproximation,logRemainder,Finset.sum_range_succ])
    (1-scalarOccupation x) (hc)
  have hxi : x∈Set.Icc 0.627265914305 0.627320350855 := by
    have he := occupation_log_identity x
    norm_num at hlx
    constructor <;> linarith [hlx.1,hlx.2]
  have hr := remaining_ratio_bounds ((76341257/163840000)) ((3817301/8192000)) ((1567367648339/100000000000)) ((1567367648341/100000000000))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (scalarOccupation x) criticalActivity (by convert hq using 1; norm_num) (by convert criticalActivity_bounds using 1; norm_num)
  have hri : criticalActivity*(1-scalarOccupation x)/scalarOccupation x∈Set.Icc
      (((6856761683820974961/381730100000000000) : ℚ) : ℝ) (((137142699048703535363/7634125700000000000) : ℚ) : ℝ) := by
    norm_num at hr ⊢
    exact hr
  have hly := logarithm_enclosure (6856761683820974961/381730100000000000) (137142699048703535363/7634125700000000000) (2888276737129/1000000000000) (1444196781319/500000000000) (-4) (-4) 14
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [scaledLogLower,logApproximation,logRemainder,Finset.sum_range_succ])
    (by norm_num [scaledLogUpper,logApproximation,logRemainder,Finset.sum_range_succ])
    (criticalActivity*(1-scalarOccupation x)/scalarOccupation x) (hri)
  have hyi : remainingPotential x∈Set.Icc (2.888276737129) (2.888393562638) := by
    rw [remainingPotential_eq_log_div x hx,occupation_remaining_ratio x hx]
    norm_num at hly ⊢
    exact hly
  have hz := cubicCenter_tight_bounds
  have hm : (scalarOccupation x)*(scalarOccupation x)*(remainingPotential x*
      (1+0.016*((remainingPotential x-cubicCenter)*(remainingPotential x-cubicCenter))))<1*x := by
    dyadic_interval +kernel [prec := 80]
  convert hm using 1; simp [scalarPartitionFunction,hx.ne',potential,cubicPotential,cubicCoefficient,pow_two]; norm_num

theorem scalar_box_0533 (x : ℝ) (hx : 0<x)
    (hq : scalarOccupation x∈Set.Icc 0.4659791259765625 0.466008197021484375) :
    scalarPartitionFunction x<1*x := by
  have hc : 1-scalarOccupation x∈Set.Icc (((87489217/163840000) : ℚ) : ℝ) (((4374699/8192000) : ℚ) : ℝ) := by
    norm_num
    constructor <;> linarith [hq.1,hq.2]
  have hlx := logarithm_enclosure (87489217/163840000) (4374699/8192000) (-19605462199/31250000000) (-313660175427/500000000000) (1) (1) 14
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [scaledLogLower,logApproximation,logRemainder,Finset.sum_range_succ])
    (by norm_num [scaledLogUpper,logApproximation,logRemainder,Finset.sum_range_succ])
    (1-scalarOccupation x) (hc)
  have hxi : x∈Set.Icc 0.627320350854 0.627374790368 := by
    have he := occupation_log_identity x
    norm_num at hlx
    constructor <;> linarith [hlx.1,hlx.2]
  have hr := remaining_ratio_bounds ((3817301/8192000)) ((76350783/163840000)) ((1567367648339/100000000000)) ((1567367648341/100000000000))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (scalarOccupation x) criticalActivity (by convert hq using 1; norm_num) (by convert criticalActivity_bounds using 1; norm_num)
  have hri : criticalActivity*(1-scalarOccupation x)/scalarOccupation x∈Set.Icc
      (((137127768304310460563/7635078300000000000) : ℚ) : ℝ) (((6856761683829724359/381730100000000000) : ℚ) : ℝ) := by
    norm_num at hr ⊢
    exact hr
  have hly := logarithm_enclosure (137127768304310460563/7635078300000000000) (6856761683829724359/381730100000000000) (2888159912551/1000000000000) (722069184283/250000000000) (-4) (-4) 14
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [scaledLogLower,logApproximation,logRemainder,Finset.sum_range_succ])
    (by norm_num [scaledLogUpper,logApproximation,logRemainder,Finset.sum_range_succ])
    (criticalActivity*(1-scalarOccupation x)/scalarOccupation x) (hri)
  have hyi : remainingPotential x∈Set.Icc (2.888159912551) (2.888276737132) := by
    rw [remainingPotential_eq_log_div x hx,occupation_remaining_ratio x hx]
    norm_num at hly ⊢
    exact hly
  have hz := cubicCenter_tight_bounds
  have hm : (scalarOccupation x)*(scalarOccupation x)*(remainingPotential x*
      (1+0.016*((remainingPotential x-cubicCenter)*(remainingPotential x-cubicCenter))))<1*x := by
    dyadic_interval +kernel [prec := 80]
  convert hm using 1; simp [scalarPartitionFunction,hx.ne',potential,cubicPotential,cubicCoefficient,pow_two]; norm_num

theorem scalar_box_0534 (x : ℝ) (hx : 0<x)
    (hq : scalarOccupation x∈Set.Icc 0.466008197021484375 0.46603726806640625) :
    scalarPartitionFunction x<1*x := by
  have hc : 1-scalarOccupation x∈Set.Icc (((43742227/81920000) : ℚ) : ℝ) (((87489217/163840000) : ℚ) : ℝ) := by
    norm_num
    constructor <;> linarith [hq.1,hq.2]
  have hlx := logarithm_enclosure (43742227/81920000) (87489217/163840000) (-156857308211/250000000000) (-627374790367/1000000000000) (1) (1) 14
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [scaledLogLower,logApproximation,logRemainder,Finset.sum_range_succ])
    (by norm_num [scaledLogUpper,logApproximation,logRemainder,Finset.sum_range_succ])
    (1-scalarOccupation x) (hc)
  have hxi : x∈Set.Icc 0.627374790367 0.627429232844 := by
    have he := occupation_log_identity x
    norm_num at hlx
    constructor <;> linarith [hlx.1,hlx.2]
  have hr := remaining_ratio_bounds ((76350783/163840000)) ((38177773/81920000)) ((1567367648339/100000000000)) ((1567367648341/100000000000))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (scalarOccupation x) criticalActivity (by convert hq using 1; norm_num) (by convert criticalActivity_bounds using 1; norm_num)
  have hri : criticalActivity*(1-scalarOccupation x)/scalarOccupation x∈Set.Icc
      (((68560151466100710953/3817777300000000000) : ℚ) : ℝ) (((137127768304485438997/7635078300000000000) : ℚ) : ℝ) := by
    norm_num at hr ⊢
    exact hr
  have hly := logarithm_enclosure (68560151466100710953/3817777300000000000) (137127768304485438997/7635078300000000000) (2888043088901/1000000000000) (1444079956277/500000000000) (-4) (-4) 14
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [scaledLogLower,logApproximation,logRemainder,Finset.sum_range_succ])
    (by norm_num [scaledLogUpper,logApproximation,logRemainder,Finset.sum_range_succ])
    (criticalActivity*(1-scalarOccupation x)/scalarOccupation x) (hri)
  have hyi : remainingPotential x∈Set.Icc (2.888043088901) (2.888159912554) := by
    rw [remainingPotential_eq_log_div x hx,occupation_remaining_ratio x hx]
    norm_num at hly ⊢
    exact hly
  have hz := cubicCenter_tight_bounds
  have hm : (scalarOccupation x)*(scalarOccupation x)*(remainingPotential x*
      (1+0.016*((remainingPotential x-cubicCenter)*(remainingPotential x-cubicCenter))))<1*x := by
    dyadic_interval +kernel [prec := 80]
  convert hm using 1; simp [scalarPartitionFunction,hx.ne',potential,cubicPotential,cubicCoefficient,pow_two]; norm_num

theorem scalar_box_0535 (x : ℝ) (hx : 0<x)
    (hq : scalarOccupation x∈Set.Icc 0.46603726806640625 0.466066339111328125) :
    scalarPartitionFunction x<1*x := by
  have hc : 1-scalarOccupation x∈Set.Icc (((87479691/163840000) : ℚ) : ℝ) (((43742227/81920000) : ℚ) : ℝ) := by
    norm_num
    constructor <;> linarith [hq.1,hq.2]
  have hlx := logarithm_enclosure (87479691/163840000) (43742227/81920000) (-125496735657/200000000000) (-627429232843/1000000000000) (1) (1) 14
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [scaledLogLower,logApproximation,logRemainder,Finset.sum_range_succ])
    (by norm_num [scaledLogUpper,logApproximation,logRemainder,Finset.sum_range_succ])
    (1-scalarOccupation x) (hc)
  have hxi : x∈Set.Icc 0.627429232843 0.627483678285 := by
    have he := occupation_log_identity x
    norm_num at hlx
    constructor <;> linarith [hlx.1,hlx.2]
  have hr := remaining_ratio_bounds ((38177773/81920000)) ((76360309/163840000)) ((1567367648339/100000000000)) ((1567367648341/100000000000))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (scalarOccupation x) criticalActivity (by convert hq using 1; norm_num) (by convert criticalActivity_bounds using 1; norm_num)
  have hri : criticalActivity*(1-scalarOccupation x)/scalarOccupation x∈Set.Icc
      (((137112837560092383249/7636030900000000000) : ℚ) : ℝ) (((68560151466188195407/3817777300000000000) : ℚ) : ℝ) := by
    norm_num at hr ⊢
    exact hr
  have hly := logarithm_enclosure (137112837560092383249/7636030900000000000) (68560151466188195407/3817777300000000000) (1443963133089/500000000000) (361005386113/125000000000) (-4) (-4) 14
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [scaledLogLower,logApproximation,logRemainder,Finset.sum_range_succ])
    (by norm_num [scaledLogUpper,logApproximation,logRemainder,Finset.sum_range_succ])
    (criticalActivity*(1-scalarOccupation x)/scalarOccupation x) (hri)
  have hyi : remainingPotential x∈Set.Icc (2.887926266178) (2.888043088904) := by
    rw [remainingPotential_eq_log_div x hx,occupation_remaining_ratio x hx]
    norm_num at hly ⊢
    exact hly
  have hz := cubicCenter_tight_bounds
  have hm : (scalarOccupation x)*(scalarOccupation x)*(remainingPotential x*
      (1+0.016*((remainingPotential x-cubicCenter)*(remainingPotential x-cubicCenter))))<1*x := by
    dyadic_interval +kernel [prec := 80]
  convert hm using 1; simp [scalarPartitionFunction,hx.ne',potential,cubicPotential,cubicCoefficient,pow_two]; norm_num

theorem scalar_box_0536 (x : ℝ) (hx : 0<x)
    (hq : scalarOccupation x∈Set.Icc 0.466066339111328125 0.46609541015625) :
    scalarPartitionFunction x<1*x := by
  have hc : 1-scalarOccupation x∈Set.Icc (((5467183/10240000) : ℚ) : ℝ) (((87479691/163840000) : ℚ) : ℝ) := by
    norm_num
    constructor <;> linarith [hq.1,hq.2]
  have hlx := logarithm_enclosure (5467183/10240000) (87479691/163840000) (-627538126691/1000000000000) (-156870919571/250000000000) (1) (1) 14
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [scaledLogLower,logApproximation,logRemainder,Finset.sum_range_succ])
    (by norm_num [scaledLogUpper,logApproximation,logRemainder,Finset.sum_range_succ])
    (1-scalarOccupation x) (hc)
  have hxi : x∈Set.Icc 0.627483678284 0.627538126691 := by
    have he := occupation_log_identity x
    norm_num at hlx
    constructor <;> linarith [hlx.1,hlx.2]
  have hr := remaining_ratio_bounds ((76360309/163840000)) ((4772817/10240000)) ((1567367648339/100000000000)) ((1567367648341/100000000000))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (scalarOccupation x) criticalActivity (by convert hq using 1; norm_num) (by convert criticalActivity_bounds using 1; norm_num)
  have hri : criticalActivity*(1-scalarOccupation x)/scalarOccupation x∈Set.Icc
      (((8569085761748959037/477281700000000000) : ℚ) : ℝ) (((137112837560267342631/7636030900000000000) : ℚ) : ℝ) := by
    norm_num at hr ⊢
    exact hr
  have hly := logarithm_enclosure (8569085761748959037/477281700000000000) (137112837560267342631/7636030900000000000) (2887809444381/1000000000000) (144396313309/50000000000) (-4) (-4) 14
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [scaledLogLower,logApproximation,logRemainder,Finset.sum_range_succ])
    (by norm_num [scaledLogUpper,logApproximation,logRemainder,Finset.sum_range_succ])
    (criticalActivity*(1-scalarOccupation x)/scalarOccupation x) (hri)
  have hyi : remainingPotential x∈Set.Icc (2.887809444381) (2.88792626618) := by
    rw [remainingPotential_eq_log_div x hx,occupation_remaining_ratio x hx]
    norm_num at hly ⊢
    exact hly
  have hz := cubicCenter_tight_bounds
  have hm : (scalarOccupation x)*(scalarOccupation x)*(remainingPotential x*
      (1+0.016*((remainingPotential x-cubicCenter)*(remainingPotential x-cubicCenter))))<1*x := by
    dyadic_interval +kernel [prec := 80]
  convert hm using 1; simp [scalarPartitionFunction,hx.ne',potential,cubicPotential,cubicCoefficient,pow_two]; norm_num

theorem scalar_box_0537 (x : ℝ) (hx : 0<x)
    (hq : scalarOccupation x∈Set.Icc 0.46609541015625 0.466124481201171875) :
    scalarPartitionFunction x<1*x := by
  have hc : 1-scalarOccupation x∈Set.Icc (((17494033/32768000) : ℚ) : ℝ) (((5467183/10240000) : ℚ) : ℝ) := by
    norm_num
    constructor <;> linarith [hq.1,hq.2]
  have hlx := logarithm_enclosure (17494033/32768000) (5467183/10240000) (-627592578061/1000000000000) (-62753812669/100000000000) (1) (1) 14
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [scaledLogLower,logApproximation,logRemainder,Finset.sum_range_succ])
    (by norm_num [scaledLogUpper,logApproximation,logRemainder,Finset.sum_range_succ])
    (1-scalarOccupation x) (hc)
  have hxi : x∈Set.Icc 0.62753812669 0.627592578061 := by
    have he := occupation_log_identity x
    norm_num at hlx
    constructor <;> linarith [hlx.1,hlx.2]
  have hr := remaining_ratio_bounds ((4772817/10240000)) ((15273967/32768000)) ((1567367648339/100000000000)) ((1567367648341/100000000000))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (scalarOccupation x) criticalActivity (by convert hq using 1; norm_num) (by convert criticalActivity_bounds using 1; norm_num)
  have hri : criticalActivity*(1-scalarOccupation x)/scalarOccupation x∈Set.Icc
      (((27419581363174861187/1527396700000000000) : ℚ) : ℝ) (((8569085761759893403/477281700000000000) : ℚ) : ℝ) := by
    norm_num at hr ⊢
    exact hr
  have hly := logarithm_enclosure (27419581363174861187/1527396700000000000) (8569085761759893403/477281700000000000) (288769262351/100000000000) (2887809444383/1000000000000) (-4) (-4) 14
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [scaledLogLower,logApproximation,logRemainder,Finset.sum_range_succ])
    (by norm_num [scaledLogUpper,logApproximation,logRemainder,Finset.sum_range_succ])
    (criticalActivity*(1-scalarOccupation x)/scalarOccupation x) (hri)
  have hyi : remainingPotential x∈Set.Icc (2.88769262351) (2.887809444383) := by
    rw [remainingPotential_eq_log_div x hx,occupation_remaining_ratio x hx]
    norm_num at hly ⊢
    exact hly
  have hz := cubicCenter_tight_bounds
  have hm : (scalarOccupation x)*(scalarOccupation x)*(remainingPotential x*
      (1+0.016*((remainingPotential x-cubicCenter)*(remainingPotential x-cubicCenter))))<1*x := by
    dyadic_interval +kernel [prec := 80]
  convert hm using 1; simp [scalarPartitionFunction,hx.ne',potential,cubicPotential,cubicCoefficient,pow_two]; norm_num

theorem scalar_box_0538 (x : ℝ) (hx : 0<x)
    (hq : scalarOccupation x∈Set.Icc 0.466124481201171875 0.46615355224609375) :
    scalarPartitionFunction x<1*x := by
  have hc : 1-scalarOccupation x∈Set.Icc (((43732701/81920000) : ℚ) : ℝ) (((17494033/32768000) : ℚ) : ℝ) := by
    norm_num
    constructor <;> linarith [hq.1,hq.2]
  have hlx := logarithm_enclosure (43732701/81920000) (17494033/32768000) (-156911758099/250000000000) (-31379628903/50000000000) (1) (1) 14
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [scaledLogLower,logApproximation,logRemainder,Finset.sum_range_succ])
    (by norm_num [scaledLogUpper,logApproximation,logRemainder,Finset.sum_range_succ])
    (1-scalarOccupation x) (hc)
  have hxi : x∈Set.Icc 0.62759257806 0.627647032396 := by
    have he := occupation_log_identity x
    norm_num at hlx
    constructor <;> linarith [hlx.1,hlx.2]
  have hr := remaining_ratio_bounds ((15273967/32768000)) ((38187299/81920000)) ((1567367648339/100000000000)) ((1567367648341/100000000000))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (scalarOccupation x) criticalActivity (by convert hq using 1; norm_num) (by convert criticalActivity_bounds using 1; norm_num)
  have hri : criticalActivity*(1-scalarOccupation x)/scalarOccupation x∈Set.Icc
      (((68545220721882633639/3818729900000000000) : ℚ) : ℝ) (((27419581363209849253/1527396700000000000) : ℚ) : ℝ) := by
    norm_num at hr ⊢
    exact hr
  have hly := logarithm_enclosure (68545220721882633639/3818729900000000000) (27419581363209849253/1527396700000000000) (2887575803563/1000000000000) (360961577939/125000000000) (-4) (-4) 14
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [scaledLogLower,logApproximation,logRemainder,Finset.sum_range_succ])
    (by norm_num [scaledLogUpper,logApproximation,logRemainder,Finset.sum_range_succ])
    (criticalActivity*(1-scalarOccupation x)/scalarOccupation x) (hri)
  have hyi : remainingPotential x∈Set.Icc (2.887575803563) (2.887692623512) := by
    rw [remainingPotential_eq_log_div x hx,occupation_remaining_ratio x hx]
    norm_num at hly ⊢
    exact hly
  have hz := cubicCenter_tight_bounds
  have hm : (scalarOccupation x)*(scalarOccupation x)*(remainingPotential x*
      (1+0.016*((remainingPotential x-cubicCenter)*(remainingPotential x-cubicCenter))))<1*x := by
    dyadic_interval +kernel [prec := 80]
  convert hm using 1; simp [scalarPartitionFunction,hx.ne',potential,cubicPotential,cubicCoefficient,pow_two]; norm_num

theorem scalar_box_0539 (x : ℝ) (hx : 0<x)
    (hq : scalarOccupation x∈Set.Icc 0.46615355224609375 0.466182623291015625) :
    scalarPartitionFunction x<1*x := by
  have hc : 1-scalarOccupation x∈Set.Icc (((87460639/163840000) : ℚ) : ℝ) (((43732701/81920000) : ℚ) : ℝ) := by
    norm_num
    constructor <;> linarith [hq.1,hq.2]
  have hlx := logarithm_enclosure (87460639/163840000) (43732701/81920000) (-19615671553/31250000000) (-125529406479/200000000000) (1) (1) 14
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [scaledLogLower,logApproximation,logRemainder,Finset.sum_range_succ])
    (by norm_num [scaledLogUpper,logApproximation,logRemainder,Finset.sum_range_succ])
    (1-scalarOccupation x) (hc)
  have hxi : x∈Set.Icc 0.627647032395 0.627701489696 := by
    have he := occupation_log_identity x
    norm_num at hlx
    constructor <;> linarith [hlx.1,hlx.2]
  have hr := remaining_ratio_bounds ((38187299/81920000)) ((76379361/163840000)) ((1567367648339/100000000000)) ((1567367648341/100000000000))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (scalarOccupation x) criticalActivity (by convert hq using 1; norm_num) (by convert criticalActivity_bounds using 1; norm_num)
  have hri : criticalActivity*(1-scalarOccupation x)/scalarOccupation x∈Set.Icc
      (((137082976071656228621/7637936100000000000) : ℚ) : ℝ) (((68545220721970099041/3818729900000000000) : ℚ) : ℝ) := by
    norm_num at hr ⊢
    exact hr
  have hly := logarithm_enclosure (137082976071656228621/7637936100000000000) (68545220721970099041/3818729900000000000) (2887458984539/1000000000000) (577515160713/200000000000) (-4) (-4) 14
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [scaledLogLower,logApproximation,logRemainder,Finset.sum_range_succ])
    (by norm_num [scaledLogUpper,logApproximation,logRemainder,Finset.sum_range_succ])
    (criticalActivity*(1-scalarOccupation x)/scalarOccupation x) (hri)
  have hyi : remainingPotential x∈Set.Icc (2.887458984539) (2.887575803565) := by
    rw [remainingPotential_eq_log_div x hx,occupation_remaining_ratio x hx]
    norm_num at hly ⊢
    exact hly
  have hz := cubicCenter_tight_bounds
  have hm : (scalarOccupation x)*(scalarOccupation x)*(remainingPotential x*
      (1+0.016*((remainingPotential x-cubicCenter)*(remainingPotential x-cubicCenter))))<1*x := by
    dyadic_interval +kernel [prec := 80]
  convert hm using 1; simp [scalarPartitionFunction,hx.ne',potential,cubicPotential,cubicCoefficient,pow_two]; norm_num

theorem scalar_box_0540 (x : ℝ) (hx : 0<x)
    (hq : scalarOccupation x∈Set.Icc 0.466182623291015625 0.4662116943359375) :
    scalarPartitionFunction x<1*x := by
  have hc : 1-scalarOccupation x∈Set.Icc (((21863969/40960000) : ℚ) : ℝ) (((87460639/163840000) : ℚ) : ℝ) := by
    norm_num
    constructor <;> linarith [hq.1,hq.2]
  have hlx := logarithm_enclosure (21863969/40960000) (87460639/163840000) (-627755949963/1000000000000) (-125540297939/200000000000) (1) (1) 14
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [scaledLogLower,logApproximation,logRemainder,Finset.sum_range_succ])
    (by norm_num [scaledLogUpper,logApproximation,logRemainder,Finset.sum_range_succ])
    (1-scalarOccupation x) (hc)
  have hxi : x∈Set.Icc 0.627701489695 0.627755949963 := by
    have he := occupation_log_identity x
    norm_num at hlx
    constructor <;> linarith [hlx.1,hlx.2]
  have hr := remaining_ratio_bounds ((76379361/163840000)) ((19096031/40960000)) ((1567367648339/100000000000)) ((1567367648341/100000000000))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (scalarOccupation x) criticalActivity (by convert hq using 1; norm_num) (by convert criticalActivity_bounds using 1; norm_num)
  have hri : criticalActivity*(1-scalarOccupation x)/scalarOccupation x∈Set.Icc
      (((34268877674886797491/1909603100000000000) : ℚ) : ℝ) (((137082976071831149899/7637936100000000000) : ℚ) : ℝ) := by
    norm_num at hr ⊢
    exact hr
  have hly := logarithm_enclosure (34268877674886797491/1909603100000000000) (137082976071831149899/7637936100000000000) (2887342166439/1000000000000) (1443729492271/500000000000) (-4) (-4) 14
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [scaledLogLower,logApproximation,logRemainder,Finset.sum_range_succ])
    (by norm_num [scaledLogUpper,logApproximation,logRemainder,Finset.sum_range_succ])
    (criticalActivity*(1-scalarOccupation x)/scalarOccupation x) (hri)
  have hyi : remainingPotential x∈Set.Icc (2.887342166439) (2.887458984542) := by
    rw [remainingPotential_eq_log_div x hx,occupation_remaining_ratio x hx]
    norm_num at hly ⊢
    exact hly
  have hz := cubicCenter_tight_bounds
  have hm : (scalarOccupation x)*(scalarOccupation x)*(remainingPotential x*
      (1+0.016*((remainingPotential x-cubicCenter)*(remainingPotential x-cubicCenter))))<1*x := by
    dyadic_interval +kernel [prec := 80]
  convert hm using 1; simp [scalarPartitionFunction,hx.ne',potential,cubicPotential,cubicCoefficient,pow_two]; norm_num

theorem scalar_box_0541 (x : ℝ) (hx : 0<x)
    (hq : scalarOccupation x∈Set.Icc 0.4662116943359375 0.466240765380859375) :
    scalarPartitionFunction x<1*x := by
  have hc : 1-scalarOccupation x∈Set.Icc (((87451113/163840000) : ℚ) : ℝ) (((21863969/40960000) : ℚ) : ℝ) := by
    norm_num
    constructor <;> linarith [hq.1,hq.2]
  have hlx := logarithm_enclosure (87451113/163840000) (21863969/40960000) (-125562082639/200000000000) (-313877974981/500000000000) (1) (1) 14
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [scaledLogLower,logApproximation,logRemainder,Finset.sum_range_succ])
    (by norm_num [scaledLogUpper,logApproximation,logRemainder,Finset.sum_range_succ])
    (1-scalarOccupation x) (hc)
  have hxi : x∈Set.Icc 0.627755949962 0.627810413195 := by
    have he := occupation_log_identity x
    norm_num at hlx
    constructor <;> linarith [hlx.1,hlx.2]
  have hr := remaining_ratio_bounds ((19096031/40960000)) ((76388887/163840000)) ((1567367648339/100000000000)) ((1567367648341/100000000000))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (scalarOccupation x) criticalActivity (by convert hq using 1; norm_num) (by convert criticalActivity_bounds using 1; norm_num)
  have hri : criticalActivity*(1-scalarOccupation x)/scalarOccupation x∈Set.Icc
      (((137068045327438151307/7638888700000000000) : ℚ) : ℝ) (((34268877674930525429/1909603100000000000) : ℚ) : ℝ) := by
    norm_num at hr ⊢
    exact hr
  have hly := logarithm_enclosure (137068045327438151307/7638888700000000000) (34268877674930525429/1909603100000000000) (2887225349261/1000000000000) (1443671083221/500000000000) (-4) (-4) 14
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [scaledLogLower,logApproximation,logRemainder,Finset.sum_range_succ])
    (by norm_num [scaledLogUpper,logApproximation,logRemainder,Finset.sum_range_succ])
    (criticalActivity*(1-scalarOccupation x)/scalarOccupation x) (hri)
  have hyi : remainingPotential x∈Set.Icc (2.887225349261) (2.887342166442) := by
    rw [remainingPotential_eq_log_div x hx,occupation_remaining_ratio x hx]
    norm_num at hly ⊢
    exact hly
  have hz := cubicCenter_tight_bounds
  have hm : (scalarOccupation x)*(scalarOccupation x)*(remainingPotential x*
      (1+0.016*((remainingPotential x-cubicCenter)*(remainingPotential x-cubicCenter))))<1*x := by
    dyadic_interval +kernel [prec := 80]
  convert hm using 1; simp [scalarPartitionFunction,hx.ne',potential,cubicPotential,cubicCoefficient,pow_two]; norm_num

theorem scalar_box_0542 (x : ℝ) (hx : 0<x)
    (hq : scalarOccupation x∈Set.Icc 0.466240765380859375 0.46626983642578125) :
    scalarPartitionFunction x<1*x := by
  have hc : 1-scalarOccupation x∈Set.Icc (((1748927/3276800) : ℚ) : ℝ) (((87451113/163840000) : ℚ) : ℝ) := by
    norm_num
    constructor <;> linarith [hq.1,hq.2]
  have hlx := logarithm_enclosure (1748927/3276800) (87451113/163840000) (-313932439697/500000000000) (-313905206597/500000000000) (1) (1) 14
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [scaledLogLower,logApproximation,logRemainder,Finset.sum_range_succ])
    (by norm_num [scaledLogUpper,logApproximation,logRemainder,Finset.sum_range_succ])
    (1-scalarOccupation x) (hc)
  have hxi : x∈Set.Icc 0.627810413194 0.627864879394 := by
    have he := occupation_log_identity x
    norm_num at hlx
    constructor <;> linarith [hlx.1,hlx.2]
  have hr := remaining_ratio_bounds ((76388887/163840000)) ((1527873/3276800)) ((1567367648339/100000000000)) ((1567367648341/100000000000))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (scalarOccupation x) criticalActivity (by convert hq using 1; norm_num) (by convert criticalActivity_bounds using 1; norm_num)
  have hri : criticalActivity*(1-scalarOccupation x)/scalarOccupation x∈Set.Icc
      (((2741211599106582253/152787300000000000) : ℚ) : ℝ) (((137068045327613053533/7638888700000000000) : ℚ) : ℝ) := by
    norm_num at hr ⊢
    exact hr
  have hly := logarithm_enclosure (2741211599106582253/152787300000000000) (137068045327613053533/7638888700000000000) (577421706601/200000000000) (180451584329/62500000000) (-4) (-4) 14
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [scaledLogLower,logApproximation,logRemainder,Finset.sum_range_succ])
    (by norm_num [scaledLogUpper,logApproximation,logRemainder,Finset.sum_range_succ])
    (criticalActivity*(1-scalarOccupation x)/scalarOccupation x) (hri)
  have hyi : remainingPotential x∈Set.Icc (2.887108533005) (2.887225349264) := by
    rw [remainingPotential_eq_log_div x hx,occupation_remaining_ratio x hx]
    norm_num at hly ⊢
    exact hly
  have hz := cubicCenter_tight_bounds
  have hm : (scalarOccupation x)*(scalarOccupation x)*(remainingPotential x*
      (1+0.016*((remainingPotential x-cubicCenter)*(remainingPotential x-cubicCenter))))<1*x := by
    dyadic_interval +kernel [prec := 80]
  convert hm using 1; simp [scalarPartitionFunction,hx.ne',potential,cubicPotential,cubicCoefficient,pow_two]; norm_num

theorem scalar_box_0543 (x : ℝ) (hx : 0<x)
    (hq : scalarOccupation x∈Set.Icc 0.46626983642578125 0.466298907470703125) :
    scalarPartitionFunction x<1*x := by
  have hc : 1-scalarOccupation x∈Set.Icc (((87441587/163840000) : ℚ) : ℝ) (((1748927/3276800) : ℚ) : ℝ) := by
    norm_num
    constructor <;> linarith [hq.1,hq.2]
  have hlx := logarithm_enclosure (87441587/163840000) (1748927/3276800) (-7848991857/12500000000) (-627864879393/1000000000000) (1) (1) 14
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [scaledLogLower,logApproximation,logRemainder,Finset.sum_range_succ])
    (by norm_num [scaledLogUpper,logApproximation,logRemainder,Finset.sum_range_succ])
    (1-scalarOccupation x) (hc)
  have hxi : x∈Set.Icc 0.627864879393 0.62791934856 := by
    have he := occupation_log_identity x
    norm_num at hlx
    constructor <;> linarith [hlx.1,hlx.2]
  have hr := remaining_ratio_bounds ((1527873/3276800)) ((76398413/163840000)) ((1567367648339/100000000000)) ((1567367648341/100000000000))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (scalarOccupation x) criticalActivity (by convert hq using 1; norm_num) (by convert criticalActivity_bounds using 1; norm_num)
  have hri : criticalActivity*(1-scalarOccupation x)/scalarOccupation x∈Set.Icc
      (((137053114583220073993/7639841300000000000) : ℚ) : ℝ) (((2741211599110080107/152787300000000000) : ℚ) : ℝ) := by
    norm_num at hr ⊢
    exact hr
  have hly := logarithm_enclosure (137053114583220073993/7639841300000000000) (2741211599110080107/152787300000000000) (2886991717669/1000000000000) (2887108533007/1000000000000) (-4) (-4) 14
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [scaledLogLower,logApproximation,logRemainder,Finset.sum_range_succ])
    (by norm_num [scaledLogUpper,logApproximation,logRemainder,Finset.sum_range_succ])
    (criticalActivity*(1-scalarOccupation x)/scalarOccupation x) (hri)
  have hyi : remainingPotential x∈Set.Icc (2.886991717669) (2.887108533007) := by
    rw [remainingPotential_eq_log_div x hx,occupation_remaining_ratio x hx]
    norm_num at hly ⊢
    exact hly
  have hz := cubicCenter_tight_bounds
  have hm : (scalarOccupation x)*(scalarOccupation x)*(remainingPotential x*
      (1+0.016*((remainingPotential x-cubicCenter)*(remainingPotential x-cubicCenter))))<1*x := by
    dyadic_interval +kernel [prec := 80]
  convert hm using 1; simp [scalarPartitionFunction,hx.ne',potential,cubicPotential,cubicCoefficient,pow_two]; norm_num

end HardCoreActivityThreshold
