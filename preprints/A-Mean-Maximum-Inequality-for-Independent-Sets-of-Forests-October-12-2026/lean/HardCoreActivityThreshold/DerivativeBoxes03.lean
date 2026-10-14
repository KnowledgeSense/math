import HardCoreActivityThreshold.DerivativePolynomials

namespace HardCoreActivityThreshold
set_option maxHeartbeats 4000000
set_option maxRecDepth 8192

theorem fourth_box_0030 (x : ℝ) (hx : 0<x)
    (hq : scalarOccupation x∈Set.Icc 0.569921875 0.57421875) :
    0<fourthNumerator (scalarOccupation x) (remainingPotential x) := by
  have hc : 1-scalarOccupation x∈Set.Icc (((109/256) : ℚ) : ℝ) (((1101/2560) : ℚ) : ℝ) := by
    norm_num
    constructor <;> linarith [hq.1,hq.2]
  have hlx := logarithm_enclosure (109/256) (1101/2560) (-853829562251/1000000000000) (-3375153603/4000000000) (2) (2) 14
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [scaledLogLower,logApproximation,logRemainder,Finset.sum_range_succ])
    (by norm_num [scaledLogUpper,logApproximation,logRemainder,Finset.sum_range_succ])
    (1-scalarOccupation x) (hc)
  have hxi : x∈Set.Icc 0.84378840075 0.853829562251 := by
    have he := occupation_log_identity x
    norm_num at hlx
    constructor <;> linarith [hlx.1,hlx.2]
  have hr := remaining_ratio_bounds ((1459/2560)) ((147/256)) ((1567367648339/100000000000)) ((1567367648341/100000000000))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (scalarOccupation x) criticalActivity (by convert hq using 1; norm_num) (by convert criticalActivity_bounds using 1; norm_num)
  have hri : criticalActivity*(1-scalarOccupation x)/scalarOccupation x∈Set.Icc
      (((170843073668951/14700000000000) : ℚ) : ℝ) (((1725671780823441/145900000000000) : ℚ) : ℝ) := by
    norm_num at hr ⊢
    exact hr
  have hly := logarithm_enclosure (170843073668951/14700000000000) (1725671780823441/145900000000000) (2452897943533/1000000000000) (617612559071/250000000000) (-3) (-3) 14
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [scaledLogLower,logApproximation,logRemainder,Finset.sum_range_succ])
    (by norm_num [scaledLogUpper,logApproximation,logRemainder,Finset.sum_range_succ])
    (criticalActivity*(1-scalarOccupation x)/scalarOccupation x) (hri)
  have hyi : remainingPotential x∈Set.Icc 2.452897943533 2.470450236284 := by
    rw [remainingPotential_eq_log_div x hx,occupation_remaining_ratio x hx]
    norm_num at hly ⊢
    exact hly
  have hz := cubicCenter_tight_bounds
  rw [fourthNumerator_expanded]
  unfold expandedFourth
  dyadic_interval +kernel [prec := 80]

theorem fourth_box_0031 (x : ℝ) (hx : 0<x)
    (hq : scalarOccupation x∈Set.Icc 0.57421875 0.578515625) :
    0<fourthNumerator (scalarOccupation x) (remainingPotential x) := by
  have hc : 1-scalarOccupation x∈Set.Icc (((1079/2560) : ℚ) : ℝ) (((109/256) : ℚ) : ℝ) := by
    norm_num
    constructor <;> linarith [hq.1,hq.2]
  have hlx := logarithm_enclosure (1079/2560) (109/256) (-107996571527/125000000000) (-3415318249/4000000000) (2) (2) 14
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [scaledLogLower,logApproximation,logRemainder,Finset.sum_range_succ])
    (by norm_num [scaledLogUpper,logApproximation,logRemainder,Finset.sum_range_succ])
    (1-scalarOccupation x) (hc)
  have hxi : x∈Set.Icc 0.85382956225 0.863972572216 := by
    have he := occupation_log_identity x
    norm_num at hlx
    constructor <;> linarith [hlx.1,hlx.2]
  have hr := remaining_ratio_bounds ((147/256)) ((1481/2560)) ((1567367648339/100000000000)) ((1567367648341/100000000000))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (scalarOccupation x) criticalActivity (by convert hq using 1; norm_num) (by convert criticalActivity_bounds using 1; norm_num)
  have hri : criticalActivity*(1-scalarOccupation x)/scalarOccupation x∈Set.Icc
      (((1691189692557781/148100000000000) : ℚ) : ℝ) (((170843073669169/14700000000000) : ℚ) : ℝ) := by
    norm_num at hr ⊢
    exact hr
  have hly := logarithm_enclosure (1691189692557781/148100000000000) (170843073669169/14700000000000) (2435299799073/1000000000000) (490579588707/200000000000) (-3) (-3) 14
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [scaledLogLower,logApproximation,logRemainder,Finset.sum_range_succ])
    (by norm_num [scaledLogUpper,logApproximation,logRemainder,Finset.sum_range_succ])
    (criticalActivity*(1-scalarOccupation x)/scalarOccupation x) (hri)
  have hyi : remainingPotential x∈Set.Icc 2.435299799073 2.452897943535 := by
    rw [remainingPotential_eq_log_div x hx,occupation_remaining_ratio x hx]
    norm_num at hly ⊢
    exact hly
  have hz := cubicCenter_tight_bounds
  rw [fourthNumerator_expanded]
  unfold expandedFourth
  dyadic_interval +kernel [prec := 80]

theorem fourth_box_0032 (x : ℝ) (hx : 0<x)
    (hq : scalarOccupation x∈Set.Icc 0.578515625 0.5828125) :
    0<fourthNumerator (scalarOccupation x) (remainingPotential x) := by
  have hc : 1-scalarOccupation x∈Set.Icc (((267/640) : ℚ) : ℝ) (((1079/2560) : ℚ) : ℝ) := by
    norm_num
    constructor <;> linarith [hq.1,hq.2]
  have hlx := logarithm_enclosure (267/640) (1079/2560) (-437109758977/500000000000) (-172794514443/200000000000) (2) (2) 14
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [scaledLogLower,logApproximation,logRemainder,Finset.sum_range_succ])
    (by norm_num [scaledLogUpper,logApproximation,logRemainder,Finset.sum_range_succ])
    (1-scalarOccupation x) (hc)
  have hxi : x∈Set.Icc 0.863972572215 0.874219517954 := by
    have he := occupation_log_identity x
    norm_num at hlx
    constructor <;> linarith [hlx.1,hlx.2]
  have hr := remaining_ratio_bounds ((1481/2560)) ((373/640)) ((1567367648339/100000000000)) ((1567367648341/100000000000))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (scalarOccupation x) criticalActivity (by convert hq using 1; norm_num) (by convert criticalActivity_bounds using 1; norm_num)
  have hri : criticalActivity*(1-scalarOccupation x)/scalarOccupation x∈Set.Icc
      (((418487162106513/37300000000000) : ℚ) : ℝ) (((1691189692559939/148100000000000) : ℚ) : ℝ) := by
    norm_num at hr ⊢
    exact hr
  have hly := logarithm_enclosure (418487162106513/37300000000000) (1691189692559939/148100000000000) (2417652886839/1000000000000) (97411991963/40000000000) (-3) (-3) 14
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [scaledLogLower,logApproximation,logRemainder,Finset.sum_range_succ])
    (by norm_num [scaledLogUpper,logApproximation,logRemainder,Finset.sum_range_succ])
    (criticalActivity*(1-scalarOccupation x)/scalarOccupation x) (hri)
  have hyi : remainingPotential x∈Set.Icc 2.417652886839 2.435299799075 := by
    rw [remainingPotential_eq_log_div x hx,occupation_remaining_ratio x hx]
    norm_num at hly ⊢
    exact hly
  have hz := cubicCenter_tight_bounds
  rw [fourthNumerator_expanded]
  unfold expandedFourth
  dyadic_interval +kernel [prec := 80]

theorem fourth_box_0033 (x : ℝ) (hx : 0<x)
    (hq : scalarOccupation x∈Set.Icc 0.5828125 0.587109375) :
    0<fourthNumerator (scalarOccupation x) (remainingPotential x) := by
  have hc : 1-scalarOccupation x∈Set.Icc (((1057/2560) : ℚ) : ℝ) (((267/640) : ℚ) : ℝ) := by
    norm_num
    constructor <;> linarith [hq.1,hq.2]
  have hlx := logarithm_enclosure (1057/2560) (267/640) (-221143137901/250000000000) (-874219517953/1000000000000) (2) (2) 14
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [scaledLogLower,logApproximation,logRemainder,Finset.sum_range_succ])
    (by norm_num [scaledLogUpper,logApproximation,logRemainder,Finset.sum_range_succ])
    (1-scalarOccupation x) (hc)
  have hxi : x∈Set.Icc 0.874219517953 0.884572551604 := by
    have he := occupation_log_identity x
    norm_num at hlx
    constructor <;> linarith [hlx.1,hlx.2]
  have hr := remaining_ratio_bounds ((373/640)) ((1503/2560)) ((1567367648339/100000000000)) ((1567367648341/100000000000))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (scalarOccupation x) criticalActivity (by convert hq using 1; norm_num) (by convert criticalActivity_bounds using 1; norm_num)
  have hri : criticalActivity*(1-scalarOccupation x)/scalarOccupation x∈Set.Icc
      (((1656707604294323/150300000000000) : ℚ) : ℝ) (((418487162107047/37300000000000) : ℚ) : ℝ) := by
    norm_num at hr ⊢
    exact hr
  have hly := logarithm_enclosure (1656707604294323/150300000000000) (418487162107047/37300000000000) (2399954244199/1000000000000) (2417652886841/1000000000000) (-3) (-3) 14
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [scaledLogLower,logApproximation,logRemainder,Finset.sum_range_succ])
    (by norm_num [scaledLogUpper,logApproximation,logRemainder,Finset.sum_range_succ])
    (criticalActivity*(1-scalarOccupation x)/scalarOccupation x) (hri)
  have hyi : remainingPotential x∈Set.Icc 2.399954244199 2.417652886841 := by
    rw [remainingPotential_eq_log_div x hx,occupation_remaining_ratio x hx]
    norm_num at hly ⊢
    exact hly
  have hz := cubicCenter_tight_bounds
  rw [fourthNumerator_expanded]
  unfold expandedFourth
  dyadic_interval +kernel [prec := 80]

theorem fourth_box_0034 (x : ℝ) (hx : 0<x)
    (hq : scalarOccupation x∈Set.Icc 0.587109375 0.59140625) :
    0<fourthNumerator (scalarOccupation x) (remainingPotential x) := by
  have hc : 1-scalarOccupation x∈Set.Icc (((523/1280) : ℚ) : ℝ) (((1057/2560) : ℚ) : ℝ) := by
    norm_num
    constructor <;> linarith [hq.1,hq.2]
  have hlx := logarithm_enclosure (523/1280) (1057/2560) (-895033892849/1000000000000) (-884572551603/1000000000000) (2) (2) 14
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [scaledLogLower,logApproximation,logRemainder,Finset.sum_range_succ])
    (by norm_num [scaledLogUpper,logApproximation,logRemainder,Finset.sum_range_succ])
    (1-scalarOccupation x) (hc)
  have hxi : x∈Set.Icc 0.884572551603 0.895033892849 := by
    have he := occupation_log_identity x
    norm_num at hlx
    constructor <;> linarith [hlx.1,hlx.2]
  have hr := remaining_ratio_bounds ((1503/2560)) ((757/1280)) ((1567367648339/100000000000)) ((1567367648341/100000000000))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (scalarOccupation x) criticalActivity (by convert hq using 1; norm_num) (by convert criticalActivity_bounds using 1; norm_num)
  have hri : criticalActivity*(1-scalarOccupation x)/scalarOccupation x∈Set.Icc
      (((819733280081297/75700000000000) : ℚ) : ℝ) (((1656707604296437/150300000000000) : ℚ) : ℝ) := by
    norm_num at hr ⊢
    exact hr
  have hly := logarithm_enclosure (819733280081297/75700000000000) (1656707604296437/150300000000000) (238220085871/100000000000) (1199977122101/500000000000) (-3) (-3) 14
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [scaledLogLower,logApproximation,logRemainder,Finset.sum_range_succ])
    (by norm_num [scaledLogUpper,logApproximation,logRemainder,Finset.sum_range_succ])
    (criticalActivity*(1-scalarOccupation x)/scalarOccupation x) (hri)
  have hyi : remainingPotential x∈Set.Icc 2.38220085871 2.399954244202 := by
    rw [remainingPotential_eq_log_div x hx,occupation_remaining_ratio x hx]
    norm_num at hly ⊢
    exact hly
  have hz := cubicCenter_tight_bounds
  rw [fourthNumerator_expanded]
  unfold expandedFourth
  dyadic_interval +kernel [prec := 80]

theorem fourth_box_0035 (x : ℝ) (hx : 0<x)
    (hq : scalarOccupation x∈Set.Icc 0.59140625 0.595703125) :
    0<fourthNumerator (scalarOccupation x) (remainingPotential x) := by
  have hc : 1-scalarOccupation x∈Set.Icc (((207/512) : ℚ) : ℝ) (((523/1280) : ℚ) : ℝ) := by
    norm_num
    constructor <;> linarith [hq.1,hq.2]
  have hlx := logarithm_enclosure (207/512) (523/1280) (-36224233271/40000000000) (-55939618303/62500000000) (2) (2) 14
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [scaledLogLower,logApproximation,logRemainder,Finset.sum_range_succ])
    (by norm_num [scaledLogUpper,logApproximation,logRemainder,Finset.sum_range_succ])
    (1-scalarOccupation x) (hc)
  have hxi : x∈Set.Icc 0.895033892848 0.905605831775 := by
    have he := occupation_log_identity x
    norm_num at hlx
    constructor <;> linarith [hlx.1,hlx.2]
  have hr := remaining_ratio_bounds ((757/1280)) ((305/512)) ((1567367648339/100000000000)) ((1567367648341/100000000000))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (scalarOccupation x) criticalActivity (by convert hq using 1; norm_num) (by convert criticalActivity_bounds using 1; norm_num)
  have hri : criticalActivity*(1-scalarOccupation x)/scalarOccupation x∈Set.Icc
      (((324445103206173/30500000000000) : ℚ) : ℝ) (((819733280082343/75700000000000) : ℚ) : ℝ) := by
    norm_num at hr ⊢
    exact hr
  have hly := logarithm_enclosure (324445103206173/30500000000000) (819733280082343/75700000000000) (118219483237/50000000000) (297775107339/125000000000) (-3) (-3) 14
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [scaledLogLower,logApproximation,logRemainder,Finset.sum_range_succ])
    (by norm_num [scaledLogUpper,logApproximation,logRemainder,Finset.sum_range_succ])
    (criticalActivity*(1-scalarOccupation x)/scalarOccupation x) (hri)
  have hyi : remainingPotential x∈Set.Icc 2.36438966474 2.382200858712 := by
    rw [remainingPotential_eq_log_div x hx,occupation_remaining_ratio x hx]
    norm_num at hly ⊢
    exact hly
  have hz := cubicCenter_tight_bounds
  rw [fourthNumerator_expanded]
  unfold expandedFourth
  dyadic_interval +kernel [prec := 80]

theorem fourth_box_0036 (x : ℝ) (hx : 0<x)
    (hq : scalarOccupation x∈Set.Icc 0.595703125 0.6) :
    0<fourthNumerator (scalarOccupation x) (remainingPotential x) := by
  have hc : 1-scalarOccupation x∈Set.Icc (((2/5) : ℚ) : ℝ) (((207/512) : ℚ) : ℝ) := by
    norm_num
    constructor <;> linarith [hq.1,hq.2]
  have hlx := logarithm_enclosure (2/5) (207/512) (-1466065171/1600000000) (-452802915887/500000000000) (2) (2) 14
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [scaledLogLower,logApproximation,logRemainder,Finset.sum_range_succ])
    (by norm_num [scaledLogUpper,logApproximation,logRemainder,Finset.sum_range_succ])
    (1-scalarOccupation x) (hc)
  have hxi : x∈Set.Icc 0.905605831774 0.916290731875 := by
    have he := occupation_log_identity x
    norm_num at hlx
    constructor <;> linarith [hlx.1,hlx.2]
  have hr := remaining_ratio_bounds ((305/512)) ((3/5)) ((1567367648339/100000000000)) ((1567367648341/100000000000))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (scalarOccupation x) criticalActivity (by convert hq using 1; norm_num) (by convert criticalActivity_bounds using 1; norm_num)
  have hri : criticalActivity*(1-scalarOccupation x)/scalarOccupation x∈Set.Icc
      (((1567367648339/150000000000) : ℚ) : ℝ) (((324445103206587/30500000000000) : ℚ) : ℝ) := by
    norm_num at hr ⊢
    exact hr
  have hly := logarithm_enclosure (1567367648339/150000000000) (324445103206587/30500000000000) (1173258769987/500000000000) (2364389664743/1000000000000) (-3) (-3) 14
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [scaledLogLower,logApproximation,logRemainder,Finset.sum_range_succ])
    (by norm_num [scaledLogUpper,logApproximation,logRemainder,Finset.sum_range_succ])
    (criticalActivity*(1-scalarOccupation x)/scalarOccupation x) (hri)
  have hyi : remainingPotential x∈Set.Icc 2.346517539974 2.364389664743 := by
    rw [remainingPotential_eq_log_div x hx,occupation_remaining_ratio x hx]
    norm_num at hly ⊢
    exact hly
  have hz := cubicCenter_tight_bounds
  rw [fourthNumerator_expanded]
  unfold expandedFourth
  dyadic_interval +kernel [prec := 80]

theorem gap_box_0037 (x : ℝ) (hx : 0<x)
    (hq : scalarOccupation x∈Set.Icc 0.393 0.4105) :
    0<secondFivefoldDerivative x := by
  have hc : 1-scalarOccupation x∈Set.Icc (((1179/2000) : ℚ) : ℝ) (((607/1000) : ℚ) : ℝ) := by
    norm_num
    constructor <;> linarith [hq.1,hq.2]
  have hlx := logarithm_enclosure (1179/2000) (607/1000) (-105696111801/200000000000) (-249613243961/500000000000) (1) (1) 14
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [scaledLogLower,logApproximation,logRemainder,Finset.sum_range_succ])
    (by norm_num [scaledLogUpper,logApproximation,logRemainder,Finset.sum_range_succ])
    (1-scalarOccupation x) (hc)
  have hxi : x∈Set.Icc 0.499226487922 0.528480559005 := by
    have he := occupation_log_identity x
    norm_num at hlx
    constructor <;> linarith [hlx.1,hlx.2]
  have hr := remaining_ratio_bounds ((393/1000)) ((821/2000)) ((1567367648339/100000000000)) ((1567367648341/100000000000))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (scalarOccupation x) criticalActivity (by convert hq using 1; norm_num) (by convert criticalActivity_bounds using 1; norm_num)
  have hri : criticalActivity*(1-scalarOccupation x)/scalarOccupation x∈Set.Icc
      (((1847926457391681/82100000000000) : ℚ) : ℝ) (((951392162542987/39300000000000) : ℚ) : ℝ) := by
    norm_num at hr ⊢
    exact hr
  have hly := logarithm_enclosure (1847926457391681/82100000000000) (951392162542987/39300000000000) (3113881439167/1000000000000) (127468073091/40000000000) (-4) (-4) 14
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [scaledLogLower,logApproximation,logRemainder,Finset.sum_range_succ])
    (by norm_num [scaledLogUpper,logApproximation,logRemainder,Finset.sum_range_succ])
    (criticalActivity*(1-scalarOccupation x)/scalarOccupation x) (hri)
  have hyi : remainingPotential x∈Set.Icc 3.113881439167 3.186701827275 := by
    rw [remainingPotential_eq_log_div x hx,occupation_remaining_ratio x hx]
    norm_num at hly ⊢
    exact hly
  have hz := cubicCenter_tight_bounds
  unfold secondFivefoldDerivative
  rw [secondPartitionDerivative_expanded]
  rw [show cubicCoefficient=(0.016 : ℝ) by norm_num [cubicCoefficient]]
  unfold expandedSecond
  dyadic_interval +kernel [prec := 80]

theorem gap_box_0038 (x : ℝ) (hx : 0<x)
    (hq : scalarOccupation x∈Set.Icc 0.4105 0.428) :
    0<secondFivefoldDerivative x := by
  have hc : 1-scalarOccupation x∈Set.Icc (((143/250) : ℚ) : ℝ) (((1179/2000) : ℚ) : ℝ) := by
    norm_num
    constructor <;> linarith [hq.1,hq.2]
  have hlx := logarithm_enclosure (143/250) (1179/2000) (-558616287603/1000000000000) (-132120139751/250000000000) (1) (1) 14
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [scaledLogLower,logApproximation,logRemainder,Finset.sum_range_succ])
    (by norm_num [scaledLogUpper,logApproximation,logRemainder,Finset.sum_range_succ])
    (1-scalarOccupation x) (hc)
  have hxi : x∈Set.Icc 0.528480559004 0.558616287603 := by
    have he := occupation_log_identity x
    norm_num at hlx
    constructor <;> linarith [hlx.1,hlx.2]
  have hr := remaining_ratio_bounds ((821/2000)) ((107/250)) ((1567367648339/100000000000)) ((1567367648341/100000000000))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (scalarOccupation x) criticalActivity (by convert hq using 1; norm_num) (by convert criticalActivity_bounds using 1; norm_num)
  have hri : criticalActivity*(1-scalarOccupation x)/scalarOccupation x∈Set.Icc
      (((224133573712477/10700000000000) : ℚ) : ℝ) (((1847926457394039/82100000000000) : ℚ) : ℝ) := by
    norm_num at hr ⊢
    exact hr
  have hly := logarithm_enclosure (224133573712477/10700000000000) (1847926457394039/82100000000000) (76049961097/25000000000) (311388143917/100000000000) (-4) (-4) 14
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [scaledLogLower,logApproximation,logRemainder,Finset.sum_range_succ])
    (by norm_num [scaledLogUpper,logApproximation,logRemainder,Finset.sum_range_succ])
    (criticalActivity*(1-scalarOccupation x)/scalarOccupation x) (hri)
  have hyi : remainingPotential x∈Set.Icc 3.04199844388 3.11388143917 := by
    rw [remainingPotential_eq_log_div x hx,occupation_remaining_ratio x hx]
    norm_num at hly ⊢
    exact hly
  have hz := cubicCenter_tight_bounds
  unfold secondFivefoldDerivative
  rw [secondPartitionDerivative_expanded]
  rw [show cubicCoefficient=(0.016 : ℝ) by norm_num [cubicCoefficient]]
  unfold expandedSecond
  dyadic_interval +kernel [prec := 80]

theorem gap_box_0039 (x : ℝ) (hx : 0<x)
    (hq : scalarOccupation x∈Set.Icc 0.428 0.4455) :
    0<secondFivefoldDerivative x := by
  have hc : 1-scalarOccupation x∈Set.Icc (((1109/2000) : ℚ) : ℝ) (((143/250) : ℚ) : ℝ) := by
    norm_num
    constructor <;> linarith [hq.1,hq.2]
  have hlx := logarithm_enclosure (1109/2000) (143/250) (-4606941189/7812500000) (-279308143801/500000000000) (1) (1) 14
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [scaledLogLower,logApproximation,logRemainder,Finset.sum_range_succ])
    (by norm_num [scaledLogUpper,logApproximation,logRemainder,Finset.sum_range_succ])
    (1-scalarOccupation x) (hc)
  have hxi : x∈Set.Icc 0.558616287602 0.589688472192 := by
    have he := occupation_log_identity x
    norm_num at hlx
    constructor <;> linarith [hlx.1,hlx.2]
  have hr := remaining_ratio_bounds ((107/250)) ((891/2000)) ((1567367648339/100000000000)) ((1567367648341/100000000000))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (scalarOccupation x) criticalActivity (by convert hq using 1; norm_num) (by convert criticalActivity_bounds using 1; norm_num)
  have hri : criticalActivity*(1-scalarOccupation x)/scalarOccupation x∈Set.Icc
      (((1738210722007951/89100000000000) : ℚ) : ℝ) (((224133573712763/10700000000000) : ℚ) : ℝ) := by
    norm_num at hr ⊢
    exact hr
  have hly := logarithm_enclosure (1738210722007951/89100000000000) (224133573712763/10700000000000) (1485426103981/500000000000) (3041998443883/1000000000000) (-4) (-4) 14
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [scaledLogLower,logApproximation,logRemainder,Finset.sum_range_succ])
    (by norm_num [scaledLogUpper,logApproximation,logRemainder,Finset.sum_range_succ])
    (criticalActivity*(1-scalarOccupation x)/scalarOccupation x) (hri)
  have hyi : remainingPotential x∈Set.Icc 2.970852207962 3.041998443883 := by
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
