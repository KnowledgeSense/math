import HardCoreActivityThreshold.DerivativePolynomials

namespace HardCoreActivityThreshold
set_option maxHeartbeats 4000000
set_option maxRecDepth 8192

theorem fourth_box_0000 (x : ℝ) (hx : 0<x)
    (hq : scalarOccupation x∈Set.Icc 0.05 0.084375) :
    0<fourthNumerator (scalarOccupation x) (remainingPotential x) := by
  have hc : 1-scalarOccupation x∈Set.Icc (((293/320) : ℚ) : ℝ) (((19/20) : ℚ) : ℝ) := by
    norm_num
    constructor <;> linarith [hq.1,hq.2]
  have hlx := logarithm_enclosure (293/320) (19/20) (-88148386777/1000000000000) (-51293294387/1000000000000) (1) (1) 14
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [scaledLogLower,logApproximation,logRemainder,Finset.sum_range_succ])
    (by norm_num [scaledLogUpper,logApproximation,logRemainder,Finset.sum_range_succ])
    (1-scalarOccupation x) (hc)
  have hxi : x∈Set.Icc 0.051293294387 0.088148386777 := by
    have he := occupation_log_identity x
    norm_num at hlx
    constructor <;> linarith [hlx.1,hlx.2]
  have hr := remaining_ratio_bounds ((1/20)) ((27/320)) ((1567367648339/100000000000)) ((1567367648341/100000000000))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (scalarOccupation x) criticalActivity (by convert hq using 1; norm_num) (by convert criticalActivity_bounds using 1; norm_num)
  have hri : criticalActivity*(1-scalarOccupation x)/scalarOccupation x∈Set.Icc
      (((459238720963327/2700000000000) : ℚ) : ℝ) (((29779985318479/100000000000) : ℚ) : ℝ) := by
    norm_num at hr ⊢
    exact hr
  have hly := logarithm_enclosure (459238720963327/2700000000000) (29779985318479/100000000000) (1027263678219/200000000000) (5696421627251/1000000000000) (-7) (-8) 14
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [scaledLogLower,logApproximation,logRemainder,Finset.sum_range_succ])
    (by norm_num [scaledLogUpper,logApproximation,logRemainder,Finset.sum_range_succ])
    (criticalActivity*(1-scalarOccupation x)/scalarOccupation x) (hri)
  have hyi : remainingPotential x∈Set.Icc 5.136318391095 5.696421627251 := by
    rw [remainingPotential_eq_log_div x hx,occupation_remaining_ratio x hx]
    norm_num at hly ⊢
    exact hly
  have hz := cubicCenter_tight_bounds
  rw [fourthNumerator_expanded]
  unfold expandedFourth
  dyadic_interval +kernel [prec := 80]

theorem fourth_box_0001 (x : ℝ) (hx : 0<x)
    (hq : scalarOccupation x∈Set.Icc 0.084375 0.11875) :
    0<fourthNumerator (scalarOccupation x) (remainingPotential x) := by
  have hc : 1-scalarOccupation x∈Set.Icc (((141/160) : ℚ) : ℝ) (((293/320) : ℚ) : ℝ) := by
    norm_num
    constructor <;> linarith [hq.1,hq.2]
  have hlx := logarithm_enclosure (141/160) (293/320) (-15801740607/125000000000) (-11018548347/125000000000) (1) (1) 14
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [scaledLogLower,logApproximation,logRemainder,Finset.sum_range_succ])
    (by norm_num [scaledLogUpper,logApproximation,logRemainder,Finset.sum_range_succ])
    (1-scalarOccupation x) (hc)
  have hxi : x∈Set.Icc 0.088148386776 0.126413924856 := by
    have he := occupation_log_identity x
    norm_num at hlx
    constructor <;> linarith [hlx.1,hlx.2]
  have hr := remaining_ratio_bounds ((27/320)) ((19/160)) ((1567367648339/100000000000)) ((1567367648341/100000000000))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (scalarOccupation x) criticalActivity (by convert hq using 1; norm_num) (by convert criticalActivity_bounds using 1; norm_num)
  have hri : criticalActivity*(1-scalarOccupation x)/scalarOccupation x∈Set.Icc
      (((220998838415799/1900000000000) : ℚ) : ℝ) (((459238720963913/2700000000000) : ℚ) : ℝ) := by
    norm_num at hr ⊢
    exact hr
  have hly := logarithm_enclosure (220998838415799/1900000000000) (459238720963913/2700000000000) (2378151779647/500000000000) (5136318391097/1000000000000) (-6) (-7) 14
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [scaledLogLower,logApproximation,logRemainder,Finset.sum_range_succ])
    (by norm_num [scaledLogUpper,logApproximation,logRemainder,Finset.sum_range_succ])
    (criticalActivity*(1-scalarOccupation x)/scalarOccupation x) (hri)
  have hyi : remainingPotential x∈Set.Icc 4.756303559294 5.136318391097 := by
    rw [remainingPotential_eq_log_div x hx,occupation_remaining_ratio x hx]
    norm_num at hly ⊢
    exact hly
  have hz := cubicCenter_tight_bounds
  rw [fourthNumerator_expanded]
  unfold expandedFourth
  dyadic_interval +kernel [prec := 80]

theorem fourth_box_0002 (x : ℝ) (hx : 0<x)
    (hq : scalarOccupation x∈Set.Icc 0.11875 0.153125) :
    0<fourthNumerator (scalarOccupation x) (remainingPotential x) := by
  have hc : 1-scalarOccupation x∈Set.Icc (((271/320) : ℚ) : ℝ) (((141/160) : ℚ) : ℝ) := by
    norm_num
    constructor <;> linarith [hq.1,hq.2]
  have hlx := logarithm_enclosure (271/320) (141/160) (-33240434983/200000000000) (-25282784971/200000000000) (1) (1) 14
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [scaledLogLower,logApproximation,logRemainder,Finset.sum_range_succ])
    (by norm_num [scaledLogUpper,logApproximation,logRemainder,Finset.sum_range_succ])
    (1-scalarOccupation x) (hc)
  have hxi : x∈Set.Icc 0.126413924855 0.166202174915 := by
    have he := occupation_log_identity x
    norm_num at hlx
    constructor <;> linarith [hlx.1,hlx.2]
  have hr := remaining_ratio_bounds ((19/160)) ((49/320)) ((1567367648339/100000000000)) ((1567367648341/100000000000))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (scalarOccupation x) criticalActivity (by convert hq using 1; norm_num) (by convert criticalActivity_bounds using 1; norm_num)
  have hri : criticalActivity*(1-scalarOccupation x)/scalarOccupation x∈Set.Icc
      (((424756632699869/4900000000000) : ℚ) : ℝ) (((220998838416081/1900000000000) : ℚ) : ℝ) := by
    norm_num at hr ⊢
    exact hr
  have hly := logarithm_enclosure (424756632699869/4900000000000) (220998838416081/1900000000000) (4462281170851/1000000000000) (37158621557/7812500000) (-6) (-6) 14
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [scaledLogLower,logApproximation,logRemainder,Finset.sum_range_succ])
    (by norm_num [scaledLogUpper,logApproximation,logRemainder,Finset.sum_range_succ])
    (criticalActivity*(1-scalarOccupation x)/scalarOccupation x) (hri)
  have hyi : remainingPotential x∈Set.Icc 4.462281170851 4.756303559296 := by
    rw [remainingPotential_eq_log_div x hx,occupation_remaining_ratio x hx]
    norm_num at hly ⊢
    exact hly
  have hz := cubicCenter_tight_bounds
  rw [fourthNumerator_expanded]
  unfold expandedFourth
  dyadic_interval +kernel [prec := 80]

theorem fourth_box_0003 (x : ℝ) (hx : 0<x)
    (hq : scalarOccupation x∈Set.Icc 0.153125 0.1875) :
    0<fourthNumerator (scalarOccupation x) (remainingPotential x) := by
  have hc : 1-scalarOccupation x∈Set.Icc (((13/16) : ℚ) : ℝ) (((271/320) : ℚ) : ℝ) := by
    norm_num
    constructor <;> linarith [hq.1,hq.2]
  have hlx := logarithm_enclosure (13/16) (271/320) (-207639364779/1000000000000) (-83101087457/500000000000) (1) (1) 14
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [scaledLogLower,logApproximation,logRemainder,Finset.sum_range_succ])
    (by norm_num [scaledLogUpper,logApproximation,logRemainder,Finset.sum_range_succ])
    (1-scalarOccupation x) (hc)
  have hxi : x∈Set.Icc 0.166202174914 0.207639364779 := by
    have he := occupation_log_identity x
    norm_num at hlx
    constructor <;> linarith [hlx.1,hlx.2]
  have hr := remaining_ratio_bounds ((49/320)) ((3/16)) ((1567367648339/100000000000)) ((1567367648341/100000000000))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (scalarOccupation x) criticalActivity (by convert hq using 1; norm_num) (by convert criticalActivity_bounds using 1; norm_num)
  have hri : criticalActivity*(1-scalarOccupation x)/scalarOccupation x∈Set.Icc
      (((20375779428407/300000000000) : ℚ) : ℝ) (((424756632700411/4900000000000) : ℚ) : ℝ) := by
    norm_num at hr ⊢
    exact hr
  have hly := logarithm_enclosure (20375779428407/300000000000) (424756632700411/4900000000000) (1054579929219/250000000000) (2231140585427/500000000000) (-6) (-6) 14
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [scaledLogLower,logApproximation,logRemainder,Finset.sum_range_succ])
    (by norm_num [scaledLogUpper,logApproximation,logRemainder,Finset.sum_range_succ])
    (criticalActivity*(1-scalarOccupation x)/scalarOccupation x) (hri)
  have hyi : remainingPotential x∈Set.Icc 4.218319716876 4.462281170854 := by
    rw [remainingPotential_eq_log_div x hx,occupation_remaining_ratio x hx]
    norm_num at hly ⊢
    exact hly
  have hz := cubicCenter_tight_bounds
  rw [fourthNumerator_expanded]
  unfold expandedFourth
  dyadic_interval +kernel [prec := 80]

theorem fourth_box_0004 (x : ℝ) (hx : 0<x)
    (hq : scalarOccupation x∈Set.Icc 0.1875 0.221875) :
    0<fourthNumerator (scalarOccupation x) (remainingPotential x) := by
  have hc : 1-scalarOccupation x∈Set.Icc (((249/320) : ℚ) : ℝ) (((13/16) : ℚ) : ℝ) := by
    norm_num
    constructor <;> linarith [hq.1,hq.2]
  have hlx := logarithm_enclosure (249/320) (13/16) (-25086809933/100000000000) (-103819682389/500000000000) (1) (1) 14
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [scaledLogLower,logApproximation,logRemainder,Finset.sum_range_succ])
    (by norm_num [scaledLogUpper,logApproximation,logRemainder,Finset.sum_range_succ])
    (1-scalarOccupation x) (hc)
  have hxi : x∈Set.Icc 0.207639364778 0.25086809933 := by
    have he := occupation_log_identity x
    norm_num at hlx
    constructor <;> linarith [hlx.1,hlx.2]
  have hr := remaining_ratio_bounds ((3/16)) ((71/320)) ((1567367648339/100000000000)) ((1567367648341/100000000000))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (scalarOccupation x) criticalActivity (by convert hq using 1; norm_num) (by convert criticalActivity_bounds using 1; norm_num)
  have hri : criticalActivity*(1-scalarOccupation x)/scalarOccupation x∈Set.Icc
      (((390274544436411/7100000000000) : ℚ) : ℝ) (((20375779428433/300000000000) : ℚ) : ℝ) := by
    norm_num at hr ⊢
    exact hr
  have hly := logarithm_enclosure (390274544436411/7100000000000) (20375779428433/300000000000) (2003377833753/500000000000) (2109159858439/500000000000) (-5) (-6) 14
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [scaledLogLower,logApproximation,logRemainder,Finset.sum_range_succ])
    (by norm_num [scaledLogUpper,logApproximation,logRemainder,Finset.sum_range_succ])
    (criticalActivity*(1-scalarOccupation x)/scalarOccupation x) (hri)
  have hyi : remainingPotential x∈Set.Icc 4.006755667506 4.218319716878 := by
    rw [remainingPotential_eq_log_div x hx,occupation_remaining_ratio x hx]
    norm_num at hly ⊢
    exact hly
  have hz := cubicCenter_tight_bounds
  rw [fourthNumerator_expanded]
  unfold expandedFourth
  dyadic_interval +kernel [prec := 80]

theorem fourth_box_0005 (x : ℝ) (hx : 0<x)
    (hq : scalarOccupation x∈Set.Icc 0.221875 0.25625) :
    0<fourthNumerator (scalarOccupation x) (remainingPotential x) := by
  have hc : 1-scalarOccupation x∈Set.Icc (((119/160) : ℚ) : ℝ) (((249/320) : ℚ) : ℝ) := by
    norm_num
    constructor <;> linarith [hq.1,hq.2]
  have hlx := logarithm_enclosure (119/160) (249/320) (-296050322123/1000000000000) (-250868099329/1000000000000) (1) (1) 14
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [scaledLogLower,logApproximation,logRemainder,Finset.sum_range_succ])
    (by norm_num [scaledLogUpper,logApproximation,logRemainder,Finset.sum_range_succ])
    (1-scalarOccupation x) (hc)
  have hxi : x∈Set.Icc 0.250868099329 0.296050322123 := by
    have he := occupation_log_identity x
    norm_num at hlx
    constructor <;> linarith [hlx.1,hlx.2]
  have hr := remaining_ratio_bounds ((71/320)) ((41/160)) ((1567367648339/100000000000)) ((1567367648341/100000000000))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (scalarOccupation x) criticalActivity (by convert hq using 1; norm_num) (by convert criticalActivity_bounds using 1; norm_num)
  have hri : criticalActivity*(1-scalarOccupation x)/scalarOccupation x∈Set.Icc
      (((186516750152341/4100000000000) : ℚ) : ℝ) (((390274544436909/7100000000000) : ℚ) : ℝ) := by
    norm_num at hr ⊢
    exact hr
  have hly := logarithm_enclosure (186516750152341/4100000000000) (390274544436909/7100000000000) (3817534074489/1000000000000) (1001688916877/250000000000) (-5) (-5) 14
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [scaledLogLower,logApproximation,logRemainder,Finset.sum_range_succ])
    (by norm_num [scaledLogUpper,logApproximation,logRemainder,Finset.sum_range_succ])
    (criticalActivity*(1-scalarOccupation x)/scalarOccupation x) (hri)
  have hyi : remainingPotential x∈Set.Icc 3.817534074489 4.006755667508 := by
    rw [remainingPotential_eq_log_div x hx,occupation_remaining_ratio x hx]
    norm_num at hly ⊢
    exact hly
  have hz := cubicCenter_tight_bounds
  rw [fourthNumerator_expanded]
  unfold expandedFourth
  dyadic_interval +kernel [prec := 80]

theorem fourth_box_0006 (x : ℝ) (hx : 0<x)
    (hq : scalarOccupation x∈Set.Icc 0.25625 0.290625) :
    0<fourthNumerator (scalarOccupation x) (remainingPotential x) := by
  have hc : 1-scalarOccupation x∈Set.Icc (((227/320) : ℚ) : ℝ) (((119/160) : ℚ) : ℝ) := by
    norm_num
    constructor <;> linarith [hq.1,hq.2]
  have hlx := logarithm_enclosure (227/320) (119/160) (-343370978313/1000000000000) (-148025161061/500000000000) (1) (1) 14
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [scaledLogLower,logApproximation,logRemainder,Finset.sum_range_succ])
    (by norm_num [scaledLogUpper,logApproximation,logRemainder,Finset.sum_range_succ])
    (1-scalarOccupation x) (hc)
  have hxi : x∈Set.Icc 0.296050322122 0.343370978313 := by
    have he := occupation_log_identity x
    norm_num at hlx
    constructor <;> linarith [hlx.1,hlx.2]
  have hr := remaining_ratio_bounds ((41/160)) ((93/320)) ((1567367648339/100000000000)) ((1567367648341/100000000000))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (scalarOccupation x) criticalActivity (by convert hq using 1; norm_num) (by convert criticalActivity_bounds using 1; norm_num)
  have hri : criticalActivity*(1-scalarOccupation x)/scalarOccupation x∈Set.Icc
      (((355792456172953/9300000000000) : ℚ) : ℝ) (((186516750152579/4100000000000) : ℚ) : ℝ) := by
    norm_num at hr ⊢
    exact hr
  have hly := logarithm_enclosure (355792456172953/9300000000000) (186516750152579/4100000000000) (364433317241/100000000000) (954383518623/250000000000) (-5) (-5) 14
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [scaledLogLower,logApproximation,logRemainder,Finset.sum_range_succ])
    (by norm_num [scaledLogUpper,logApproximation,logRemainder,Finset.sum_range_succ])
    (criticalActivity*(1-scalarOccupation x)/scalarOccupation x) (hri)
  have hyi : remainingPotential x∈Set.Icc 3.64433317241 3.817534074492 := by
    rw [remainingPotential_eq_log_div x hx,occupation_remaining_ratio x hx]
    norm_num at hly ⊢
    exact hly
  have hz := cubicCenter_tight_bounds
  rw [fourthNumerator_expanded]
  unfold expandedFourth
  dyadic_interval +kernel [prec := 80]

theorem fourth_box_0007 (x : ℝ) (hx : 0<x)
    (hq : scalarOccupation x∈Set.Icc 0.290625 0.3078125) :
    0<fourthNumerator (scalarOccupation x) (remainingPotential x) := by
  have hc : 1-scalarOccupation x∈Set.Icc (((443/640) : ℚ) : ℝ) (((227/320) : ℚ) : ℝ) := by
    norm_num
    constructor <;> linarith [hq.1,hq.2]
  have hlx := logarithm_enclosure (443/640) (227/320) (-367898406309/1000000000000) (-42921372289/125000000000) (1) (1) 14
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [scaledLogLower,logApproximation,logRemainder,Finset.sum_range_succ])
    (by norm_num [scaledLogUpper,logApproximation,logRemainder,Finset.sum_range_succ])
    (1-scalarOccupation x) (hc)
  have hxi : x∈Set.Icc 0.343370978312 0.367898406309 := by
    have he := occupation_log_identity x
    norm_num at hlx
    constructor <;> linarith [hlx.1,hlx.2]
  have hr := remaining_ratio_bounds ((93/320)) ((197/640)) ((1567367648339/100000000000)) ((1567367648341/100000000000))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (scalarOccupation x) criticalActivity (by convert hq using 1; norm_num) (by convert criticalActivity_bounds using 1; norm_num)
  have hri : criticalActivity*(1-scalarOccupation x)/scalarOccupation x∈Set.Icc
      (((694343868214177/19700000000000) : ℚ) : ℝ) (((355792456173407/9300000000000) : ℚ) : ℝ) := by
    norm_num at hr ⊢
    exact hr
  have hly := logarithm_enclosure (694343868214177/19700000000000) (355792456173407/9300000000000) (3562348689389/1000000000000) (3644333172413/1000000000000) (-5) (-5) 14
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [scaledLogLower,logApproximation,logRemainder,Finset.sum_range_succ])
    (by norm_num [scaledLogUpper,logApproximation,logRemainder,Finset.sum_range_succ])
    (criticalActivity*(1-scalarOccupation x)/scalarOccupation x) (hri)
  have hyi : remainingPotential x∈Set.Icc 3.562348689389 3.644333172413 := by
    rw [remainingPotential_eq_log_div x hx,occupation_remaining_ratio x hx]
    norm_num at hly ⊢
    exact hly
  have hz := cubicCenter_tight_bounds
  rw [fourthNumerator_expanded]
  unfold expandedFourth
  dyadic_interval +kernel [prec := 80]

theorem fourth_box_0008 (x : ℝ) (hx : 0<x)
    (hq : scalarOccupation x∈Set.Icc 0.3078125 0.325) :
    0<fourthNumerator (scalarOccupation x) (remainingPotential x) := by
  have hc : 1-scalarOccupation x∈Set.Icc (((27/40) : ℚ) : ℝ) (((443/640) : ℚ) : ℝ) := by
    norm_num
    constructor <;> linarith [hq.1,hq.2]
  have hlx := logarithm_enclosure (27/40) (443/640) (-39304258811/100000000000) (-91974601577/250000000000) (1) (1) 14
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [scaledLogLower,logApproximation,logRemainder,Finset.sum_range_succ])
    (by norm_num [scaledLogUpper,logApproximation,logRemainder,Finset.sum_range_succ])
    (1-scalarOccupation x) (hc)
  have hxi : x∈Set.Icc 0.367898406308 0.39304258811 := by
    have he := occupation_log_identity x
    norm_num at hlx
    constructor <;> linarith [hlx.1,hlx.2]
  have hr := remaining_ratio_bounds ((197/640)) ((13/40)) ((1567367648339/100000000000)) ((1567367648341/100000000000))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (scalarOccupation x) criticalActivity (by convert hq using 1; norm_num) (by convert criticalActivity_bounds using 1; norm_num)
  have hri : criticalActivity*(1-scalarOccupation x)/scalarOccupation x∈Set.Icc
      (((42318926505153/1300000000000) : ℚ) : ℝ) (((694343868215063/19700000000000) : ℚ) : ℝ) := by
    norm_num at hr ⊢
    exact hr
  have hly := logarithm_enclosure (42318926505153/1300000000000) (694343868215063/19700000000000) (27862961253/8000000000) (222646793087/62500000000) (-5) (-5) 14
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [scaledLogLower,logApproximation,logRemainder,Finset.sum_range_succ])
    (by norm_num [scaledLogUpper,logApproximation,logRemainder,Finset.sum_range_succ])
    (criticalActivity*(1-scalarOccupation x)/scalarOccupation x) (hri)
  have hyi : remainingPotential x∈Set.Icc 3.482870156625 3.562348689392 := by
    rw [remainingPotential_eq_log_div x hx,occupation_remaining_ratio x hx]
    norm_num at hly ⊢
    exact hly
  have hz := cubicCenter_tight_bounds
  rw [fourthNumerator_expanded]
  unfold expandedFourth
  dyadic_interval +kernel [prec := 80]

theorem fourth_box_0009 (x : ℝ) (hx : 0<x)
    (hq : scalarOccupation x∈Set.Icc 0.325 0.3421875) :
    0<fourthNumerator (scalarOccupation x) (remainingPotential x) := by
  have hc : 1-scalarOccupation x∈Set.Icc (((421/640) : ℚ) : ℝ) (((27/40) : ℚ) : ℝ) := by
    norm_num
    constructor <;> linarith [hq.1,hq.2]
  have hlx := logarithm_enclosure (421/640) (27/40) (-26177208917/62500000000) (-393042588109/1000000000000) (1) (1) 14
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [scaledLogLower,logApproximation,logRemainder,Finset.sum_range_succ])
    (by norm_num [scaledLogUpper,logApproximation,logRemainder,Finset.sum_range_succ])
    (1-scalarOccupation x) (hc)
  have hxi : x∈Set.Icc 0.393042588109 0.418835342672 := by
    have he := occupation_log_identity x
    norm_num at hlx
    constructor <;> linarith [hlx.1,hlx.2]
  have hr := remaining_ratio_bounds ((13/40)) ((219/640)) ((1567367648339/100000000000)) ((1567367648341/100000000000))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (scalarOccupation x) criticalActivity (by convert hq using 1; norm_num) (by convert criticalActivity_bounds using 1; norm_num)
  have hri : criticalActivity*(1-scalarOccupation x)/scalarOccupation x∈Set.Icc
      (((659861779950719/21900000000000) : ℚ) : ℝ) (((42318926505207/1300000000000) : ℚ) : ℝ) := by
    norm_num at hr ⊢
    exact hr
  have hly := logarithm_enclosure (659861779950719/21900000000000) (42318926505207/1300000000000) (851385937987/250000000000) (3482870156627/1000000000000) (-4) (-5) 14
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [scaledLogLower,logApproximation,logRemainder,Finset.sum_range_succ])
    (by norm_num [scaledLogUpper,logApproximation,logRemainder,Finset.sum_range_succ])
    (criticalActivity*(1-scalarOccupation x)/scalarOccupation x) (hri)
  have hyi : remainingPotential x∈Set.Icc 3.405543751948 3.482870156627 := by
    rw [remainingPotential_eq_log_div x hx,occupation_remaining_ratio x hx]
    norm_num at hly ⊢
    exact hly
  have hz := cubicCenter_tight_bounds
  rw [fourthNumerator_expanded]
  unfold expandedFourth
  dyadic_interval +kernel [prec := 80]

end HardCoreActivityThreshold
