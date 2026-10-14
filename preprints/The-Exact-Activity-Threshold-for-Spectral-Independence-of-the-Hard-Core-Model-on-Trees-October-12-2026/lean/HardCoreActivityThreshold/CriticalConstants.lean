import HardCoreActivityThreshold.CubicPotential
import HardCoreActivityThreshold.LogarithmBounds
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Tactic

namespace HardCoreActivityThreshold

set_option maxHeartbeats 2000000
set_option maxRecDepth 4096

theorem criticalOccupation_pos : 0<criticalOccupation := by
  unfold criticalOccupation
  positivity

theorem criticalOccupation_square : 5*criticalOccupation^2=1 := by
  have hs := Real.sq_sqrt (by norm_num : (0 : ℝ)≤5)
  unfold criticalOccupation
  field_simp
  nlinarith

theorem criticalOccupation_bounds : criticalOccupation∈Set.Icc 0.447213595499957 0.447213595499959 := by
  have hs := criticalOccupation_square
  have hp := criticalOccupation_pos
  constructor <;> nlinarith

theorem activity_interval (q : ℝ)
    (hq : q∈Set.Icc 0.447213595499957 0.447213595499959) :
    q/(1-q)^6∈Set.Icc 15.67367648339 15.67367648341 := by
  have hd : 0 < (1-q)^6 := by
    have hp : 0 < 1-q := by linarith [hq.2]
    positivity
  constructor
  · rw [le_div_iff₀ hd]
    simp only [pow_succ, pow_zero]
    dyadic_interval +kernel [prec := 80]
  · rw [div_le_iff₀ hd]
    simp only [pow_succ, pow_zero]
    dyadic_interval +kernel [prec := 80]

theorem criticalActivity_bounds : criticalActivity∈Set.Icc 15.67367648339 15.67367648341 :=
  activity_interval criticalOccupation criticalOccupation_bounds

theorem logarithm_lower_critical_complement :
    (-0.59278360071672 : ℝ)≤Real.log (0.552786404500041 : ℝ) := by
  have h := (scaledLog_bounds (552786404500041/1000000000000000) 1 20 (by norm_num) (by norm_num)).1
  have hn : (-0.59278360071672 : ℝ)≤
      (scaledLogLower (552786404500041/1000000000000000) 1 20 : ℝ) := by
    norm_num [scaledLogLower,logApproximation,logRemainder,Finset.sum_range_succ]
  exact hn.trans (by norm_num at h ⊢; exact h)

theorem logarithm_upper_critical_complement :
    Real.log (0.552786404500043 : ℝ)≤(-0.59278360071669 : ℝ) := by
  have h := (scaledLog_bounds (552786404500043/1000000000000000) 1 20 (by norm_num) (by norm_num)).2
  have hn : (scaledLogUpper (552786404500043/1000000000000000) 1 20 : ℝ)≤(-0.59278360071669 : ℝ) := by
    norm_num [scaledLogUpper,logApproximation,logRemainder,Finset.sum_range_succ]
  have he : Real.log (0.552786404500043 : ℝ) ≤
      (scaledLogUpper (552786404500043/1000000000000000) 1 20 : ℝ) := by
    norm_num at h ⊢
    exact h
  exact he.trans hn

theorem criticalLog_bounds : criticalLog∈Set.Icc 0.59278360071669 0.59278360071672 := by
  have hq := criticalOccupation_bounds
  have hlo := Real.strictMonoOn_log.monotoneOn
    (by norm_num : (0.552786404500041 : ℝ)∈Set.Ioi 0)
    (show 1-criticalOccupation∈Set.Ioi 0 by have := hq.2; simp only [Set.mem_Ioi]; linarith)
    (show (0.552786404500041 : ℝ)≤1-criticalOccupation by have := hq.2; linarith)
  have hhi := Real.strictMonoOn_log.monotoneOn
    (show 1-criticalOccupation∈Set.Ioi 0 by have := hq.2; simp only [Set.mem_Ioi]; linarith)
    (by norm_num : (0.552786404500043 : ℝ)∈Set.Ioi 0)
    (show 1-criticalOccupation≤(0.552786404500043 : ℝ) by have := hq.1; linarith)
  have hl := logarithm_lower_critical_complement
  have hu := logarithm_upper_critical_complement
  unfold criticalLog
  constructor <;> linarith

theorem criticalPotential_bounds : criticalPotential∈Set.Icc 2.96391800358345 2.9639180035836 := by
  have h := criticalLog_bounds
  unfold criticalPotential
  constructor <;> linarith [h.1,h.2]

theorem slope_interval (q : ℝ)
    (hq : q∈Set.Icc 0.447213595499957 0.447213595499959) :
    2*q*(1-q)/(1+q)∈Set.Icc 0.34164078649986 0.34164078649989 := by
  have hd : 0<1+q := by linarith [hq.1]
  constructor
  · rw [le_div_iff₀ hd]
    dyadic_interval +kernel [prec := 80]
  · rw [div_le_iff₀ hd]
    dyadic_interval +kernel [prec := 80]

theorem criticalSlope_bounds : criticalSlope∈Set.Icc 0.34164078649986 0.34164078649989 :=
  slope_interval criticalOccupation criticalOccupation_bounds

theorem defect_interval (d y : ℝ)
    (hd : d∈Set.Icc 0.34164078649986 0.34164078649989)
    (hy : y∈Set.Icc 2.96391800358345 2.9639180035836) :
    d-1/y∈Set.Icc 0.00424953654254 0.00424953654261 := by
  have hp : 0<y := by linarith [hy.1]
  have hlo : (1 : ℝ) / y ≤ d-0.00424953654254 := by
    rw [div_le_iff₀ hp]
    dyadic_interval +kernel [prec := 80]
  have hhi : d-0.00424953654261 ≤ (1 : ℝ) / y := by
    rw [le_div_iff₀ hp]
    dyadic_interval +kernel [prec := 80]
  constructor <;> linarith

theorem slopeDefect_bounds : slopeDefect∈Set.Icc 0.00424953654254 0.00424953654261 :=
  defect_interval criticalSlope criticalPotential criticalSlope_bounds criticalPotential_bounds

theorem slopeDefect_pos : 0<slopeDefect := by linarith [slopeDefect_bounds.1]

theorem radical_interval (d : ℝ)
    (hd : d∈Set.Icc 0.00424953654254 0.00424953654261) :
    1-d^2/(2/125)∈Set.Icc 0.9988713399482 0.9988713399485 := by
  rw [show ∀ d : ℝ, d^2/(2/125)=62.5*(d*d) by intro d; ring]
  constructor <;> dyadic_interval +kernel [prec := 80]

theorem radical_bounds : 1-slopeDefect^2/cubicCoefficient∈Set.Icc 0.9988713399482 0.9988713399485 := by
  exact radical_interval slopeDefect slopeDefect_bounds

theorem radical_sqrt_bounds :
    Real.sqrt (1-slopeDefect^2/cubicCoefficient)∈Set.Icc 0.9994355106499 0.9994355106502 := by
  have hr := radical_bounds
  have hp : 0≤1-slopeDefect^2/cubicCoefficient := by linarith [hr.1]
  have hs := Real.sq_sqrt hp
  have hn := Real.sqrt_nonneg (1-slopeDefect^2/cubicCoefficient)
  constructor <;> nlinarith [hr.1,hr.2]

theorem displacement_interval (d s : ℝ)
    (hd : d∈Set.Icc 0.00424953654254 0.00424953654261)
    (hs : s∈Set.Icc 0.9994355106499 0.9994355106502) :
    d/((2/125)*(1+s))∈Set.Icc 0.132835509069 0.132835509073 := by
  rw [show (2/125 : ℝ)=0.016 by norm_num]
  have hp : 0 < (0.016 : ℝ)*(1+s) := by linarith [hs.1]
  constructor
  · rw [le_div_iff₀ hp]
    dyadic_interval +kernel [prec := 80]
  · rw [div_le_iff₀ hp]
    dyadic_interval +kernel [prec := 80]

theorem cubicDisplacement_bounds : cubicDisplacement∈Set.Icc 0.132835509069 0.132835509073 :=
  displacement_interval _ _ slopeDefect_bounds radical_sqrt_bounds

theorem cubicCenter_bounds : cubicCenter∈Set.Icc 2.8310 2.8311 := by
  have hy := criticalPotential_bounds
  have ht := cubicDisplacement_bounds
  unfold cubicCenter
  constructor <;> linarith [hy.1,hy.2,ht.1,ht.2]

theorem potential_strictMono : StrictMono potential := by
  apply cubicPotential_strictMono cubicCenter
  convert cubicCenter_bounds using 1; norm_num

theorem cubicCenter_tight_bounds : cubicCenter∈Set.Icc 2.831082494510 2.831082494515 := by
  have hy := criticalPotential_bounds
  have ht := cubicDisplacement_bounds
  unfold cubicCenter
  constructor <;> linarith [hy.1,hy.2,ht.1,ht.2]

end HardCoreActivityThreshold
