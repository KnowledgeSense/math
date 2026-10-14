import HardCoreActivityThreshold.ScalarFunctions

namespace HardCoreActivityThreshold

set_option maxHeartbeats 1000000

theorem displacement_equation :
    slopeDefect*(1+cubicCoefficient*cubicDisplacement^2)=2*cubicCoefficient*cubicDisplacement := by
  have hc := cubicCoefficient_pos
  have hr := radical_bounds
  have hnon : 0≤1-slopeDefect^2/cubicCoefficient := by linarith [hr.1]
  have hs := Real.sq_sqrt hnon
  have hp := Real.sqrt_nonneg (1-slopeDefect^2/cubicCoefficient)
  have hn : 1+Real.sqrt (1-slopeDefect^2/cubicCoefficient)≠0 := by linarith
  unfold cubicDisplacement
  field_simp
  field_simp at hs
  have hm := congrArg (fun v : ℝ => slopeDefect*v) hs
  nlinarith [hm]

theorem potential_logarithmic_derivative_critical :
    potentialDerivative criticalPotential=criticalSlope*potential criticalPotential := by
  have he := displacement_equation
  have hy := criticalPotential_bounds
  have hne : criticalPotential≠0 := by linarith [hy.1]
  unfold slopeDefect at he
  field_simp at he
  unfold potentialDerivative potential cubicPotential cubicCenter
  nlinarith [he]

theorem occupation_at_criticalLog : scalarOccupation criticalLog=criticalOccupation := by
  have hq := criticalOccupation_bounds
  have hp : 0<1-criticalOccupation := by linarith [hq.2]
  unfold scalarOccupation criticalLog
  rw [neg_neg,Real.exp_log hp]
  ring

theorem remainingPotential_at_criticalLog : remainingPotential criticalLog=criticalPotential := by
  have hx : 0<criticalLog := by linarith [criticalLog_bounds.1]
  rw [remainingPotential_occupation criticalLog hx,occupation_at_criticalLog]
  have hq := criticalOccupation_pos
  have hc : 0<1-criticalOccupation := by linarith [criticalOccupation_bounds.2]
  unfold criticalActivity
  rw [Real.log_div hq.ne' (pow_ne_zero 6 hc.ne'), Real.log_pow]
  unfold criticalPotential criticalLog
  ring

theorem fivefoldGap_at_criticalLog : fivefoldGap criticalLog=0 := by
  have hx : criticalLog≠0 := by linarith [criticalLog_bounds.1]
  have hq := criticalOccupation_square
  unfold fivefoldGap scalarPartitionFunction
  simp only [hx,↓reduceIte,occupation_at_criticalLog,remainingPotential_at_criticalLog]
  change potential criticalPotential-5*(criticalOccupation^2*potential criticalPotential)=0
  nlinarith [congrArg (fun t : ℝ => t*potential criticalPotential) hq]

theorem fivefoldGap_hasDerivAt (x : ℝ) (hx : 0<x) :
    HasDerivAt fivefoldGap (5*potentialDerivative (5*x)-5*firstPartitionDerivative x) x := by
  convert ((potential_hasDerivAt (5*x)).comp x ((hasDerivAt_id x).const_mul 5)).sub
    ((partitionFunction_hasDerivAt x hx).const_mul 5) using 1
  · rfl
  · ring

theorem fivefoldGap_stationary : HasDerivAt fivefoldGap 0 criticalLog := by
  have hx : 0<criticalLog := by linarith [criticalLog_bounds.1]
  convert fivefoldGap_hasDerivAt criticalLog hx using 1
  unfold firstPartitionDerivative
  rw [occupation_at_criticalLog,remainingPotential_at_criticalLog]
  change 0=5*potentialDerivative criticalPotential-
    5*(2*criticalOccupation*(1-criticalOccupation)*potential criticalPotential-
      criticalOccupation*potentialDerivative criticalPotential)
  rw [potential_logarithmic_derivative_critical]
  unfold criticalSlope
  have hn : 1+criticalOccupation≠0 := by linarith [criticalOccupation_pos]
  field_simp
  ring

noncomputable def firstFivefoldDerivative (x : ℝ) : ℝ :=
  5*potentialDerivative (5*x)-5*firstPartitionDerivative x
noncomputable def secondFivefoldDerivative (x : ℝ) : ℝ :=
  50*cubicCoefficient*(15*x-2*cubicCenter)-5*secondPartitionDerivative x

theorem firstFivefoldDerivative_hasDerivAt (x : ℝ) (hx : 0<x) :
    HasDerivAt firstFivefoldDerivative (secondFivefoldDerivative x) x := by
  have hd := (((potentialDerivative_hasDerivAt (5*x)).comp x
    ((hasDerivAt_id x).const_mul 5)).const_mul 5).sub
    ((firstPartitionDerivative_hasDerivAt x hx).const_mul 5)
  convert hd using 1
  · rfl
  · unfold secondFivefoldDerivative potentialSecondDerivative
    ring

end HardCoreActivityThreshold
