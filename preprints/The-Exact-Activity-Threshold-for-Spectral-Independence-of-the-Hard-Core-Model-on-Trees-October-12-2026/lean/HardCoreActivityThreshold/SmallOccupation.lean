import HardCoreActivityThreshold.EndpointLogarithms

namespace HardCoreActivityThreshold

noncomputable def smallEnvelopeLog (q : ℝ) : ℝ := Real.log criticalActivity-Real.log q
noncomputable def smallEnvelope (q : ℝ) : ℝ :=
  q*(smallEnvelopeLog q+cubicCoefficient*(smallEnvelopeLog q)^3)

theorem smallEnvelopeLog_hasDerivAt (q : ℝ) (hq : 0<q) :
    HasDerivAt smallEnvelopeLog (-q⁻¹) q := by
  convert (hasDerivAt_const q (Real.log criticalActivity)).sub (Real.hasDerivAt_log hq.ne') using 1
  · rfl
  · simp

theorem smallEnvelope_hasDerivAt (q : ℝ) (hq : 0<q) :
    HasDerivAt smallEnvelope (smallEnvelopeLog q-1+
      cubicCoefficient*(smallEnvelopeLog q)^2*(smallEnvelopeLog q-3)) q := by
  have hu := smallEnvelopeLog_hasDerivAt q hq
  convert (hasDerivAt_id q).mul (hu.add ((hu.pow 3).const_mul cubicCoefficient)) using 1
  · rfl
  · have hn := hq.ne'
    dsimp
    field_simp
    ring

theorem smallEnvelopeLog_eq (q : ℝ) (hq : 0<q) :
    smallEnvelopeLog q=Real.log (criticalActivity/q) := by
  rw [Real.log_div scalarCriticalActivity_pos.ne' hq.ne']
  rfl

set_option maxHeartbeats 2000000
set_option maxRecDepth 8192

theorem logarithm_fifteen_hundred_bounds : Real.log ((1500/1) : ℝ)∈Set.Icc (7.31322038709) (7.313220387091) := by
  have hl := logarithm_enclosure (1500/1) (1500/1) (731322038709/100000000000) (7313220387091/1000000000000) (-10) (-10) 14
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [scaledLogLower,logApproximation,logRemainder,Finset.sum_range_succ])
    (by norm_num [scaledLogUpper,logApproximation,logRemainder,Finset.sum_range_succ])
    (((1500/1) : ℝ)) (by norm_num)
  norm_num at hl ⊢
  exact hl

theorem logarithm_fifteen_sixty_eight_bounds : Real.log ((1568/1) : ℝ)∈Set.Icc (7.35755620091) (7.357556200911) := by
  have hl := logarithm_enclosure (1568/1) (1568/1) (735755620091/100000000000) (7357556200911/1000000000000) (-10) (-10) 14
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [scaledLogLower,logApproximation,logRemainder,Finset.sum_range_succ])
    (by norm_num [scaledLogUpper,logApproximation,logRemainder,Finset.sum_range_succ])
    (((1568/1) : ℝ)) (by norm_num)
  norm_num at hl ⊢
  exact hl

theorem smallEnvelopeLog_lower (q : ℝ) (hq : 0<q) (hsmall : q≤0.01) :
    7<smallEnvelopeLog q := by
  rw [smallEnvelopeLog_eq q hq]
  have hr : (1500 : ℝ)≤criticalActivity/q := by
    rw [le_div_iff₀ hq]
    linarith [criticalActivity_bounds.1]
  have hp : 0<criticalActivity/q := div_pos scalarCriticalActivity_pos hq
  have hl := Real.strictMonoOn_log.monotoneOn (by norm_num : (1500 : ℝ)∈Set.Ioi 0) hp hr
  have hb := logarithm_fifteen_hundred_bounds
  norm_num at hb
  linarith [hb.1]

theorem smallEnvelope_strictMonoOn : StrictMonoOn smallEnvelope (Set.Ioc 0 0.01) := by
  apply strictMonoOn_of_deriv_pos (convex_Ioc 0 0.01)
  · intro q hq
    exact (smallEnvelope_hasDerivAt q hq.1).continuousAt.continuousWithinAt
  · intro q hq
    have hqm := interior_subset hq
    rw [(smallEnvelope_hasDerivAt q hqm.1).deriv]
    have hu := smallEnvelopeLog_lower q hqm.1 hqm.2
    have hc := cubicCoefficient_pos
    have hm := mul_nonneg (mul_nonneg hc.le (sq_nonneg (smallEnvelopeLog q)))
      (show 0≤smallEnvelopeLog q-3 by linarith)
    linarith

theorem smallEnvelopeLog_upper_at_one_hundredth : smallEnvelopeLog 0.01<7.36 := by
  rw [smallEnvelopeLog_eq 0.01 (by norm_num)]
  have hr : criticalActivity/0.01≤1568 := by
    rw [div_le_iff₀ (by norm_num : (0 : ℝ)<0.01)]
    linarith [criticalActivity_bounds.2]
  have hp : 0<criticalActivity/0.01 := div_pos scalarCriticalActivity_pos (by norm_num)
  have hl := Real.strictMonoOn_log.monotoneOn hp (by norm_num : (1568 : ℝ)∈Set.Ioi 0) hr
  have hb := logarithm_fifteen_sixty_eight_bounds
  norm_num at hb
  linarith [hb.2]

theorem smallEnvelope_at_one_hundredth : smallEnvelope 0.01<0.138 := by
  have hlo := smallEnvelopeLog_lower 0.01 (by norm_num) le_rfl
  have hhi := smallEnvelopeLog_upper_at_one_hundredth
  have hi : smallEnvelopeLog 0.01∈Set.Icc 7 7.36 := ⟨hlo.le,hhi.le⟩
  unfold smallEnvelope
  rw [show cubicCoefficient=(0.016 : ℝ) by norm_num [cubicCoefficient]]
  simp only [pow_succ,pow_zero]
  dyadic_interval +kernel [prec := 80]

theorem occupation_le_self (x : ℝ) : scalarOccupation x≤x := by
  have h := Real.add_one_le_exp (-x)
  unfold scalarOccupation
  linarith

theorem remainingPotential_le_smallEnvelopeLog (x : ℝ) (hx : 0<x) :
    remainingPotential x≤smallEnvelopeLog (scalarOccupation x) := by
  rw [remainingPotential_occupation x hx]
  unfold smallEnvelopeLog
  have hq := occupation_pos x hx
  have hqc := occupation_lt_one x
  have hl := Real.log_nonpos (show 0≤1-scalarOccupation x by linarith)
    (show 1-scalarOccupation x≤1 by linarith)
  linarith

theorem potential_le_cubic_envelope (u : ℝ) (hu : 7<u) :
    potential u≤u+cubicCoefficient*u^3 := by
  have hz := cubicCenter_bounds
  unfold potential cubicPotential
  have hz0 : 0≤cubicCenter := by linarith [hz.1]
  have hz1 : cubicCenter≤u := by linarith [hz.2]
  have hm := mul_nonneg hz0 (show 0≤2*u-cubicCenter by linarith)
  have hc := cubicCoefficient_pos
  have up : 0≤u := by linarith
  have hm' := mul_nonneg (mul_nonneg up hc.le) hm
  nlinarith

theorem partitionFunction_small (x : ℝ) (hx : 0<x) (hqsmall : scalarOccupation x≤0.01) :
    scalarPartitionFunction x<0.138*x := by
  have hq := occupation_pos x hx
  have hu := smallEnvelopeLog_lower (scalarOccupation x) hq hqsmall
  have hphi := potential_strictMono.monotone (remainingPotential_le_smallEnvelopeLog x hx)
  have hphi' := hphi.trans (potential_le_cubic_envelope _ hu)
  have hc := cubicCoefficient_pos
  have up : 0≤smallEnvelopeLog (scalarOccupation x) := by linarith
  have hbase : 0≤smallEnvelopeLog (scalarOccupation x)+cubicCoefficient*(smallEnvelopeLog (scalarOccupation x))^3 := by
    positivity
  have hf : scalarPartitionFunction x≤scalarOccupation x*smallEnvelope (scalarOccupation x) := by
    have hm := mul_le_mul_of_nonneg_left hphi' (sq_nonneg (scalarOccupation x))
    simpa [scalarPartitionFunction,hx.ne',smallEnvelope,pow_two,mul_assoc] using hm
  have hg : 0≤smallEnvelope (scalarOccupation x) := mul_nonneg hq.le hbase
  have hqx := occupation_le_self x
  have hbound := smallEnvelope_strictMonoOn.monotoneOn ⟨hq, hqsmall⟩ ⟨by norm_num,le_rfl⟩ hqsmall
  have hl : smallEnvelope (scalarOccupation x)<0.138 := hbound.trans_lt smallEnvelope_at_one_hundredth
  have ht := mul_le_mul_of_nonneg_right hqx hg
  have hs := mul_lt_mul_of_pos_left hl hx
  nlinarith

end HardCoreActivityThreshold
