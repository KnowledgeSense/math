import HardCoreActivityThreshold.SubcriticalPotential

namespace HardCoreActivityThreshold

 theorem subcritical_uniform_compensation (Λ : ℝ) (hΛ : 0<Λ) (hL : Λ<criticalActivity) :
    ∃η : ℝ,0<η ∧ η≤1/2 ∧ ∀x : ℝ,0<x → x≤subcriticalEndpoint Λ →
      subcriticalFunction Λ x≤(1-η)*scalarPartitionFunction x+η*x/2 := by
  let B := max smallEndpoint (subcriticalEndpoint Λ)
  have hB : smallEndpoint≤B := le_max_left _ _
  have hc : ContinuousOn (subcriticalGap Λ) (Set.Icc smallEndpoint B) := by
    intro x hx
    exact (subcriticalGap_continuousAt Λ x (lt_of_lt_of_le smallEndpoint_pos hx.1)).continuousWithinAt
  obtain ⟨z,hz,hmin⟩ := isCompact_Icc.exists_isMinOn ⟨smallEndpoint,le_rfl,hB⟩ hc
  have hm : 0<subcriticalGap Λ z := subcriticalGap_pos Λ z hΛ hL
    (lt_of_lt_of_le smallEndpoint_pos hz.1)
  let M := 1.001*criticalEndpoint+1
  have hXpos : 0<criticalEndpoint := lt_trans (subcriticalEndpoint_pos Λ hΛ)
    (subcriticalEndpoint_lt Λ hΛ hL)
  have hM : 0<M := by dsimp [M]; positivity
  let η := min (1/2 : ℝ) (subcriticalGap Λ z/M)
  have hη : 0<η := lt_min (by norm_num) (div_pos hm hM)
  have hηhalf : η≤1/2 := min_le_left _ _
  have hηM : η*M≤subcriticalGap Λ z := by
    exact (le_div_iff₀ hM).mp (min_le_right _ _)
  refine ⟨η,hη,hηhalf,?_⟩
  intro x hx hxΛ
  have hxX : x≤criticalEndpoint := hxΛ.trans (subcriticalEndpoint_lt Λ hΛ hL).le
  have hf : subcriticalFunction Λ x≤scalarPartitionFunction x :=
    (subcriticalFunction_lt Λ x hΛ hL hx).le
  by_cases hs : x≤smallEndpoint
  · have hq : scalarOccupation x≤0.01 := by
      rw [←occupation_smallEndpoint]
      exact occupation_strictMono.monotone hs
    have hb := partitionFunction_small x hx hq
    have hp : 0≤η*(x/2-scalarPartitionFunction x) := mul_nonneg hη.le (by linarith)
    nlinarith
  · have hxI : x∈Set.Icc smallEndpoint B := ⟨(le_of_not_ge hs),hxΛ.trans (le_max_right _ _)⟩
    have hgap : subcriticalGap Λ z≤subcriticalGap Λ x := hmin hxI
    have hg := partitionFunction_global_bound x hx hxX
    have hfm : scalarPartitionFunction x≤M := by dsimp [M]; nlinarith
    have hmul := mul_le_mul_of_nonneg_left hfm hη.le
    unfold subcriticalGap at hgap hηM
    have hp : 0≤η*x := mul_nonneg hη.le hx.le
    nlinarith

end HardCoreActivityThreshold
