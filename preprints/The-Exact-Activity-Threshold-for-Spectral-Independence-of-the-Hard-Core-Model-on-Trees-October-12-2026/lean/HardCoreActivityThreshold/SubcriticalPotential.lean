import HardCoreActivityThreshold.CubicPartition

namespace HardCoreActivityThreshold

noncomputable def subcriticalEndpoint (Λ : ℝ) : ℝ := Real.log (1+Λ)
noncomputable def subcriticalPotential (Λ x : ℝ) : ℝ :=
  Real.log Λ-Real.log (Real.exp x-1)
noncomputable def subcriticalFunction (Λ x : ℝ) : ℝ :=
  (scalarOccupation x)^2*potential (subcriticalPotential Λ x)
noncomputable def subcriticalGap (Λ x : ℝ) : ℝ := scalarPartitionFunction x-subcriticalFunction Λ x
noncomputable def smallEndpoint : ℝ := -Real.log 0.99

theorem smallEndpoint_pos : 0<smallEndpoint := by
  unfold smallEndpoint
  have h := logarithm_small_bounds
  norm_num at h ⊢
  linarith [h.2]

theorem occupation_smallEndpoint : scalarOccupation smallEndpoint=0.01 := by
  unfold smallEndpoint scalarOccupation
  rw [neg_neg,Real.exp_log (by norm_num : (0 : ℝ)<0.99)]
  norm_num

theorem subcriticalEndpoint_pos (Λ : ℝ) (hΛ : 0<Λ) : 0<subcriticalEndpoint Λ := by
  unfold subcriticalEndpoint
  exact Real.log_pos (by linarith)

theorem subcriticalEndpoint_lt (Λ : ℝ) (hΛ : 0<Λ) (hL : Λ<criticalActivity) :
    subcriticalEndpoint Λ<criticalEndpoint := by
  unfold subcriticalEndpoint criticalEndpoint
  apply Real.strictMonoOn_log (by change 0<1+Λ; linarith)
    (by change 0<1+criticalActivity; linarith [scalarCriticalActivity_pos])
  linarith

theorem subcriticalPotential_lt (Λ x : ℝ) (hΛ : 0<Λ) (hL : Λ<criticalActivity) :
    subcriticalPotential Λ x<remainingPotential x := by
  have hl := Real.strictMonoOn_log hΛ scalarCriticalActivity_pos hL
  unfold subcriticalPotential remainingPotential
  linarith

theorem subcriticalFunction_lt (Λ x : ℝ) (hΛ : 0<Λ) (hL : Λ<criticalActivity) (hx : 0<x) :
    subcriticalFunction Λ x<scalarPartitionFunction x := by
  have hp := potential_strictMono (subcriticalPotential_lt Λ x hΛ hL)
  have hm := mul_lt_mul_of_pos_left hp (sq_pos_of_pos (occupation_pos x hx))
  simpa [subcriticalFunction,scalarPartitionFunction,hx.ne'] using hm

theorem subcriticalGap_pos (Λ x : ℝ) (hΛ : 0<Λ) (hL : Λ<criticalActivity) (hx : 0<x) :
    0<subcriticalGap Λ x := sub_pos.mpr (subcriticalFunction_lt Λ x hΛ hL hx)

theorem subcriticalFunction_continuousAt (Λ x : ℝ) (hx : 0<x) :
    ContinuousAt (subcriticalFunction Λ) x := by
  unfold subcriticalFunction subcriticalPotential
  apply ContinuousAt.mul ((occupation_hasDerivAt x).continuousAt.pow 2)
  apply (potential_hasDerivAt _).continuousAt.comp
  exact continuousAt_const.sub (((Real.hasDerivAt_exp x).sub_const 1).log
    (exp_sub_one_pos x hx).ne').continuousAt

theorem subcriticalGap_continuousAt (Λ x : ℝ) (hx : 0<x) :
    ContinuousAt (subcriticalGap Λ) x :=
  (partitionFunction_hasDerivAt x hx).continuousAt.sub (subcriticalFunction_continuousAt Λ x hx)

end HardCoreActivityThreshold
