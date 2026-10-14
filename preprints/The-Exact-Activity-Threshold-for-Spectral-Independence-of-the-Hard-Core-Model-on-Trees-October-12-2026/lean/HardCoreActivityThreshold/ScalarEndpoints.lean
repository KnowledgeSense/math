import HardCoreActivityThreshold.ScalarCoordinates

namespace HardCoreActivityThreshold

theorem occupation_le_iff (x a : ℝ) (ha : a<1) :
    scalarOccupation x≤a ↔ x≤-Real.log (1-a) := by
  have hp : 0<1-a := by linarith
  have he := Real.log_le_iff_le_exp (y := -x) hp
  unfold scalarOccupation
  constructor
  · intro h
    have h' : 1-a≤Real.exp (-x) := by linarith
    have hl := he.mpr h'
    linarith
  · intro h
    have hl : Real.log (1-a)≤-x := by linarith
    have h' := he.mp hl
    linarith

theorem le_occupation_iff (x a : ℝ) (ha : a<1) :
    a≤scalarOccupation x ↔ -Real.log (1-a)≤x := by
  have hp : 0<1-a := by linarith
  have he := (Real.le_log_iff_exp_le (x := -x) hp).symm
  unfold scalarOccupation
  constructor
  · intro h
    have h' : Real.exp (-x)≤1-a := by linarith
    have hl := he.mp h'
    linarith
  · intro h
    have hl : -x≤Real.log (1-a) := by linarith
    have h' := he.mpr hl
    linarith

theorem occupation_criticalEndpoint : scalarOccupation criticalEndpoint=criticalActivity/(1+criticalActivity) := by
  have hp : 0<1+criticalActivity := by linarith [scalarCriticalActivity_pos]
  unfold scalarOccupation criticalEndpoint
  rw [Real.exp_neg,Real.exp_log hp]
  field_simp
  ring

theorem occupation_criticalEndpoint_lt : scalarOccupation criticalEndpoint<0.941 := by
  rw [occupation_criticalEndpoint]
  have hp : 0<1+criticalActivity := by linarith [scalarCriticalActivity_pos]
  rw [div_lt_iff₀ hp]
  linarith [criticalActivity_bounds.2]

theorem occupation_strictMono : StrictMono scalarOccupation := by
  apply strictMono_of_deriv_pos
  intro x
  rw [(occupation_hasDerivAt x).deriv]
  linarith [occupation_lt_one x]

theorem occupation_concavityEndpoint : scalarOccupation concavityEndpoint=0.6 := by
  unfold scalarOccupation concavityEndpoint
  rw [Real.exp_neg,Real.exp_log (by norm_num : (0 : ℝ)<5/2)]
  norm_num

end HardCoreActivityThreshold
