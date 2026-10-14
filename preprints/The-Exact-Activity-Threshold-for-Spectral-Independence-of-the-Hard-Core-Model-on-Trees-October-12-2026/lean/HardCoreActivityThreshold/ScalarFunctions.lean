import HardCoreActivityThreshold.CriticalConstants
import Mathlib.Analysis.SpecialFunctions.ExpDeriv

namespace HardCoreActivityThreshold

noncomputable def scalarOccupation (x : ℝ) : ℝ := 1-Real.exp (-x)
noncomputable def remainingPotential (x : ℝ) : ℝ :=
  Real.log criticalActivity-Real.log (Real.exp x-1)
noncomputable def scalarPartitionFunction (x : ℝ) : ℝ :=
  if x=0 then 0 else (scalarOccupation x)^2*potential (remainingPotential x)
noncomputable def criticalEndpoint : ℝ := Real.log (1+criticalActivity)
noncomputable def concavityEndpoint : ℝ := Real.log (5/2)
noncomputable def fivefoldGap (x : ℝ) : ℝ := potential (5*x)-5*scalarPartitionFunction x

theorem scalarCriticalActivity_pos : 0<criticalActivity := by
  linarith [criticalActivity_bounds.1]

theorem occupation_pos (x : ℝ) (hx : 0<x) : 0<scalarOccupation x := by
  unfold scalarOccupation
  have h : Real.exp (-x)<1 := by rw [Real.exp_lt_one_iff]; linarith
  linarith

theorem occupation_lt_one (x : ℝ) : scalarOccupation x<1 := by
  unfold scalarOccupation
  linarith [Real.exp_pos (-x)]

theorem exp_sub_one_pos (x : ℝ) (hx : 0<x) : 0<Real.exp x-1 := by
  have h : 1<Real.exp x := by exact Real.one_lt_exp_iff.mpr hx
  linarith

theorem occupation_hasDerivAt (x : ℝ) : HasDerivAt scalarOccupation (1-scalarOccupation x) x := by
  convert (hasDerivAt_const x (1 : ℝ)).sub
    ((hasDerivAt_id x).neg.exp) using 1
  · rfl
  · simp [scalarOccupation]

theorem remainingPotential_eq_log_div (x : ℝ) (hx : 0<x) :
    remainingPotential x=Real.log (criticalActivity/(Real.exp x-1)) := by
  rw [Real.log_div scalarCriticalActivity_pos.ne' (exp_sub_one_pos x hx).ne']
  rfl

theorem occupation_exp_identity (x : ℝ) : scalarOccupation x*Real.exp x=Real.exp x-1 := by
  unfold scalarOccupation
  rw [sub_mul, one_mul, Real.exp_neg, inv_mul_cancel₀ (Real.exp_ne_zero x)]

theorem remainingPotential_hasDerivAt (x : ℝ) (hx : 0<x) :
    HasDerivAt remainingPotential (-(scalarOccupation x)⁻¹) x := by
  have he := ((Real.hasDerivAt_exp x).sub_const 1).log (exp_sub_one_pos x hx).ne'
  convert (hasDerivAt_const x (Real.log criticalActivity)).sub he using 1
  · rfl
  · have hq := occupation_pos x hx
    have hr := exp_sub_one_pos x hx
    field_simp
    nlinarith [occupation_exp_identity x]

noncomputable def potentialDerivative (y : ℝ) : ℝ :=
  1+cubicCoefficient*(3*y^2-4*cubicCenter*y+cubicCenter^2)
noncomputable def potentialSecondDerivative (y : ℝ) : ℝ :=
  2*cubicCoefficient*(3*y-2*cubicCenter)

theorem potential_hasDerivAt (y : ℝ) :
    HasDerivAt potential (potentialDerivative y) y :=
  cubicPotential_hasDerivAt cubicCenter y

theorem potentialDerivative_hasDerivAt (y : ℝ) :
    HasDerivAt potentialDerivative (potentialSecondDerivative y) y := by
  convert (((hasDerivAt_id y).pow 2 |>.const_mul 3).sub
    ((hasDerivAt_id y).const_mul (4*cubicCenter)) |>.add_const (cubicCenter^2)
    |>.const_mul cubicCoefficient |>.const_add 1) using 1
  · rfl
  · dsimp
    unfold potentialSecondDerivative
    ring

theorem potentialSecondDerivative_hasDerivAt (y : ℝ) :
    HasDerivAt potentialSecondDerivative (6*cubicCoefficient) y := by
  convert (((hasDerivAt_id y).const_mul 3).sub_const (2*cubicCenter)
    |>.const_mul (2*cubicCoefficient)) using 1
  · rfl
  · ring

noncomputable def firstPartitionDerivative (x : ℝ) : ℝ :=
  2*scalarOccupation x*(1-scalarOccupation x)*potential (remainingPotential x)-
    scalarOccupation x*potentialDerivative (remainingPotential x)
noncomputable def secondPartitionDerivative (x : ℝ) : ℝ :=
  2*(1-scalarOccupation x)*(1-2*scalarOccupation x)*potential (remainingPotential x)-
    3*(1-scalarOccupation x)*potentialDerivative (remainingPotential x)+
    potentialSecondDerivative (remainingPotential x)

theorem partitionFunction_hasDerivAt (x : ℝ) (hx : 0<x) :
    HasDerivAt scalarPartitionFunction (firstPartitionDerivative x) x := by
  have hq := occupation_hasDerivAt x
  have hy := remainingPotential_hasDerivAt x hx
  have hp := (potential_hasDerivAt (remainingPotential x)).comp x hy
  have hd := (hq.pow 2).mul hp
  have he : scalarPartitionFunction =ᶠ[nhds x]
      (fun t => (scalarOccupation t)^2*potential (remainingPotential t)) := by
    filter_upwards [eventually_ne_nhds hx.ne'] with t ht
    simp [scalarPartitionFunction,ht]
  apply (hd.congr_of_eventuallyEq he).congr_deriv
  unfold firstPartitionDerivative
  have hqn := (occupation_pos x hx).ne'
  simp only [Function.comp_apply, Pi.pow_apply]
  field_simp
  ring

theorem firstPartitionDerivative_hasDerivAt (x : ℝ) (hx : 0<x) :
    HasDerivAt firstPartitionDerivative (secondPartitionDerivative x) x := by
  have hq := occupation_hasDerivAt x
  have hy := remainingPotential_hasDerivAt x hx
  have hp := (potential_hasDerivAt (remainingPotential x)).comp x hy
  have hp1 := (potentialDerivative_hasDerivAt (remainingPotential x)).comp x hy
  have hd := (((hq.const_mul 2).mul ((hasDerivAt_const x (1 : ℝ)).sub hq)).mul hp).sub
    (hq.mul hp1)
  convert hd using 1
  · rfl
  · simp only [Function.comp_apply, Pi.sub_apply, Pi.mul_apply]
    unfold secondPartitionDerivative
    have hqn := (occupation_pos x hx).ne'
    field_simp
    ring

theorem partitionFunction_deriv (x : ℝ) (hx : 0<x) :
    deriv scalarPartitionFunction x=firstPartitionDerivative x :=
  (partitionFunction_hasDerivAt x hx).deriv

theorem occupation_log_identity (x : ℝ) : -Real.log (1-scalarOccupation x)=x := by
  simp [scalarOccupation, Real.log_exp]

theorem remainingPotential_occupation (x : ℝ) (hx : 0<x) :
    remainingPotential x=Real.log criticalActivity+
      Real.log (1-scalarOccupation x)-Real.log (scalarOccupation x) := by
  have hq := occupation_pos x hx
  have he := occupation_exp_identity x
  have hl := Real.log_mul hq.ne' (Real.exp_ne_zero x)
  rw [he,Real.log_exp] at hl
  have hc : Real.log (1-scalarOccupation x)=-x := by simp [scalarOccupation]
  unfold remainingPotential
  rw [hc,hl]
  ring

theorem remainingPotential_nonneg (x : ℝ) (hx : 0<x) (hX : x≤criticalEndpoint) :
    0≤remainingPotential x := by
  have he : Real.exp x≤1+criticalActivity := by
    have h := Real.exp_le_exp.mpr hX
    simpa [criticalEndpoint,Real.exp_log (by linarith [scalarCriticalActivity_pos] : 0<1+criticalActivity)] using h
  have hl := Real.strictMonoOn_log.monotoneOn (exp_sub_one_pos x hx)
    scalarCriticalActivity_pos (by linarith : Real.exp x-1≤criticalActivity)
  unfold remainingPotential
  linarith

theorem partitionFunction_nonneg (x : ℝ) (hx : 0≤x) (hX : x≤criticalEndpoint) :
    0≤scalarPartitionFunction x := by
  by_cases hz : x=0
  · simp [scalarPartitionFunction,hz]
  · simp only [scalarPartitionFunction, hz, ↓reduceIte]
    exact mul_nonneg (sq_nonneg _) (cubicPotential_nonneg _ _
      (remainingPotential_nonneg x (lt_of_le_of_ne hx (Ne.symm hz)) hX))

end HardCoreActivityThreshold
