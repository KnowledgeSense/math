import HardCoreActivityThreshold.ThinningResponse
import Mathlib.Tactic.FunProp

/-! Continuity up to the unobserved endpoint, including vanishing observation probabilities. -/
namespace HardCoreActivityThreshold
open Finset
open Filter
attribute [local instance] Classical.propDecidable
variable {V : Type*} [Fintype V] [DecidableEq V]

noncomputable def pinnedFieldMoment (μ : FiniteLaw (Finset V)) (θ : ℝ)
    (r : Finset V) (f : Finset V → ℝ) : ℝ :=
  ∑ s, if r ⊆ s then μ.mass s * θ^s.card * f s else 0

theorem continuous_pinnedFieldMoment (μ : FiniteLaw (Finset V))
    (r : Finset V) (f : Finset V → ℝ) : Continuous (fun x => pinnedFieldMoment μ x r f) := by
  unfold pinnedFieldMoment
  apply continuous_finsetSum
  intro s _
  by_cases hrs : r ⊆ s <;> simp only [hrs, ite_true, ite_false] <;> fun_prop

theorem pinnedFieldMoment_one_pos (μ : FiniteLaw (Finset V)) (r : Finset V)
    (hr : 0 < μ.eventMass (fun s => r ⊆ s)) {θ : ℝ} (hθ : 0 < θ) :
    0 < pinnedFieldMoment μ θ r (fun _ => 1) := by
  unfold FiniteLaw.eventMass at hr
  obtain ⟨s, _, hs⟩ := (sum_pos_iff_of_nonneg (fun s (_ : s ∈ (univ : Finset (Finset V))) =>
    by split_ifs; exact μ.nonneg s; rfl)).mp hr
  have hrs : r ⊆ s := by by_contra h; simp [h] at hs
  rw [ite_eq_left hrs] at hs
  apply sum_pos'
  · intro t _
    split_ifs
    · exact mul_nonneg (mul_nonneg (μ.nonneg t) (pow_nonneg hθ.le _)) zero_le_one
    · rfl
  · exact ⟨s, mem_univ s, by rw [ite_eq_left hrs, mul_one]; exact mul_pos hs (pow_pos hθ _)⟩

theorem thinningMoment_field_factor (μ : FiniteLaw (Finset V))
    {θ : ℝ} (hθ : 0 < θ) (r : Finset V) (f : Finset V → ℝ) :
    thinningMoment μ θ r f = ((1 - θ) / θ)^r.card * pinnedFieldMoment μ θ r f := by
  unfold thinningMoment pinnedFieldMoment
  rw [mul_sum]
  apply sum_congr rfl
  intro s _
  rw [thinningKernel_field hθ]
  by_cases hrs : r ⊆ s <;> simp [hrs, fieldWeight]
  ring

private theorem quadratic_ratio_factor (c a z : ℝ) :
    (c * a)^2 / (c * z) = c * (a^2 / z) := by
  by_cases hc : c = 0
  · simp [hc]
  · by_cases hz : z = 0
    · simp [hz]
    · field_simp

theorem thinningEnergy_field_factor (μ : FiniteLaw (Finset V))
    {θ : ℝ} (hθ : 0 < θ) (r : Finset V) (f : Finset V → ℝ) :
    thinningEnergy μ θ r f = ((1 - θ) / θ)^r.card *
      (pinnedFieldMoment μ θ r f ^ 2 / pinnedFieldMoment μ θ r (fun _ => 1)) := by
  unfold thinningEnergy thinningMass
  simp_rw [thinningMoment_field_factor μ hθ]
  exact quadratic_ratio_factor _ _ _

/-- Null observations at `θ = 1` cause no discontinuity in their weighted variance contributions. -/
theorem continuousAt_thinningEnergy (μ : FiniteLaw (Finset V)) {θ : ℝ} (hθ : 0 < θ)
    (r : Finset V) (f : Finset V → ℝ) : ContinuousAt (fun x => thinningEnergy μ x r f) θ := by
  by_cases hr : 0 < μ.eventMass (fun s => r ⊆ s)
  · have hZ := (pinnedFieldMoment_one_pos μ r hr hθ).ne'
    have hc : ContinuousAt (fun x : ℝ => ((1 - x) / x)^r.card *
        (pinnedFieldMoment μ x r f ^ 2 / pinnedFieldMoment μ x r (fun _ => 1))) θ := by
      exact (((continuousAt_const.sub continuousAt_id).div continuousAt_id hθ.ne').pow _).mul
        (((continuous_pinnedFieldMoment μ r f).continuousAt.pow 2).div
          (continuous_pinnedFieldMoment μ r (fun _ => 1)).continuousAt hZ)
    apply hc.congr_of_eventuallyEq
    filter_upwards [eventually_gt_nhds hθ] with x hx
    exact thinningEnergy_field_factor μ hx r f
  · have hr0 : μ.eventMass (fun s => r ⊆ s) = 0 :=
      le_antisymm (le_of_not_gt hr) (μ.eventMass_nonneg _)
    have he : (fun x => thinningEnergy μ x r f) = fun _ => (0 : ℝ) := by
      funext x
      simp [thinningEnergy, thinningMoment_zero_of_infeasible μ r hr0]
    rw [he]
    exact continuousAt_const

theorem continuousAt_thinningVariance (μ : FiniteLaw (Finset V)) {θ : ℝ} (hθ : 0 < θ)
    (f : Finset V → ℝ) : ContinuousAt (fun x => thinningVariance μ x f) θ := by
  exact continuousAt_const.sub (tendsto_finsetSum _
    (fun r _ => continuousAt_thinningEnergy μ hθ r f))

@[simp] theorem thinningMoment_one (μ : FiniteLaw (Finset V))
    (r : Finset V) (f : Finset V → ℝ) :
    thinningMoment μ 1 r f = if r = ∅ then μ.expectation f else 0 := by
  by_cases hr : r = ∅ <;> simp [thinningMoment, thinningKernel_one, hr, FiniteLaw.expectation]

@[simp] theorem thinningVariance_one (μ : FiniteLaw (Finset V)) (f : Finset V → ℝ) :
    thinningVariance μ 1 f = μ.variance f := by
  rw [FiniteLaw.variance_eq_second_moment]
  unfold thinningVariance thinningEnergy thinningMass
  simp_rw [thinningMoment_one, FiniteLaw.expectation_const]
  have he (r : Finset V) :
      (if r = ∅ then μ.expectation f else 0)^2 / (if r = ∅ then (1 : ℝ) else 0) =
        if r = ∅ then μ.expectation f ^ 2 else 0 := by
    split_ifs <;> simp
  simp_rw [he]
  simp

end HardCoreActivityThreshold
