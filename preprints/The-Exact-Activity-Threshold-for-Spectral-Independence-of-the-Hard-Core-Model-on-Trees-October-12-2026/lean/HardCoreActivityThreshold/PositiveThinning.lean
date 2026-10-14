import HardCoreActivityThreshold.FiniteObservation
import HardCoreActivityThreshold.Fields
import Mathlib.Algebra.BigOperators.Ring.Finset

/-! Independently revealing each occupied coordinate, with exact Bayes posteriors. -/
namespace HardCoreActivityThreshold
open Finset
attribute [local instance] Classical.propDecidable
variable {V : Type*} [Fintype V] [DecidableEq V]

/-- An occupied site is retained as unrevealed with probability `θ`. -/
noncomputable def thinningKernel (θ : ℝ) (s r : Finset V) : ℝ :=
  if r ⊆ s then (1 - θ)^r.card * θ^(s \ r).card else 0

omit [Fintype V] in
theorem thinningKernel_nonneg {θ : ℝ} (hθ : 0 ≤ θ) (hθ1 : θ ≤ 1)
    (s r : Finset V) : 0 ≤ thinningKernel θ s r := by
  unfold thinningKernel
  split_ifs
  · exact mul_nonneg (pow_nonneg (sub_nonneg.mpr hθ1) _) (pow_nonneg hθ _)
  · rfl

theorem thinningKernel_sum (θ : ℝ) (s : Finset V) : ∑ r, thinningKernel θ s r = 1 := by
  calc
    _ = ∑ r ∈ s.powerset, (1 - θ)^r.card * θ^(s \ r).card := by
      unfold thinningKernel
      rw [← sum_filter]
      congr 1
      ext r
      simp
    _ = ∏ _v ∈ s, ((1 - θ) + θ) := by
      rw [prod_add]
      simp
    _ = 1 := by simp

noncomputable def positiveThinning (θ : ℝ) (hθ : 0 ≤ θ) (hθ1 : θ ≤ 1) :
    ObservationChannel (Finset V) (Finset V) where
  kernel := thinningKernel θ
  nonneg := thinningKernel_nonneg hθ hθ1
  sum_one := thinningKernel_sum θ

omit [Fintype V] in
theorem thinningKernel_pos_iff {θ : ℝ} (hθ : 0 < θ) (hθ1 : θ < 1)
    (s r : Finset V) : 0 < thinningKernel θ s r ↔ r ⊆ s := by
  unfold thinningKernel
  split_ifs with hrs
  · exact iff_of_true (mul_pos (pow_pos (sub_pos.mpr hθ1) _) (pow_pos hθ _)) hrs
  · simp [hrs]

omit [Fintype V] in
/-- The factors depending only on the observation cancel in the posterior. -/
theorem thinningKernel_field {θ : ℝ} (hθ : 0 < θ) (s r : Finset V) :
    thinningKernel θ s r =
      ((1 - θ) / θ)^r.card * (if r ⊆ s then fieldWeight (fun _ : V => θ) s else 0) := by
  unfold thinningKernel
  by_cases hrs : r ⊆ s
  · rw [ite_eq_left hrs, ite_eq_left hrs]
    simp only [fieldWeight, prod_const]
    rw [← card_sdiff_add_card_eq_card hrs, pow_add, div_pow]
    field_simp
  · rw [ite_eq_right hrs, ite_eq_right hrs, mul_zero]

/-- Feasibility of an observation is independent of the thinning parameter in the open interval. -/
theorem positiveThinning_output_pos_iff (μ : FiniteLaw (Finset V))
    {θ : ℝ} (hθ : 0 < θ) (hθ1 : θ < 1) (r : Finset V) :
    0 < ((positiveThinning θ hθ.le hθ1.le).output μ).mass r ↔
      0 < μ.eventMass (fun s => r ⊆ s) := by
  change (0 < ∑ s, μ.mass s * thinningKernel θ s r) ↔ _
  rw [sum_pos_iff_of_nonneg (fun s _ => mul_nonneg (μ.nonneg s)
    (thinningKernel_nonneg hθ.le hθ1.le s r))]
  unfold FiniteLaw.eventMass
  rw [sum_pos_iff_of_nonneg (fun s _ => by split_ifs; exact μ.nonneg s; rfl)]
  constructor
  · rintro ⟨s, _, hs⟩
    obtain ⟨hm, hk⟩ := (mul_pos_iff.mp hs).resolve_right
      (fun h => (μ.nonneg s).not_gt h.1)
    refine ⟨s, mem_univ s, ?_⟩
    rw [ite_eq_left ((thinningKernel_pos_iff hθ hθ1 s r).mp hk)]
    exact hm
  · rintro ⟨s, _, hs⟩
    by_cases hrs : r ⊆ s
    · rw [ite_eq_left hrs] at hs
      exact ⟨s, mem_univ s, mul_pos hs ((thinningKernel_pos_iff hθ hθ1 s r).mpr hrs)⟩
    · simp [hrs] at hs

/-- The observation likelihood is a field-weighted occupied-coordinate event. -/
theorem positiveThinning_output_field (μ : FiniteLaw (Finset V))
    {θ : ℝ} (hθ : 0 < θ) (hθ1 : θ ≤ 1) (r : Finset V) :
    ((positiveThinning θ hθ.le hθ1).output μ).mass r =
      ((1 - θ) / θ)^r.card * μ.expectation (fieldWeight (fun _ : V => θ)) *
        (applyField μ (fun _ => θ) (fun _ => hθ)).eventMass (fun s => r ⊆ s) := by
  have hZ := (field_expectation_pos μ (fun _ : V => θ) (fun _ => hθ)).ne'
  change (∑ s, μ.mass s * thinningKernel θ s r) = _
  simp_rw [thinningKernel_field hθ]
  unfold FiniteLaw.eventMass applyField FiniteLaw.reweight
  simp only
  rw [mul_sum]
  apply sum_congr rfl
  intro s _
  by_cases hrs : r ⊆ s <;> simp only [hrs, ite_true, ite_false, mul_zero]
  field_simp

omit [Fintype V] in
/-- Revealing `r` pins exactly those coordinates to occupied. -/
theorem agreesWith_self_iff (r s : Finset V) : agreesWith r r s ↔ r ⊆ s := by
  simp only [agreesWith, inter_eq_right]

omit [Fintype V] in
theorem agreesWith_self (r : Finset V) : agreesWith r r = (fun s => r ⊆ s) := by
  funext s
  exact propext (agreesWith_self_iff r s)

theorem positiveThinning_pinning_feasible (μ : FiniteLaw (Finset V))
    {θ : ℝ} (hθ : 0 < θ) (hθ1 : θ < 1) (r : Finset V)
    (hr : 0 < ((positiveThinning θ hθ.le hθ1.le).output μ).mass r) :
    0 < (applyField μ (fun _ : V => θ) (fun _ => hθ)).eventMass (agreesWith r r) := by
  simp_rw [agreesWith_self]
  rw [positiveThinning_output_field μ hθ hθ1.le] at hr
  have hp : 0 < ((1 - θ) / θ)^r.card * μ.expectation (fieldWeight (fun _ : V => θ)) :=
    mul_pos (pow_pos (div_pos (sub_pos.mpr hθ1) hθ) _)
      (field_expectation_pos μ (fun _ => θ) (fun _ => hθ))
  exact (mul_pos_iff.mp hr).resolve_right (fun h => hp.not_gt h.1) |>.2

/-- Exact posterior law, with both the external field and the occupied pinning explicit. -/
theorem positiveThinning_posterior (μ : FiniteLaw (Finset V))
    {θ : ℝ} (hθ : 0 < θ) (hθ1 : θ < 1) (r : Finset V)
    (hr : 0 < ((positiveThinning θ hθ.le hθ1.le).output μ).mass r) :
    (positiveThinning θ hθ.le hθ1.le).posterior μ r =
      (applyField μ (fun _ : V => θ) (fun _ => hθ)).condition (agreesWith r r)
        (positiveThinning_pinning_feasible μ hθ hθ1 r hr) := by
  apply FiniteLaw.ext
  intro s
  rw [ObservationChannel.posterior_mass _ μ r hr,
    positiveThinning_output_field μ hθ hθ1.le]
  change μ.mass s * thinningKernel θ s r / _ = _
  rw [thinningKernel_field hθ, FiniteLaw.condition_mass]
  simp only [agreesWith_self_iff]
  have hc : ((1 - θ) / θ)^r.card ≠ 0 :=
    (pow_pos (div_pos (sub_pos.mpr hθ1) hθ) _).ne'
  have hZ : μ.expectation (fieldWeight (fun _ : V => θ)) ≠ 0 :=
    (field_expectation_pos μ (fun _ => θ) (fun _ => hθ)).ne'
  have hE := (positiveThinning_pinning_feasible μ hθ hθ1 r hr).ne'
  simp_rw [agreesWith_self] at hE
  unfold applyField FiniteLaw.reweight
  simp only
  by_cases hrs : r ⊆ s <;> simp only [hrs, ite_true, ite_false, mul_zero, zero_div]
  simp_rw [agreesWith_self]
  field_simp

omit [Fintype V] in
@[simp] theorem thinningKernel_one (s r : Finset V) :
    thinningKernel 1 s r = if r = ∅ then 1 else 0 := by
  by_cases hr : r = ∅
  · simp [thinningKernel, hr]
  · have hc : r.card ≠ 0 := by simpa using hr
    simp [thinningKernel, hr, hc]

end HardCoreActivityThreshold
