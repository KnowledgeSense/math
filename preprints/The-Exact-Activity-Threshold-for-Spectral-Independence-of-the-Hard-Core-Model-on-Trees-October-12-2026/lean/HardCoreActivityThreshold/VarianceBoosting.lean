import HardCoreActivityThreshold.ThinningContinuity
import HardCoreActivityThreshold.ConditionalVarianceMixture
import Mathlib.Analysis.Calculus.Deriv.MeanValue

/-! Variance boosting by a finite, explicitly normalized positive-revealing channel. -/
namespace HardCoreActivityThreshold
open Finset
attribute [local instance] Classical.propDecidable
variable {V : Type*} [Fintype V] [DecidableEq V]

noncomputable def thinningVarianceDerivative (μ : FiniteLaw (Finset V)) (θ : ℝ)
    (f : Finset V → ℝ) : ℝ :=
  (∑ r, revealEnergy (thinningMass μ θ) (fun r => thinningMean μ θ r f) r) / (1 - θ)

theorem thinningVarianceDerivative_le (μ : FiniteLaw (Finset V))
    {θ C : ℝ} (hθ : 0 < θ) (hθ1 : θ < 1) (hC : 0 ≤ C)
    (hpost : ∀ r, 0 < thinningMass μ θ r →
      CorrelationBound ((positiveThinning θ hθ.le hθ1.le).posterior μ r) C)
    (f : Finset V → ℝ) :
    thinningVarianceDerivative μ θ f ≤ (C / θ) * thinningVariance μ θ f := by
  have hmass (r : Finset V) : 0 ≤ thinningMass μ θ r := by
    rw [thinningMass_eq_output μ hθ.le hθ1.le]
    exact ((positiveThinning θ hθ.le hθ1.le).output μ).nonneg r
  have hratio : 0 ≤ (1 - θ) / θ := (div_pos (sub_pos.mpr hθ1) hθ).le
  have hbound : (∑ r, revealEnergy (thinningMass μ θ) (fun r => thinningMean μ θ r f) r) ≤
      ((1 - θ) / θ) * C * (positiveThinning θ hθ.le hθ1.le).retainedVariance μ f := by
    unfold ObservationChannel.retainedVariance
    rw [mul_sum]
    apply sum_le_sum
    intro r _
    rw [revealEnergy_eq_covariances μ hθ hθ1 r f, ← thinningMass_eq_output μ hθ.le hθ1.le]
    by_cases hr : 0 < thinningMass μ θ r
    · have h := mul_le_mul_of_nonneg_left ((hpost r hr).covariance_mean_sum_le hC f)
        (mul_nonneg hratio (hmass r))
      nlinarith
    · have hz : thinningMass μ θ r = 0 := le_antisymm (le_of_not_gt hr) (hmass r)
      simp [hz]
  rw [← thinningVariance_eq_retainedVariance μ hθ.le hθ1.le] at hbound
  unfold thinningVarianceDerivative
  apply (div_le_iff₀ (sub_pos.mpr hθ1)).mpr
  calc
    _ ≤ ((1 - θ) / θ) * C * thinningVariance μ θ f := hbound
    _ = _ := by ring

private theorem hasDerivAt_power_quotient {x : ℝ} (hx : x ≠ 0) (k : ℕ) :
    HasDerivAt (fun y : ℝ => y^k) ((k : ℝ) / x * x^k) x := by
  convert hasDerivAt_pow k x using 1
  cases k with
  | zero => simp
  | succ k => simp only [Nat.cast_add, Nat.cast_one, Nat.add_sub_cancel, pow_succ]; field_simp

/-- A uniform correlation bound along revealing gives a dimension-free retained-variance bound. -/
theorem thinningVariance_lower (μ : FiniteLaw (Finset V)) (k : ℕ)
    {θ : ℝ} (hθ : 0 < θ) (hθ1 : θ ≤ 1)
    (hpost : ∀ x (hx : θ < x) (hx1 : x < 1), ∀ r, 0 < thinningMass μ x r →
      CorrelationBound ((positiveThinning x (le_of_lt (lt_trans hθ hx)) hx1.le).posterior μ r) k)
    (f : Finset V → ℝ) : θ^k * μ.variance f ≤ thinningVariance μ θ f := by
  let Q : ℝ → ℝ := fun x => thinningVariance μ x f / x^k
  let D : ℝ → ℝ := fun x =>
    (thinningVarianceDerivative μ x f - (k : ℝ) / x * thinningVariance μ x f) / x^k
  have hcont : ContinuousOn Q (Set.Icc θ 1) := by
    intro x hx
    exact ((continuousAt_thinningVariance μ (lt_of_lt_of_le hθ hx.1) f).div
      (continuousAt_id.pow k) (pow_ne_zero _ (lt_of_lt_of_le hθ hx.1).ne')).continuousWithinAt
  have hdiff (x : ℝ) (hx : x ∈ interior (Set.Icc θ 1)) : HasDerivAt Q (D x) x := by
    rw [interior_Icc] at hx
    have hxpos : 0 < x := lt_trans hθ hx.1
    have hV := hasDerivAt_thinningVariance_revealEnergy μ hxpos hx.2 f
    have hp := hasDerivAt_power_quotient hxpos.ne' k
    convert hV.div hp (pow_ne_zero k hxpos.ne') using 1
    change (thinningVarianceDerivative μ x f - ↑k / x * thinningVariance μ x f) / x^k = _
    change (_ - _ * _) / _ = (thinningVarianceDerivative μ x f * x^k -
        thinningVariance μ x f * ((k : ℝ) / x * x^k)) / (x^k)^2
    field_simp
  have hnonpos (x : ℝ) (hx : x ∈ interior (Set.Icc θ 1)) : D x ≤ 0 := by
    rw [interior_Icc] at hx
    have hxpos : 0 < x := lt_trans hθ hx.1
    apply div_nonpos_of_nonpos_of_nonneg _ (pow_nonneg hxpos.le _)
    exact sub_nonpos.mpr (thinningVarianceDerivative_le μ hxpos hx.2 (Nat.cast_nonneg _)
      (hpost x hx.1 hx.2) f)
  have hmono : AntitoneOn Q (Set.Icc θ 1) :=
    antitoneOn_of_hasDerivWithinAt_nonpos (convex_Icc θ 1) hcont
      (fun x hx => (hdiff x hx).hasDerivWithinAt) hnonpos
  have hh := hmono (show θ ∈ Set.Icc θ 1 from ⟨le_refl _, hθ1⟩)
    (show (1 : ℝ) ∈ Set.Icc θ 1 from ⟨hθ1, le_refl _⟩) hθ1
  change thinningVariance μ 1 f / 1^k ≤ thinningVariance μ θ f / θ^k at hh
  rw [one_pow, div_one, thinningVariance_one] at hh
  have hh' := (le_div_iff₀ (pow_pos hθ k)).mp hh
  nlinarith

/-- Exact finite-law boosting. The hypotheses concern actual field-and-pinning posteriors;
no unformalized Markov-chain theorem is assumed. -/
theorem varianceTensorization_boost (μ : FiniteLaw (Finset V)) (k : ℕ)
    {θ C : ℝ} (hθ : 0 < θ) (hθ1 : θ < 1) (hC : 0 ≤ C)
    (hcorr : ∀ x (hx : θ < x) (hx1 : x < 1), ∀ r, 0 < thinningMass μ x r →
      CorrelationBound ((positiveThinning x (le_of_lt (lt_trans hθ hx)) hx1.le).posterior μ r) k)
    (hsmall : ∀ r, 0 < thinningMass μ θ r →
      VarianceTensorization ((positiveThinning θ hθ.le hθ1.le).posterior μ r) C) :
    VarianceTensorization μ (C / θ^k) := by
  apply ObservationChannel.tensorization_of_retainedVariance
    (positiveThinning θ hθ.le hθ1.le) μ hC (pow_pos hθ k)
  · intro f
    rw [← thinningVariance_eq_retainedVariance μ hθ.le hθ1.le]
    exact thinningVariance_lower μ k hθ hθ1.le hcorr f
  · intro r hr
    apply hsmall r
    rw [thinningMass_eq_output μ hθ.le hθ1.le]
    exact hr

end HardCoreActivityThreshold
