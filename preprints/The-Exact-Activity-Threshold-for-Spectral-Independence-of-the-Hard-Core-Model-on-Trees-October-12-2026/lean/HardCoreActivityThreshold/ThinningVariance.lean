import HardCoreActivityThreshold.ThinningMoments
import HardCoreActivityThreshold.CovarianceResponse
import HardCoreActivityThreshold.HeatBathVariance

/-! Exact retained-variance derivatives for positive-coordinate observations. -/
namespace HardCoreActivityThreshold
open Finset
attribute [local instance] Classical.propDecidable
variable {V : Type*} [Fintype V] [DecidableEq V]

noncomputable def thinningMass (μ : FiniteLaw (Finset V)) (θ : ℝ) (r : Finset V) : ℝ :=
  thinningMoment μ θ r (fun _ => 1)

noncomputable def thinningMean (μ : FiniteLaw (Finset V)) (θ : ℝ) (r : Finset V)
    (f : Finset V → ℝ) : ℝ := thinningMoment μ θ r f / thinningMass μ θ r

noncomputable def thinningEnergy (μ : FiniteLaw (Finset V)) (θ : ℝ) (r : Finset V)
    (f : Finset V → ℝ) : ℝ := thinningMoment μ θ r f ^ 2 / thinningMass μ θ r

noncomputable def thinningVariance (μ : FiniteLaw (Finset V)) (θ : ℝ)
    (f : Finset V → ℝ) : ℝ := μ.expectation (fun s => f s^2) - ∑ r, thinningEnergy μ θ r f

theorem thinningMass_eq_output (μ : FiniteLaw (Finset V))
    {θ : ℝ} (hθ : 0 ≤ θ) (hθ1 : θ ≤ 1) (r : Finset V) :
    thinningMass μ θ r = ((positiveThinning θ hθ hθ1).output μ).mass r := by
  simp only [thinningMass, thinningMoment, mul_one]
  rfl

theorem thinningVariance_eq_retainedVariance (μ : FiniteLaw (Finset V))
    {θ : ℝ} (hθ : 0 ≤ θ) (hθ1 : θ ≤ 1) (f : Finset V → ℝ) :
    thinningVariance μ θ f = (positiveThinning θ hθ hθ1).retainedVariance μ f := by
  rw [ObservationChannel.retainedVariance_eq_moments]
  simp only [thinningVariance, thinningEnergy, thinningMass_eq_output μ hθ hθ1]
  rfl

theorem thinningMoment_zero_of_infeasible (μ : FiniteLaw (Finset V)) (r : Finset V)
    (hr : μ.eventMass (fun s => r ⊆ s) = 0) (θ : ℝ) (f : Finset V → ℝ) :
    thinningMoment μ θ r f = 0 := by
  apply sum_eq_zero
  intro s _
  by_cases hrs : r ⊆ s
  · have hs := μ.mass_zero_of_eventMass_zero hrs hr
    rw [hs, zero_mul, zero_mul]
  · simp [thinningKernel, hrs]

theorem thinningMoment_zero_of_mass_zero (μ : FiniteLaw (Finset V))
    {θ : ℝ} (hθ : 0 < θ) (hθ1 : θ < 1) (r : Finset V)
    (hr : thinningMass μ θ r = 0) (f : Finset V → ℝ) : thinningMoment μ θ r f = 0 := by
  have hnot : ¬ 0 < μ.eventMass (fun s => r ⊆ s) := by
    intro he
    have hp := (positiveThinning_output_pos_iff μ hθ hθ1 r).mpr he
    rw [← thinningMass_eq_output μ hθ.le hθ1.le, hr] at hp
    exact lt_irrefl _ hp
  exact thinningMoment_zero_of_infeasible μ r
    (le_antisymm (le_of_not_gt hnot) (μ.eventMass_nonneg _)) θ f

theorem thinningMoment_eq_mass_mul_mean (μ : FiniteLaw (Finset V))
    {θ : ℝ} (hθ : 0 < θ) (hθ1 : θ < 1) (r : Finset V) (f : Finset V → ℝ) :
    thinningMoment μ θ r f = thinningMass μ θ r * thinningMean μ θ r f := by
  unfold thinningMean
  by_cases hr : thinningMass μ θ r = 0
  · rw [hr, zero_mul, thinningMoment_zero_of_mass_zero μ hθ hθ1 r hr f]
  · field_simp

theorem thinningEnergy_eq_mass_mul_mean_sq (μ : FiniteLaw (Finset V))
    (θ : ℝ) (r : Finset V) (f : Finset V → ℝ) :
    thinningEnergy μ θ r f = thinningMass μ θ r * thinningMean μ θ r f ^ 2 := by
  unfold thinningMean thinningEnergy
  by_cases hr : thinningMass μ θ r = 0
  · simp [hr]
  · field_simp

theorem hasDerivAt_thinningEnergy (μ : FiniteLaw (Finset V))
    {θ : ℝ} (hθ : 0 < θ) (hθ1 : θ < 1) (r : Finset V) (f : Finset V → ℝ) :
    HasDerivAt (fun x => thinningEnergy μ x r f)
      ((2 * thinningMean μ θ r f * insertSum (fun q => thinningMoment μ θ q f) r -
        thinningMean μ θ r f ^ 2 * insertSum (thinningMass μ θ) r -
        (r.card : ℝ) * thinningEnergy μ θ r f) / (1 - θ)) θ := by
  by_cases hr : thinningMass μ θ r = 0
  · have hnot : ¬ 0 < μ.eventMass (fun s => r ⊆ s) := by
      intro he
      have hp := (positiveThinning_output_pos_iff μ hθ hθ1 r).mpr he
      rw [← thinningMass_eq_output μ hθ.le hθ1.le, hr] at hp
      exact lt_irrefl _ hp
    have hzero := thinningMoment_zero_of_infeasible μ r
      (le_antisymm (le_of_not_gt hnot) (μ.eventMass_nonneg _))
    have he : (fun x => thinningEnergy μ x r f) = fun _ => (0 : ℝ) := by
      funext x
      simp [thinningEnergy, hzero x f]
    rw [he]
    simpa [thinningMean, thinningEnergy, hr] using (hasDerivAt_const θ (0 : ℝ))
  · have hA := hasDerivAt_thinningMoment μ hθ hθ1 r f
    have hZ := hasDerivAt_thinningMoment μ hθ hθ1 r (fun _ => 1)
    convert (hA.pow 2).div hZ hr using 1
    · rfl
    · change _ = (2 * thinningMoment μ θ r f ^ (2 - 1) *
          ((insertSum (fun q => thinningMoment μ θ q f) r -
            (r.card : ℝ) * thinningMoment μ θ r f) / (1 - θ)) * thinningMass μ θ r -
          thinningMoment μ θ r f ^ 2 * ((insertSum (thinningMass μ θ) r -
            (r.card : ℝ) * thinningMass μ θ r) / (1 - θ))) / thinningMass μ θ r ^ 2
      unfold thinningMean thinningEnergy
      field_simp
      ring

noncomputable def revealEnergy (z m : Finset V → ℝ) (r : Finset V) : ℝ :=
  ∑ v, if v ∉ r then z (insert v r) * (m (insert v r) - m r)^2 else 0

theorem sum_revealEnergy_identity (z m : Finset V → ℝ) :
    (∑ r, (2 * m r * insertSum (fun q => z q * m q) r -
      m r ^ 2 * insertSum z r - (r.card : ℝ) * (z r * m r ^ 2))) =
        -(∑ r, revealEnergy z m r) := by
  have he (r : Finset V) : 2 * m r * insertSum (fun q => z q * m q) r -
      m r ^ 2 * insertSum z r - insertSum (fun q => z q * m q ^ 2) r =
        -revealEnergy z m r := by
    unfold insertSum revealEnergy
    rw [mul_sum, mul_sum, ← sum_sub_distrib, ← sum_sub_distrib, ← sum_neg_distrib]
    apply sum_congr rfl
    intro v _
    by_cases hv : v ∉ r <;> simp [hv]
    ring
  calc
    _ = ∑ r, (2 * m r * insertSum (fun q => z q * m q) r -
        m r ^ 2 * insertSum z r - insertSum (fun q => z q * m q ^ 2) r) := by
      simp only [sum_sub_distrib, sum_insertSum]
    _ = _ := by simp_rw [he]; rw [sum_neg_distrib]

/-- Exact derivative of the full expected posterior variance, including changing posterior means. -/
theorem hasDerivAt_thinningVariance_revealEnergy (μ : FiniteLaw (Finset V))
    {θ : ℝ} (hθ : 0 < θ) (hθ1 : θ < 1) (f : Finset V → ℝ) :
    HasDerivAt (fun x => thinningVariance μ x f)
      ((∑ r, revealEnergy (thinningMass μ θ) (fun r => thinningMean μ θ r f) r) /
        (1 - θ)) θ := by
  have h := (hasDerivAt_const θ (μ.expectation (fun s => f s^2))).sub
    (HasDerivAt.fun_sum (fun r (_ : r ∈ (univ : Finset (Finset V))) =>
      hasDerivAt_thinningEnergy μ hθ hθ1 r f))
  convert h using 1
  · rfl
  · simp only [zero_sub, ← sum_div]
    simp_rw [thinningMoment_eq_mass_mul_mean μ hθ hθ1,
      thinningEnergy_eq_mass_mul_mean_sq]
    rw [sum_revealEnergy_identity]
    ring

end HardCoreActivityThreshold
