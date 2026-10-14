import HardCoreActivityThreshold.ThinningVariance

/-! The finite revealing derivative is controlled by actual occupation covariances. -/
namespace HardCoreActivityThreshold
open Finset
attribute [local instance] Classical.propDecidable
variable {V : Type*} [Fintype V] [DecidableEq V]

theorem thinningMoment_eq_weighted_posterior (μ : FiniteLaw (Finset V))
    {θ : ℝ} (hθ : 0 ≤ θ) (hθ1 : θ ≤ 1) (r : Finset V) (f : Finset V → ℝ) :
    thinningMoment μ θ r f = thinningMass μ θ r *
      ((positiveThinning θ hθ hθ1).posterior μ r).expectation f := by
  rw [thinningMass_eq_output μ hθ hθ1,
    ObservationChannel.weighted_posterior_expectation]
  rfl

theorem thinningMean_eq_posterior (μ : FiniteLaw (Finset V))
    {θ : ℝ} (hθ : 0 ≤ θ) (hθ1 : θ ≤ 1) (r : Finset V) (f : Finset V → ℝ)
    (hr : thinningMass μ θ r ≠ 0) :
    thinningMean μ θ r f = ((positiveThinning θ hθ hθ1).posterior μ r).expectation f := by
  unfold thinningMean
  rw [thinningMoment_eq_weighted_posterior μ hθ hθ1 r f]
  exact mul_div_cancel_left₀ _ hr

theorem thinningMoment_insert (μ : FiniteLaw (Finset V)) {θ : ℝ} (hθ : 0 < θ)
    (r : Finset V) {v : V} (hv : v ∉ r) (f : Finset V → ℝ) :
    thinningMoment μ θ (insert v r) f =
      ((1 - θ) / θ) * thinningMoment μ θ r (fun s => f s * occupation v s) := by
  unfold thinningMoment
  simp_rw [thinningKernel_insert hθ _ r hv, mul_sum]
  apply sum_congr rfl
  intro s _
  ring

theorem thinningMass_insert (μ : FiniteLaw (Finset V)) {θ : ℝ} (hθ : 0 < θ)
    (hθ1 : θ ≤ 1) (r : Finset V) {v : V} (hv : v ∉ r) :
    thinningMass μ θ (insert v r) = ((1 - θ) / θ) * thinningMass μ θ r *
      marginal ((positiveThinning θ hθ.le hθ1).posterior μ r) v := by
  unfold thinningMass
  rw [thinningMoment_insert μ hθ r hv]
  simp only [one_mul]
  rw [thinningMoment_eq_weighted_posterior μ hθ.le hθ1]
  simp only [thinningMass, marginal]
  ring

theorem positiveThinning_posterior_fixed (μ : FiniteLaw (Finset V))
    {θ : ℝ} (hθ : 0 < θ) (hθ1 : θ < 1) (r : Finset V)
    (hr : 0 < thinningMass μ θ r) {v : V} (hv : v ∈ r) :
    marginal ((positiveThinning θ hθ.le hθ1.le).posterior μ r) v = 1 := by
  let K := positiveThinning (V := V) θ hθ.le hθ1.le
  have hr' : 0 < (K.output μ).mass r := by
    change 0 < ((positiveThinning θ hθ.le hθ1.le).output μ).mass r
    rw [← thinningMass_eq_output μ hθ.le hθ1.le]
    exact hr
  change (K.posterior μ r).expectation (occupation v) = 1
  rw [← (K.posterior μ r).expectation_const 1]
  apply (K.posterior μ r).expectation_congr_on_support
  intro s hs
  have hp : 0 < μ.mass s * K.kernel s r := by
    rw [← K.weighted_posterior_mass μ r s]
    exact mul_pos hr' hs
  have hk : 0 < K.kernel s r :=
    ((mul_pos_iff.mp hp).resolve_right (fun h => (μ.nonneg s).not_gt h.1)).2
  have hrs : r ⊆ s := (thinningKernel_pos_iff hθ hθ1 s r).mp hk
  simp [occupation, hrs hv]

private theorem reveal_square_identity (c a b m : ℝ) :
    c * a * (b / a - m)^2 = c * (b - m * a)^2 / a := by
  by_cases ha : a = 0
  · simp [ha]
  · field_simp

/-- One reveal-edge's contribution is its normalized occupation-covariance square. -/
theorem thinning_reveal_edge (μ : FiniteLaw (Finset V))
    {θ : ℝ} (hθ : 0 < θ) (hθ1 : θ < 1) (r : Finset V)
    (hr : 0 < thinningMass μ θ r) {v : V} (hv : v ∉ r) (f : Finset V → ℝ) :
    thinningMass μ θ (insert v r) *
      (thinningMean μ θ (insert v r) f - thinningMean μ θ r f)^2 =
      ((1 - θ) / θ) * thinningMass μ θ r *
        (((positiveThinning θ hθ.le hθ1.le).posterior μ r).covariance f (occupation v)^2 /
          marginal ((positiveThinning θ hθ.le hθ1.le).posterior μ r) v) := by
  let ν := (positiveThinning (V := V) θ hθ.le hθ1.le).posterior μ r
  have hratio : ((1 - θ) / θ) * thinningMass μ θ r ≠ 0 :=
    (mul_pos (div_pos (sub_pos.mpr hθ1) hθ) hr).ne'
  have hmean : thinningMean μ θ (insert v r) f =
      ν.expectation (fun s => f s * occupation v s) / marginal ν v := by
    unfold thinningMean
    rw [thinningMoment_insert μ hθ r hv,
      thinningMoment_eq_weighted_posterior μ hθ.le hθ1.le,
      thinningMass_insert μ hθ hθ1.le r hv]
    rw [← mul_assoc, mul_div_mul_left _ _ hratio]
  rw [thinningMass_insert μ hθ hθ1.le r hv, hmean,
    thinningMean_eq_posterior μ hθ.le hθ1.le r f hr.ne',
    FiniteLaw.covariance_eq_mixed_moment]
  change _ = ((1 - θ) / θ) * thinningMass μ θ r *
    ((ν.expectation (fun s => f s * occupation v s) - ν.expectation f * marginal ν v)^2 /
      marginal ν v)
  rw [reveal_square_identity]
  ring

/-- The complete finite-sum derivative, with all conditional means accounted for. -/
theorem revealEnergy_eq_covariances (μ : FiniteLaw (Finset V))
    {θ : ℝ} (hθ : 0 < θ) (hθ1 : θ < 1) (r : Finset V) (f : Finset V → ℝ) :
    revealEnergy (thinningMass μ θ) (fun r => thinningMean μ θ r f) r =
      ((1 - θ) / θ) * thinningMass μ θ r *
        ∑ v, ((positiveThinning θ hθ.le hθ1.le).posterior μ r).covariance f (occupation v)^2 /
          marginal ((positiveThinning θ hθ.le hθ1.le).posterior μ r) v := by
  have hznonneg : 0 ≤ thinningMass μ θ r := by
    rw [thinningMass_eq_output μ hθ.le hθ1.le]
    exact ((positiveThinning θ hθ.le hθ1.le).output μ).nonneg r
  by_cases hr : 0 < thinningMass μ θ r
  · unfold revealEnergy
    rw [mul_sum]
    apply sum_congr rfl
    intro v _
    by_cases hv : v ∉ r
    · rw [ite_eq_left hv]
      exact thinning_reveal_edge μ hθ hθ1 r hr hv f
    · rw [ite_eq_right hv]
      have hm := positiveThinning_posterior_fixed μ hθ hθ1 r hr (not_not.mp hv)
      have hvar : ((positiveThinning θ hθ.le hθ1.le).posterior μ r).variance (occupation v) = 0 := by
        rw [occupation_variance, hm]
        norm_num
      rw [FiniteLaw.covariance_eq_zero_of_variance_eq_zero _ f _ hvar]
      simp
  · have hr0 : thinningMass μ θ r = 0 := le_antisymm (le_of_not_gt hr) hznonneg
    rw [hr0, mul_zero, zero_mul]
    apply sum_eq_zero
    intro v _
    by_cases hv : v ∉ r
    · rw [ite_eq_left hv, thinningMass_insert μ hθ hθ1.le r hv, hr0, mul_zero, zero_mul, zero_mul]
    · rw [ite_eq_right hv]

end HardCoreActivityThreshold
