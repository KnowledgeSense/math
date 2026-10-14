import HardCoreActivityThreshold.FiniteVariance

/-! Finite observation channels, including zero-probability observations. -/
namespace HardCoreActivityThreshold
open Finset

/-- A genuine finite conditional distribution of observations given configurations. -/
structure ObservationChannel (Ω A : Type*) [Fintype A] where
  kernel : Ω → A → ℝ
  nonneg : ∀ x a, 0 ≤ kernel x a
  sum_one : ∀ x, ∑ a, kernel x a = 1

namespace ObservationChannel
variable {Ω A : Type*} [Fintype Ω] [Fintype A]

/-- The normalized law of the observation. -/
noncomputable def output (K : ObservationChannel Ω A) (μ : FiniteLaw Ω) : FiniteLaw A where
  mass a := ∑ x, μ.mass x * K.kernel x a
  nonneg a := sum_nonneg (fun x _ => mul_nonneg (μ.nonneg x) (K.nonneg x a))
  sum_one := by
    rw [sum_comm]
    simp_rw [← mul_sum, K.sum_one, mul_one]
    exact μ.sum_one

/-- The posterior is Bayes' formula on positive-probability observations. At null observations,
its arbitrary completion is the original law, and every weighted formula ignores this completion. -/
noncomputable def posterior (K : ObservationChannel Ω A) (μ : FiniteLaw Ω) (a : A) :
    FiniteLaw Ω := by
  classical
  exact if h : 0 < (K.output μ).mass a then
    { mass := fun x => μ.mass x * K.kernel x a / (K.output μ).mass a
      nonneg := fun x => div_nonneg (mul_nonneg (μ.nonneg x) (K.nonneg x a)) h.le
      sum_one := by rw [← sum_div]; exact div_self h.ne' }
    else μ

theorem posterior_mass (K : ObservationChannel Ω A) (μ : FiniteLaw Ω) (a : A)
    (ha : 0 < (K.output μ).mass a) (x : Ω) :
    (K.posterior μ a).mass x = μ.mass x * K.kernel x a / (K.output μ).mass a := by
  simp [posterior, ha]

theorem weighted_posterior_mass (K : ObservationChannel Ω A) (μ : FiniteLaw Ω)
    (a : A) (x : Ω) :
    (K.output μ).mass a * (K.posterior μ a).mass x = μ.mass x * K.kernel x a := by
  by_cases ha : 0 < (K.output μ).mass a
  · rw [posterior_mass K μ a ha]
    exact mul_div_cancel₀ _ ha.ne'
  · have hz : (K.output μ).mass a = 0 :=
      le_antisymm (le_of_not_gt ha) ((K.output μ).nonneg a)
    have hx : μ.mass x * K.kernel x a = 0 :=
      (sum_eq_zero_iff_of_nonneg (fun x _ => mul_nonneg (μ.nonneg x)
        (K.nonneg x a))).mp hz x (mem_univ x)
    rw [hz, zero_mul, hx]

/-- Averaging the actual Bayes posteriors gives the original law. -/
theorem posterior_mixture (K : ObservationChannel Ω A) (μ : FiniteLaw Ω) (x : Ω) :
    μ.mass x = ∑ a, (K.output μ).mass a * (K.posterior μ a).mass x := by
  simp_rw [weighted_posterior_mass]
  rw [← mul_sum, K.sum_one, mul_one]

/-- Expected conditional variance retained after the observation. -/
noncomputable def retainedVariance (K : ObservationChannel Ω A) (μ : FiniteLaw Ω)
    (f : Ω → ℝ) : ℝ := ∑ a, (K.output μ).mass a * (K.posterior μ a).variance f

theorem retainedVariance_nonneg (K : ObservationChannel Ω A) (μ : FiniteLaw Ω)
    (f : Ω → ℝ) : 0 ≤ K.retainedVariance μ f :=
  sum_nonneg (fun a _ => mul_nonneg ((K.output μ).nonneg a)
    ((K.posterior μ a).variance_nonneg f))

theorem retainedVariance_le (K : ObservationChannel Ω A) (μ : FiniteLaw Ω)
    (f : Ω → ℝ) : K.retainedVariance μ f ≤ μ.variance f :=
  μ.variance_mixture_le (K.posterior μ) (K.output μ).mass (K.output μ).nonneg
    (K.posterior_mixture μ) f

/-- Every positive-weight posterior is supported inside the original support. -/
theorem posterior_support (K : ObservationChannel Ω A) (μ : FiniteLaw Ω)
    {a : A} (ha : 0 < (K.output μ).mass a) {x : Ω}
    (hx : 0 < (K.posterior μ a).mass x) : 0 < μ.mass x := by
  have he := K.weighted_posterior_mass μ a x
  have hp : 0 < μ.mass x * K.kernel x a := by rw [← he]; exact mul_pos ha hx
  exact (mul_pos_iff.mp hp).resolve_right (fun h => (μ.nonneg x).not_gt h.1) |>.1

/-- Unnormalized posterior moment. -/
noncomputable def moment (K : ObservationChannel Ω A) (μ : FiniteLaw Ω)
    (f : Ω → ℝ) (a : A) : ℝ := ∑ x, μ.mass x * K.kernel x a * f x

theorem weighted_posterior_expectation (K : ObservationChannel Ω A) (μ : FiniteLaw Ω)
    (a : A) (f : Ω → ℝ) :
    (K.output μ).mass a * (K.posterior μ a).expectation f = K.moment μ f a := by
  unfold FiniteLaw.expectation moment
  rw [mul_sum]
  apply sum_congr rfl
  intro x _
  rw [← mul_assoc, weighted_posterior_mass]

theorem weighted_posterior_variance (K : ObservationChannel Ω A) (μ : FiniteLaw Ω)
    (a : A) (f : Ω → ℝ) :
    (K.output μ).mass a * (K.posterior μ a).variance f =
      K.moment μ (fun x => f x ^ 2) a - (K.moment μ f a)^2 / (K.output μ).mass a := by
  rw [FiniteLaw.variance_eq_second_moment, mul_sub, weighted_posterior_expectation,
    ← weighted_posterior_expectation K μ a f]
  by_cases hz : (K.output μ).mass a = 0
  · simp [hz]
  · field_simp

theorem sum_moment (K : ObservationChannel Ω A) (μ : FiniteLaw Ω) (f : Ω → ℝ) :
    (∑ a, K.moment μ f a) = μ.expectation f := by
  unfold moment FiniteLaw.expectation
  rw [sum_comm]
  apply sum_congr rfl
  intro x _
  rw [← sum_mul, ← mul_sum, K.sum_one, mul_one]

theorem retainedVariance_eq_moments (K : ObservationChannel Ω A) (μ : FiniteLaw Ω)
    (f : Ω → ℝ) : K.retainedVariance μ f = μ.expectation (fun x => f x^2) -
      ∑ a, (K.moment μ f a)^2 / (K.output μ).mass a := by
  unfold retainedVariance
  simp_rw [weighted_posterior_variance]
  rw [sum_sub_distrib, sum_moment]

end ObservationChannel
end HardCoreActivityThreshold
