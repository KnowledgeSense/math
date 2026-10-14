import HardCoreActivityThreshold.FiniteProbability
import Mathlib.Algebra.Order.BigOperators.Ring.Finset

/-! Finite-law variance identities and comparison inequalities. -/
namespace HardCoreActivityThreshold.FiniteLaw
open Finset
variable {Ω : Type*} [Fintype Ω]

theorem expectation_congr_on_support (μ : FiniteLaw Ω) {f g : Ω → ℝ}
    (h : ∀ x, 0 < μ.mass x → f x = g x) : μ.expectation f = μ.expectation g := by
  apply sum_congr rfl
  intro x _
  by_cases hx : 0 < μ.mass x
  · rw [h x hx]
  · have hz : μ.mass x = 0 := le_antisymm (le_of_not_gt hx) (μ.nonneg x)
    rw [hz, zero_mul, zero_mul]

theorem variance_eq_centered (μ : FiniteLaw Ω) (f : Ω → ℝ) (c : ℝ) :
    μ.expectation (fun x => (f x - c)^2) = μ.variance f + (μ.expectation f - c)^2 := by
  have he (x : Ω) : (f x - c)^2 = f x ^ 2 - (2 * c) * f x + c^2 := by ring
  simp_rw [he]
  rw [expectation_add, expectation_sub, expectation_smul, expectation_const,
    variance_eq_second_moment]
  ring

theorem variance_le_centered (μ : FiniteLaw Ω) (f : Ω → ℝ) (c : ℝ) :
    μ.variance f ≤ μ.expectation (fun x => (f x - c)^2) := by
  rw [variance_eq_centered]
  exact le_add_of_nonneg_right (sq_nonneg _)

theorem expectation_mul_sq_le (μ : FiniteLaw Ω) (f g : Ω → ℝ) :
    μ.expectation (fun x => f x * g x)^2 ≤
      μ.expectation (fun x => f x ^ 2) * μ.expectation (fun x => g x ^ 2) := by
  apply sum_sq_le_sum_mul_sum_of_sq_le_mul univ
    (fun x _ => mul_nonneg (μ.nonneg x) (sq_nonneg (f x)))
    (fun x _ => mul_nonneg (μ.nonneg x) (sq_nonneg (g x)))
  intro x _
  exact le_of_eq (by ring)

theorem covariance_sq_le (μ : FiniteLaw Ω) (f g : Ω → ℝ) :
    μ.covariance f g ^ 2 ≤ μ.variance f * μ.variance g :=
  μ.expectation_mul_sq_le (fun x => f x - μ.expectation f)
    (fun x => g x - μ.expectation g)

theorem covariance_eq_zero_of_variance_eq_zero (μ : FiniteLaw Ω)
    (f g : Ω → ℝ) (hg : μ.variance g = 0) : μ.covariance f g = 0 := by
  have h := μ.covariance_sq_le f g
  rw [hg, mul_zero] at h
  nlinarith [sq_nonneg (μ.covariance f g)]

theorem covariance_smul_right (μ : FiniteLaw Ω) (f g : Ω → ℝ) (c : ℝ) :
    μ.covariance f (fun x => c * g x) = c * μ.covariance f g := by
  rw [covariance_eq_mixed_moment, covariance_eq_mixed_moment, expectation_smul]
  have h : μ.expectation (fun x => f x * (c * g x)) =
      c * μ.expectation (fun x => f x * g x) := by
    rw [← expectation_smul]
    congr 1
    funext x
    ring
  rw [h]
  ring

theorem covariance_sub_const_right (μ : FiniteLaw Ω) (f g : Ω → ℝ) (c : ℝ) :
    μ.covariance f (fun x => g x - c) = μ.covariance f g := by
  rw [covariance_eq_mixed_moment, covariance_eq_mixed_moment, expectation_sub,
    expectation_const]
  have he (x : Ω) : f x * (g x - c) = f x * g x - c * f x := by ring
  simp_rw [he]
  rw [expectation_sub, expectation_smul]
  ring

theorem covariance_sum_right {ι : Type*} [Fintype ι] (μ : FiniteLaw Ω)
    (f : Ω → ℝ) (g : ι → Ω → ℝ) :
    μ.covariance f (fun x => ∑ i, g i x) = ∑ i, μ.covariance f (g i) := by
  simp_rw [covariance_eq_mixed_moment, mul_sum]
  rw [expectation_sum, expectation_sum, mul_sum, sum_sub_distrib]

theorem expectation_eq_zero_of_nonneg (μ : FiniteLaw Ω) (f : Ω → ℝ)
    (hf : ∀ x, 0 ≤ f x) (h : μ.expectation f = 0) {x : Ω} (hx : 0 < μ.mass x) :
    f x = 0 := by
  have hp : μ.mass x * f x = 0 :=
    (sum_eq_zero_iff_of_nonneg (fun x _ => mul_nonneg (μ.nonneg x) (hf x))).mp h x (mem_univ x)
  exact (mul_eq_zero.mp hp).resolve_left hx.ne'

section Mixture
variable {ι : Type*} [Fintype ι]

/-- A finite mixture identity at the level of genuine normalized probability masses. -/
theorem expectation_mixture (μ : FiniteLaw Ω) (ν : ι → FiniteLaw Ω) (w : ι → ℝ)
    (hmix : ∀ x, μ.mass x = ∑ i, w i * (ν i).mass x) (f : Ω → ℝ) :
    μ.expectation f = ∑ i, w i * (ν i).expectation f := by
  unfold expectation
  simp_rw [hmix, sum_mul, mul_sum]
  rw [sum_comm]
  apply sum_congr rfl
  intro i _
  apply sum_congr rfl
  intro x _
  ring

/-- Total variance for a finite mixture, without assuming full support. -/
theorem variance_mixture (μ : FiniteLaw Ω) (ν : ι → FiniteLaw Ω) (w : ι → ℝ)
    (hmix : ∀ x, μ.mass x = ∑ i, w i * (ν i).mass x) (f : Ω → ℝ) :
    μ.variance f = (∑ i, w i * (ν i).variance f) +
      ∑ i, w i * ((ν i).expectation f - μ.expectation f)^2 := by
  change μ.expectation (fun x => (f x - μ.expectation f)^2) = _
  rw [expectation_mixture μ ν w hmix]
  simp_rw [variance_eq_centered, mul_add, sum_add_distrib]

theorem variance_mixture_le (μ : FiniteLaw Ω) (ν : ι → FiniteLaw Ω) (w : ι → ℝ)
    (hw : ∀ i, 0 ≤ w i) (hmix : ∀ x, μ.mass x = ∑ i, w i * (ν i).mass x)
    (f : Ω → ℝ) : (∑ i, w i * (ν i).variance f) ≤ μ.variance f := by
  rw [variance_mixture μ ν w hmix]
  exact le_add_of_nonneg_right (sum_nonneg (fun i _ => mul_nonneg (hw i) (sq_nonneg _)))

end Mixture
end HardCoreActivityThreshold.FiniteLaw
