import HardCoreActivityThreshold.FiniteProbability

namespace MeanMaximumForests
open Finset HardCoreActivityThreshold
attribute [local instance] Classical.propDecidable

/-- Push a finite probability law forward under an arbitrary statistic. -/
noncomputable def finiteLawImage {Ω Ξ : Type*} [Fintype Ω] [Fintype Ξ]
    (μ : FiniteLaw Ω) (f : Ω → Ξ) : FiniteLaw Ξ := by
  classical
  exact {
    mass := fun y => ∑ x ∈ univ.filter (fun x => f x = y), μ.mass x
    nonneg := fun _ => sum_nonneg (fun x _ => μ.nonneg x)
    sum_one := (sum_fiberwise univ f μ.mass).trans μ.sum_one }

@[simp] theorem finiteLawImage_mass {Ω Ξ : Type*} [Fintype Ω] [Fintype Ξ]
    (μ : FiniteLaw Ω) (f : Ω → Ξ) (y : Ξ) :
    (finiteLawImage μ f).mass y = μ.expectation (fun x => if f x = y then 1 else 0) := by
  classical
  simp only [finiteLawImage, FiniteLaw.expectation, mul_ite, mul_one, mul_zero, sum_filter]

theorem finiteLawImage_expectation {Ω Ξ : Type*} [Fintype Ω] [Fintype Ξ]
    (μ : FiniteLaw Ω) (f : Ω → Ξ) (g : Ξ → ℝ) :
    (finiteLawImage μ f).expectation g = μ.expectation (fun x => g (f x)) := by
  classical
  unfold FiniteLaw.expectation finiteLawImage
  simp only [sum_mul]
  calc
    _ = ∑ y, ∑ x ∈ univ.filter (fun x => f x = y), μ.mass x * g (f x) := by
      apply sum_congr rfl
      intro y _
      apply sum_congr rfl
      intro x hx
      rw [(mem_filter.mp hx).2]
    _ = _ := sum_fiberwise univ f _

theorem finiteLawImage_variance {Ω Ξ : Type*} [Fintype Ω] [Fintype Ξ]
    (μ : FiniteLaw Ω) (f : Ω → Ξ) (g : Ξ → ℝ) :
    (finiteLawImage μ f).variance g = μ.variance (fun x => g (f x)) := by
  unfold FiniteLaw.variance
  rw [finiteLawImage_expectation, finiteLawImage_expectation]

end MeanMaximumForests
