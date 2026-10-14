import Mathlib.Analysis.Meromorphic.Basic
import Mathlib.Analysis.Complex.RemovableSingularity

noncomputable section
open Filter
open scoped Topology
namespace CircleKernel

/-- A finite first-order punctured limit supplies a genuine meromorphic germ. -/
theorem meromorphicAt_of_first_order_limit (f : ℂ → ℂ) (a c : ℂ)
    (hd : ∀ᶠ z in 𝓝[≠] a, DifferentiableAt ℂ f z)
    (hl : Tendsto (fun z => (z-a)*f z) (𝓝[≠] a) (𝓝 c)) : MeromorphicAt f a := by
  let g : ℂ → ℂ := Function.update (fun z => (z-a)*f z) a c
  have hg : AnalyticAt ℂ g a := by
    apply Complex.analyticAt_of_differentiable_on_punctured_nhds_of_continuousAt
    · filter_upwards [hd, self_mem_nhdsWithin] with z hdz hz
      have hz' : z ≠ a := hz
      have he : g =ᶠ[𝓝 z] (fun w => (w-a)*f w) := by
        filter_upwards [eventually_ne_nhds hz'] with w hw
        exact Function.update_of_ne hw _ _
      exact (((differentiableAt_id.sub_const a).mul hdz).congr_of_eventuallyEq he)
    · exact continuousAt_update_same.mpr hl
  have hm : MeromorphicAt (fun z : ℂ => (z-a)⁻¹*g z) a :=
    ((MeromorphicAt.id a).sub (.const a a)).inv.mul hg.meromorphicAt
  apply hm.congr
  filter_upwards [self_mem_nhdsWithin] with z hz
  have hz' : z ≠ a := hz
  dsimp [g]
  rw [Function.update_of_ne hz', ← mul_assoc, inv_mul_cancel₀ (sub_ne_zero.mpr hz'), one_mul]

end CircleKernel
