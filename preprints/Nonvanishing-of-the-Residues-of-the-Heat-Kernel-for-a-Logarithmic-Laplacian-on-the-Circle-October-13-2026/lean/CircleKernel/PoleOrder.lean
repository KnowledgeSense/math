import CircleKernel.ResidueNonvanishing
import Mathlib.Analysis.Meromorphic.Order

noncomputable section
open Filter
open scoped Topology
namespace CircleKernel

theorem meromorphicOrderAt_eq_neg_one_of_limit (f : ℂ → ℂ) (a c : ℂ)
    (hf : MeromorphicAt f a) (hc : c ≠ 0)
    (hl : Tendsto (fun z => (z-a)*f z) (𝓝[≠] a) (𝓝 c)) :
    meromorphicOrderAt f a = (-1 : ℤ) := by
  let g : ℂ → ℂ := Function.update (fun z => (z-a)*f z) a c
  have hg : AnalyticAt ℂ g a := by
    apply Complex.analyticAt_of_differentiable_on_punctured_nhds_of_continuousAt
    · filter_upwards [hf.eventually_analyticAt, self_mem_nhdsWithin] with z hdz hz
      have hz' : z ≠ a := hz
      have he : g =ᶠ[𝓝 z] (fun w => (w-a)*f w) := by
        filter_upwards [eventually_ne_nhds hz'] with w hw
        exact Function.update_of_ne hw _ _
      exact (((differentiableAt_id.sub_const a).mul hdz.differentiableAt).congr_of_eventuallyEq he)
    · exact continuousAt_update_same.mpr hl
  apply (meromorphicOrderAt_eq_int_iff hf).mpr
  refine ⟨g,hg,?_,?_⟩
  · simpa [g] using hc
  · filter_upwards [self_mem_nhdsWithin] with z hz
    have hz' : z ≠ a := hz
    dsimp [g]
    rw [Function.update_of_ne hz', zpow_neg_one, ← mul_assoc,
      inv_mul_cancel₀ (sub_ne_zero.mpr hz'), one_mul]

theorem continuedKernel_simple_pole (m : ℕ) :
    meromorphicOrderAt continuedKernel (polePoint m) = (-1 : ℤ) :=
  meromorphicOrderAt_eq_neg_one_of_limit _ _ _ (continuedKernel_meromorphic _)
    (kernelResidue_ne_zero m) (continuedKernel_residue m)

end CircleKernel
