import HardCoreActivityThreshold.BooleanConfigurations
import HardCoreActivityThreshold.GapLower
import Mathlib.Data.Finset.SymmDiff

/-! Relabeling occupied and vacant values preserves the actual heat-bath conditional variances. -/
namespace HardCoreActivityThreshold
open Finset
open scoped symmDiff
attribute [local instance] Classical.propDecidable
variable {V : Type*} [Fintype V] [DecidableEq V]

omit [DecidableEq V] in
theorem FiniteLaw.mapEquiv_variance (μ : FiniteLaw (Finset V))
    (e : Finset V ≃ Finset V) (f : Finset V → ℝ) :
    (μ.mapEquiv e).variance f = μ.variance (fun s => f (e s)) := by
  rw [FiniteLaw.variance_eq_second_moment, FiniteLaw.variance_eq_second_moment,
    FiniteLaw.mapEquiv_expectation, FiniteLaw.mapEquiv_expectation]

theorem mapEquiv_fiberMass (μ : FiniteLaw (Finset V)) (e : Finset V ≃ Finset V)
    (houtside : ∀ v s t, sameOutside v (e s) (e t) ↔ sameOutside v s t)
    (v : V) (s : Finset V) : fiberMass (μ.mapEquiv e) v (e s) = fiberMass μ v s := by
  unfold fiberMass FiniteLaw.eventMass
  rw [← e.sum_comp (fun t => if sameOutside v (e s) t then (μ.mapEquiv e).mass t else 0)]
  simp only [FiniteLaw.mapEquiv, e.symm_apply_apply, houtside]

theorem mapEquiv_singleSiteKernel (μ : FiniteLaw (Finset V)) (e : Finset V ≃ Finset V)
    (houtside : ∀ v s t, sameOutside v (e s) (e t) ↔ sameOutside v s t)
    (v : V) (s t : Finset V) :
    singleSiteKernel (μ.mapEquiv e) v (e s) (e t) = singleSiteKernel μ v s t := by
  unfold singleSiteKernel
  simp only [houtside, mapEquiv_fiberMass μ e houtside, e.injective.eq_iff,
    ]
  simp only [FiniteLaw.mapEquiv, e.symm_apply_apply]

theorem mapEquiv_siteOperator (μ : FiniteLaw (Finset V)) (e : Finset V ≃ Finset V)
    (houtside : ∀ v s t, sameOutside v (e s) (e t) ↔ sameOutside v s t)
    (v : V) (f : Finset V → ℝ) (s : Finset V) :
    siteOperator (μ.mapEquiv e) v f (e s) = siteOperator μ v (fun t => f (e t)) s := by
  unfold siteOperator
  rw [← e.sum_comp (fun t => singleSiteKernel (μ.mapEquiv e) v (e s) t * f t)]
  simp only [mapEquiv_singleSiteKernel μ e houtside]

theorem mapEquiv_siteConditionalVariance (μ : FiniteLaw (Finset V))
    (e : Finset V ≃ Finset V)
    (houtside : ∀ v s t, sameOutside v (e s) (e t) ↔ sameOutside v s t)
    (v : V) (f : Finset V → ℝ) :
    siteConditionalVariance (μ.mapEquiv e) v f =
      siteConditionalVariance μ v (fun t => f (e t)) := by
  unfold siteConditionalVariance
  rw [FiniteLaw.mapEquiv_expectation]
  simp only [mapEquiv_siteOperator μ e houtside]

theorem VarianceTensorization.mapEquiv {μ : FiniteLaw (Finset V)} {C : ℝ}
    (h : VarianceTensorization μ C) (e : Finset V ≃ Finset V)
    (houtside : ∀ v s t, sameOutside v (e s) (e t) ↔ sameOutside v s t) :
    VarianceTensorization (μ.mapEquiv e) C := by
  intro f
  rw [FiniteLaw.mapEquiv_variance]
  simp only [mapEquiv_siteConditionalVariance μ e houtside]
  exact h (fun s => f (e s))

noncomputable def configurationFlip (occupied : Finset V) : Finset V ≃ Finset V where
  toFun s := s ∆ occupied
  invFun s := s ∆ occupied
  left_inv s := symmDiff_symmDiff_cancel_right occupied s
  right_inv s := symmDiff_symmDiff_cancel_right occupied s

omit [Fintype V] in
theorem erase_symmDiff (s t : Finset V) (v : V) :
    (s ∆ t).erase v = s.erase v ∆ t.erase v := by
  ext w
  by_cases hw : w = v <;> simp [mem_symmDiff, mem_erase, hw]

omit [Fintype V] in
theorem configurationFlip_sameOutside (occupied : Finset V) (v : V) (s t : Finset V) :
    sameOutside v (configurationFlip occupied s) (configurationFlip occupied t) ↔
      sameOutside v s t := by
  change (s ∆ occupied).erase v = (t ∆ occupied).erase v ↔ s.erase v = t.erase v
  rw [erase_symmDiff, erase_symmDiff]
  constructor
  · intro h
    have he := congrArg (fun a : Finset V => a ∆ occupied.erase v) h
    simpa only [symmDiff_symmDiff_cancel_right] using he
  · intro h
    rw [h]

theorem VarianceTensorization.flip {μ : FiniteLaw (Finset V)} {C : ℝ}
    (h : VarianceTensorization μ C) (occupied : Finset V) :
    VarianceTensorization (μ.mapEquiv (configurationFlip occupied)) C :=
  h.mapEquiv (configurationFlip occupied) (configurationFlip_sameOutside occupied)

end HardCoreActivityThreshold
