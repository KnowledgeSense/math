import HonestEmbeddingDimension.AnalyticPlane
import Mathlib.RingTheory.PowerSeries.Inverse

open Filter
open scoped Topology

namespace HonestEmbeddingDimension

theorem analyticTaylor_congr {f g : ℂ → ℂ} (h : f =ᶠ[𝓝 0] g) :
    analyticTaylor f = analyticTaylor g := by
  ext n
  simp only [coeff_analyticTaylor, h.iteratedDeriv_eq n]

theorem analyticTaylor_neg {f : ℂ → ℂ} (hf : AnalyticAt ℂ f 0) :
    analyticTaylor (fun t => -f t) = -analyticTaylor f := by
  have h := analyticTaylor_mul (analyticAt_const : AnalyticAt ℂ (fun _ : ℂ => (-1 : ℂ)) 0) hf
  simpa using h

theorem analyticTaylor_sub {f g : ℂ → ℂ} (hf : AnalyticAt ℂ f 0) (hg : AnalyticAt ℂ g 0) :
    analyticTaylor (fun t => f t-g t) = analyticTaylor f-analyticTaylor g := by
  simp only [sub_eq_add_neg]
  rw [analyticTaylor_add (g := fun t => -g t) hf hg.neg,analyticTaylor_neg hg]

/-- Inversion of an actual nonvanishing analytic germ agrees with formal inversion. -/
theorem analyticTaylor_inv {f : ℂ → ℂ} (hf : AnalyticAt ℂ f 0) (h0 : f 0 ≠ 0) :
    analyticTaylor (fun t => (f t)⁻¹) = (analyticTaylor f)⁻¹ := by
  apply (PowerSeries.eq_inv_iff_mul_eq_one (by simpa using h0)).mpr
  rw [← analyticTaylor_mul (f := fun t => (f t)⁻¹) (g := f) (hf.inv h0) hf]
  have he : (fun t => (f t)⁻¹*f t) =ᶠ[𝓝 0] (fun _ => 1) := by
    filter_upwards [hf.continuousAt.eventually_ne h0] with t ht
    exact inv_mul_cancel₀ ht
  rw [analyticTaylor_congr he]
  simp

theorem analyticTaylor_div {f g : ℂ → ℂ} (hf : AnalyticAt ℂ f 0) (hg : AnalyticAt ℂ g 0)
    (h0 : g 0 ≠ 0) : analyticTaylor (fun t => f t/g t) = analyticTaylor f*(analyticTaylor g)⁻¹ := by
  simp only [div_eq_mul_inv]
  rw [analyticTaylor_mul (f := f) (g := fun t => (g t)⁻¹) hf (hg.inv h0),analyticTaylor_inv hg h0]

/-- The convergent denominator used by the explicit multiplicity-five realizations. -/
theorem analyticAt_geometric_quotient (b δ : ℕ) (hδ : 0 < δ) :
    AnalyticAt ℂ (fun t : ℂ => t^b/(1-t^δ)) 0 := by
  apply (analyticAt_id.pow b).div (analyticAt_const.sub (analyticAt_id.pow δ))
  simp [Nat.ne_of_gt hδ]

theorem analyticTaylor_geometric_quotient (b δ : ℕ) (hδ : 0 < δ) :
    analyticTaylor (fun t : ℂ => t^b/(1-t^δ)) =
      PowerSeries.X^b*(1-PowerSeries.X^δ)⁻¹ := by
  rw [analyticTaylor_div (f := fun t : ℂ => t^b) (g := fun t => 1-t^δ) (analyticAt_id.pow b) (analyticAt_const.sub (analyticAt_id.pow δ))
    (by simp [Nat.ne_of_gt hδ])]
  rw [analyticTaylor_sub (f := fun _ : ℂ => 1) (g := fun t => t^δ) analyticAt_const (analyticAt_id.pow δ)]
  simp [analyticTaylor_pow (f := fun t : ℂ => t) analyticAt_id]

end HonestEmbeddingDimension
