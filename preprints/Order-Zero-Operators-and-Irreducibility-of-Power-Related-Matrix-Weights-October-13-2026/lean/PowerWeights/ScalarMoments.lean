import PowerWeights.MomentAlgebra
import Mathlib.Analysis.Polynomial.Basic
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Measure.OpenPos
import Mathlib.Topology.Algebra.Module.PerfectSpace

namespace PowerWeights

open Polynomial MeasureTheory
open scoped BigOperators

 theorem polynomial_zero_of_ae {I : Set ℝ} (hI : IsOpen I) (hne : I.Nonempty)
    (p : ℂ[X]) (hp : (fun x : ℝ => p.eval (x : ℂ)) =ᵐ[volume.restrict I] fun _ => 0) : p=0 := by
  have he : Set.EqOn (fun x : ℝ => p.eval (x : ℂ)) (fun _ => (0 : ℂ)) I :=
    MeasureTheory.Measure.eqOn_open_of_ae_eq hp hI
      (p.continuous.comp Complex.continuous_ofReal).continuousOn continuous_const.continuousOn
  obtain ⟨x,hx⟩ := hne
  have hInf : I.Infinite := infinite_of_mem_nhds x (hI.mem_nhds hx)
  apply p.eq_zero_of_infinite_isRoot
  apply (hInf.image Complex.ofReal_injective.injOn).mono
  rintro z ⟨y,hy,rfl⟩
  exact he hy

 theorem conjugate_eval_real (p : ℂ[X]) (x : ℝ) :
    star (p.eval (x : ℂ)) = ∑ j ∈ p.support, star (p.coeff j)*(x : ℂ)^j := by
  rw [Polynomial.eval_eq_sum]
  simp [Polynomial.sum,star_mul,mul_comm]

 theorem weighted_square_expansion (p : ℂ[X]) (w x : ℝ) :
    (w : ℂ)*p.eval (x : ℂ)*star (p.eval (x : ℂ)) =
      ∑ j ∈ p.support, star (p.coeff j)*((w : ℂ)*(x : ℂ)^j*p.eval (x : ℂ)) := by
  rw [conjugate_eval_real,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  ring

/-- A polynomial is determined by its weighted moments on any nonempty open
interval, even when the scalar weight is moment-indeterminate. -/
theorem polynomial_zero_of_weighted_moments {I : Set ℝ} (hI : IsOpen I)
    (hne : I.Nonempty) (w : ℝ → ℝ) (p : ℂ[X])
    (hw : ∀ᵐ x ∂volume.restrict I, 0<w x)
    (hint : ∀ j, Integrable (fun x : ℝ => (w x : ℂ)*(x : ℂ)^j*p.eval (x : ℂ))
      (volume.restrict I))
    (hzero : ∀ j, ∫ x in I, (w x : ℂ)*(x : ℂ)^j*p.eval (x : ℂ)=0) : p=0 := by
  let μ := volume.restrict I
  let f : ℝ → ℂ := fun x => (w x : ℂ)*p.eval (x : ℂ)*star (p.eval (x : ℂ))
  have hex : f = fun x => ∑ j ∈ p.support,
      star (p.coeff j)*((w x : ℂ)*(x : ℂ)^j*p.eval (x : ℂ)) := by
    funext x
    exact weighted_square_expansion p (w x) x
  have hfi : Integrable f μ := by
    rw [hex]
    exact integrable_finsetSum _ fun j _ => (hint j).const_mul _
  have hfzero : ∫ x, f x ∂μ = 0 := by
    rw [hex,integral_finsetSum]
    · simp [integral_const_mul,hzero,μ]
    · intro j _
      exact (hint j).const_mul _
  let g : ℝ → ℝ := fun x => w x * Complex.normSq (p.eval (x : ℂ))
  have hfg : ∀ x, f x=(g x : ℂ) := by
    intro x
    dsimp [f,g]
    rw [mul_assoc,Complex.mul_conj]
    simp
  have hgi : Integrable g μ := by
    have hr := hfi.re
    change Integrable (fun x => (f x).re) μ at hr
    simpa only [hfg,Complex.ofReal_re] using hr
  have hgzero : ∫ x, g x ∂μ = 0 := by
    apply Complex.ofReal_injective
    rw [← integral_complex_ofReal]
    simpa only [← hfg,Complex.ofReal_zero] using hfzero
  have hg_nonneg : 0 ≤ᵐ[μ] g := by
    filter_upwards [hw] with x hx
    exact mul_nonneg hx.le (Complex.normSq_nonneg _)
  have hg_ae := (integral_eq_zero_iff_of_nonneg_ae hg_nonneg hgi).mp hgzero
  apply polynomial_zero_of_ae hI hne
  filter_upwards [hw,hg_ae] with x hx hgx
  have hnorm : Complex.normSq (p.eval (x : ℂ))=0 :=
    (mul_eq_zero.mp hgx).resolve_left (ne_of_gt hx)
  exact Complex.normSq_eq_zero.mp hnorm

end PowerWeights
