import CircleKernel.Continuation
import CircleKernel.MeromorphicPole
import Mathlib.Analysis.Analytic.Polynomial

noncomputable section
open Filter Finset
open scoped Topology
namespace CircleKernel

theorem riemannZeta_meromorphicAt (s : ℂ) : MeromorphicAt riemannZeta s := by
  by_cases hs : s=1
  · subst s
    apply meromorphicAt_of_first_order_limit _ 1 1 _ riemannZeta_residue_one
    filter_upwards [self_mem_nhdsWithin] with z hz
    exact differentiableAt_riemannZeta hz
  · apply AnalyticAt.meromorphicAt
    apply Complex.analyticAt_iff_eventually_differentiableAt.mpr
    filter_upwards [eventually_ne_nhds hs] with z hz
    exact differentiableAt_riemannZeta hz

theorem spectralRemainder_analyticAt (M : ℕ) (hM : 0 < M) (t : ℂ)
    (ht : 1 < 2*t.re+(M : ℝ)) : AnalyticAt ℂ (spectralRemainder M) t := by
  apply Complex.analyticAt_iff_eventually_differentiableAt.mpr
  have ho : IsOpen {w : ℂ | 1 < 2*w.re+(M : ℝ)} := isOpen_lt continuous_const (by fun_prop)
  filter_upwards [ho.mem_nhds ht] with w hw
  exact spectralRemainder_differentiableAt M hM w hw

theorem regularizedKernel_meromorphicAt (M : ℕ) (hM : 0 < M) (t : ℂ)
    (ht : 1 < 2*t.re+(M : ℝ)) : MeromorphicAt (regularizedKernel M) t := by
  have hs : MeromorphicAt (fun w : ℂ => ∑ j ∈ range M,
      (complexResiduePolynomial j).eval w*riemannZeta (2*w+j)) t := by
    apply MeromorphicAt.fun_sum
    intro j hj
    have hp : AnalyticAt ℂ (fun w : ℂ => (complexResiduePolynomial j).eval w) t := by
      simpa only [Polynomial.aeval_def, Algebra.algebraMap_self, Polynomial.eval₂_id, id_eq] using
        (analyticAt_id (𝕜 := ℂ) (z := t)).aeval_polynomial (complexResiduePolynomial j)
    exact hp.meromorphicAt.mul
      ((riemannZeta_meromorphicAt (2*t+j)).comp_analyticAt (g := fun w : ℂ => 2*w+j) (by fun_prop))
  have hr := (spectralRemainder_analyticAt M hM t ht).meromorphicAt
  have he : MeromorphicAt (fun w : ℂ => Complex.exp (-(spectralConstant : ℂ)*w)) t := by
    apply AnalyticAt.meromorphicAt
    fun_prop
  exact (MeromorphicAt.const _ t).add ((MeromorphicAt.const _ t).mul ((he.mul hs).add hr))

theorem continuedKernel_meromorphic : Meromorphic continuedKernel := by
  intro t
  obtain ⟨hM,hdom⟩ := regularizationOrder_spec t
  apply (regularizedKernel_meromorphicAt _ hM t hdom).congr
  exact (continuedKernel_eventuallyEq _ hM t hdom).symm.filter_mono nhdsWithin_le_nhds

end CircleKernel
