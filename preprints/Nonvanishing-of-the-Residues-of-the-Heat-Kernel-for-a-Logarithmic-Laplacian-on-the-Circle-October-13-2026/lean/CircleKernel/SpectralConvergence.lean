import CircleKernel.HarmonicEigenvalues
import Mathlib.Analysis.PSeries

noncomputable section
open Complex MeasureTheory Filter
open scoped Topology
namespace CircleKernel

theorem spectral_norm_bound (t : ℂ) (ht : 0<t.re) :
    ∀ᶠn:ℕ in atTop, ‖Complex.exp (-(circleEigenvalue n:ℂ)*t)‖≤
      Real.exp (-t.re*(spectralConstant-1))*(n:ℝ)^(-2*t.re) := by
  have he := circleEigenvalue_log_limit.eventually_const_lt
    (show spectralConstant-1<spectralConstant by linarith)
  filter_upwards [he,eventually_ge_atTop 1] with n hn hn1
  have hnR : (0:ℝ)<n := by exact_mod_cast (show 0<n by omega)
  rw [Complex.norm_exp]
  simp only [Complex.mul_re,Complex.neg_re,Complex.ofReal_re,Complex.neg_im,Complex.ofReal_im,
    neg_zero,zero_mul,sub_zero]
  rw [Real.rpow_def_of_pos hnR,← Real.exp_add]
  apply Real.exp_le_exp.mpr
  nlinarith

theorem spectral_summable (t : ℂ) (ht : 1/2<t.re) :
    Summable (fun n:ℕ=>Complex.exp (-(circleEigenvalue n:ℂ)*t)) := by
  have hs : Summable (fun n:ℕ=>(n:ℝ)^(-2*t.re)) :=
    Real.summable_nat_rpow.mpr (by linarith)
  exact (hs.mul_left (Real.exp (-t.re*(spectralConstant-1)))).of_norm_bounded_eventually_nat
    (spectral_norm_bound t (by linarith))

theorem spectral_positive_summable (t : ℂ) (ht : 1/2<t.re) :
    Summable (fun n:ℕ=>Complex.exp (-(circleEigenvalue (n+1):ℂ)*t)) :=
  (spectral_summable t ht).comp_injective Nat.succ_injective

end CircleKernel
