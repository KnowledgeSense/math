import CircleKernel.SpectralConvergence
import Mathlib.Topology.Algebra.InfiniteSum.NatInt

noncomputable section
open Complex MeasureTheory Filter
namespace CircleKernel

/-- The original bilateral Fourier spectral series, with its zero mode included. -/
def bilateralSpectralKernel (t : ℂ) (φ θ : ℝ) : ℂ :=
  (1/(2*Real.pi))*∑'n:ℤ,Complex.exp (Complex.I*n*(φ-θ))*
    Complex.exp (-(circleEigenvalue n.natAbs:ℂ)*t)

theorem spectral_bilateral_diagonal_summable (t : ℂ) (ht : 1/2<t.re) :
    Summable (fun n:ℤ=>Complex.exp (-(circleEigenvalue n.natAbs:ℂ)*t)) := by
  apply summable_int_iff_summable_nat_and_neg.mpr
  constructor <;> simpa using spectral_summable t ht

theorem bilateralSpectralKernel_diagonal (t : ℂ) (φ : ℝ) (ht : 1/2<t.re) :
    bilateralSpectralKernel t φ φ=diagonalSpectralKernel t := by
  have he : Function.Even (fun n:ℤ=>Complex.exp (-(circleEigenvalue n.natAbs:ℂ)*t)) := by
    intro n
    simp
  unfold bilateralSpectralKernel
  simp only [sub_self,mul_zero,Complex.exp_zero,one_mul]
  rw [tsum_int_eq_zero_add_two_mul_tsum_pnat he (spectral_bilateral_diagonal_summable t ht)]
  simp only [Int.natAbs_zero,circleEigenvalue_zero,Complex.ofReal_zero,neg_zero,zero_mul,Complex.exp_zero]
  change 1/(2*Real.pi)*(1+2 • ∑'n:ℕ+,Complex.exp (-(circleEigenvalue (n:ℕ):ℂ)*t))=_
  rw [tsum_pnat_eq_tsum_succ (f:=fun n:ℕ=>Complex.exp (-(circleEigenvalue n:ℂ)*t))]
  simp only [nsmul_eq_mul]
  unfold diagonalSpectralKernel
  ring

end CircleKernel
