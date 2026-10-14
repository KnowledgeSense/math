import CircleKernel.ZetaSeries
import CircleKernel.SpectralConvergence

noncomputable section
open Filter Finset
open scoped Topology
namespace CircleKernel

def regularizedKernel (M : ℕ) (t : ℂ) : ℂ :=
  1/(2*Real.pi) + (1/(Real.pi : ℂ)) *
    (Complex.exp (-(spectralConstant : ℂ)*t) *
      (∑ j ∈ range M, (complexResiduePolynomial j).eval t*riemannZeta (2*t+j)) +
      spectralRemainder M t)

theorem regularizedKernel_initial (M : ℕ) (t : ℂ) (ht : 1/2 < t.re) :
    regularizedKernel M t = diagonalSpectralKernel t := by
  have hz : ∀ j ∈ range M, HasSum (fun n : ℕ =>
      (complexResiduePolynomial j).eval t*dirichletExponential (n+1) (2*t+j))
        ((complexResiduePolynomial j).eval t*riemannZeta (2*t+j)) := by
    intro j hj
    apply (dirichletExponential_hasSum _ _).mul_left
    norm_num [Complex.add_re, Complex.mul_re]
    have hj0 : (0 : ℝ) ≤ j := by positivity
    linarith
  have hsum := (hasSum_sum hz).mul_left (Complex.exp (-(spectralConstant : ℂ)*t))
  have hspec := (spectral_positive_summable t ht).hasSum
  have hdiff := hspec.sub hsum
  have hterm : HasSum (fun n : ℕ => spectralRemainderTerm M (n+1) t)
      ((∑' n : ℕ, Complex.exp (-(circleEigenvalue (n+1) : ℂ)*t)) -
        Complex.exp (-(spectralConstant : ℂ)*t)*
          (∑ j ∈ range M, (complexResiduePolynomial j).eval t*riemannZeta (2*t+j))) := by
    apply hdiff.congr_fun
    intro n
    simp only [spectralRemainderTerm_eq M (n+1) (by omega)]
  have he := hterm.tsum_eq
  change spectralRemainder M t = _ at he
  rw [regularizedKernel, he, diagonalSpectralKernel]
  ring

end CircleKernel
