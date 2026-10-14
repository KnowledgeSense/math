import CircleKernel.UniformSpectralRemainder
import Mathlib.Analysis.SpecialFunctions.Pow.Complex

noncomputable section
open Filter Asymptotics Finset
open scoped Topology
namespace CircleKernel

def dirichletExponential (n : ℕ) (s : ℂ) : ℂ := Complex.exp (-(Real.log n : ℂ)*s)

theorem dirichletExponential_norm (n : ℕ) (hn : 0 < n) (s : ℂ) :
    ‖dirichletExponential n s‖ = (n : ℝ)^(-s.re) := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  rw [dirichletExponential, Complex.norm_exp, Real.rpow_def_of_pos hn0]
  congr 1
  simp only [Complex.mul_re, Complex.neg_re, Complex.ofReal_re,
    Complex.neg_im, Complex.ofReal_im, neg_zero, zero_mul, sub_zero]
  ring

theorem dirichletExponential_norm_le (n : ℕ) (hn : 1 ≤ n) (s : ℂ) (σ : ℝ)
    (hs : σ ≤ s.re) : ‖dirichletExponential n s‖ ≤ (n : ℝ)^(-σ) := by
  rw [dirichletExponential_norm n (by omega)]
  apply Real.rpow_le_rpow_of_exponent_le
  · exact_mod_cast hn
  · linarith

theorem dirichletExponential_add (n : ℕ) (s t : ℂ) :
    dirichletExponential n (s+t) = dirichletExponential n s*dirichletExponential n t := by
  simp only [dirichletExponential, mul_add, Complex.exp_add]

theorem dirichletExponential_nat (n j : ℕ) (hn : 0 < n) :
    dirichletExponential n (j : ℂ) = 1/(n : ℂ)^j := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  rw [dirichletExponential, neg_mul, Complex.exp_neg, mul_comm, Complex.exp_nat_mul]
  rw [← Complex.ofReal_exp, Real.exp_log hn0]
  simp only [Complex.ofReal_natCast, one_div]

theorem dirichletExponential_differentiable (n : ℕ) : Differentiable ℂ (dirichletExponential n) := by
  unfold dirichletExponential
  fun_prop

def spectralRemainderTerm (M n : ℕ) (t : ℂ) : ℂ :=
  Complex.exp (-(spectralConstant : ℂ)*t)*dirichletExponential n (2*t)*
    (Complex.exp (-t*(spectralCorrection n : ℂ))-
      ∑ j ∈ range M, (complexResiduePolynomial j).eval t/(n : ℂ)^j)

theorem spectralRemainderTerm_differentiable (M n : ℕ) :
    Differentiable ℂ (spectralRemainderTerm M n) := by
  unfold spectralRemainderTerm dirichletExponential
  fun_prop

end CircleKernel
