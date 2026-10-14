import CircleKernel.SpectralRemainder
import Mathlib.NumberTheory.LSeries.RiemannZeta

noncomputable section
open Filter Finset
open scoped Topology
namespace CircleKernel

theorem dirichletExponential_eq_cpow (n : ℕ) (hn : 0 < n) (s : ℂ) :
    dirichletExponential n s = 1/(n : ℂ)^s := by
  have hn0 : (n : ℂ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hn
  rw [dirichletExponential, Complex.cpow_def_of_ne_zero hn0, one_div, ← Complex.exp_neg]
  rw [Complex.ofReal_log (by positivity), Complex.ofReal_natCast, neg_mul]

theorem dirichletExponential_summable (s : ℂ) (hs : 1 < s.re) :
    Summable (fun n : ℕ => dirichletExponential (n+1) s) := by
  apply Summable.of_norm
  simpa only [dirichletExponential_norm _ (Nat.succ_pos _), Function.comp_def] using
    (Real.summable_nat_rpow.mpr (by linarith : -s.re < -1)).comp_injective Nat.succ_injective

theorem dirichletExponential_hasSum (s : ℂ) (hs : 1 < s.re) :
    HasSum (fun n : ℕ => dirichletExponential (n+1) s) (riemannZeta s) := by
  have he : (∑' n : ℕ, dirichletExponential (n+1) s) = riemannZeta s := by
    rw [zeta_eq_tsum_one_div_nat_add_one_cpow hs]
    apply tsum_congr
    intro n
    simpa only [Nat.cast_add, Nat.cast_one] using dirichletExponential_eq_cpow (n+1) (by omega) s
  rw [← he]
  exact (dirichletExponential_summable s hs).hasSum

theorem spectralRemainderTerm_eq (M n : ℕ) (hn : 0 < n) (t : ℂ) :
    spectralRemainderTerm M n t = Complex.exp (-(circleEigenvalue n : ℂ)*t) -
      Complex.exp (-(spectralConstant : ℂ)*t) *
        ∑ j ∈ range M, (complexResiduePolynomial j).eval t * dirichletExponential n (2*t+j) := by
  have he : Complex.exp (-(spectralConstant : ℂ)*t)*dirichletExponential n (2*t)*
      Complex.exp (-t*(spectralCorrection n : ℂ)) = Complex.exp (-(circleEigenvalue n : ℂ)*t) := by
    simp only [dirichletExponential, ← Complex.exp_add, spectralCorrection]
    congr 1
    push_cast
    ring
  rw [spectralRemainderTerm, mul_sub, he]
  congr 1
  rw [mul_assoc]
  simp_rw [mul_sum]
  apply sum_congr rfl
  intro j hj
  rw [dirichletExponential_add, dirichletExponential_nat n j hn]
  ring

end CircleKernel
