import CircleKernel.RegularizedKernel

noncomputable section
open Filter Finset
open scoped Topology
namespace CircleKernel

theorem spectralRemainder_succ (M : ℕ) (hM : 0 < M) (t : ℂ)
    (ht : 1 < 2*t.re+(M : ℝ)) :
    spectralRemainder M t = spectralRemainder (M+1) t +
      Complex.exp (-(spectralConstant : ℂ)*t)*(complexResiduePolynomial M).eval t*
        riemannZeta (2*t+M) := by
  have hz : 1 < (2*t+(M : ℂ)).re := by
    norm_num [Complex.add_re, Complex.mul_re]
    exact ht
  have hnext : 1 < 2*t.re+((M+1 : ℕ) : ℝ) := by push_cast; linarith
  have hsum := (spectralRemainder_summable (M+1) (by omega) t hnext).hasSum.add
    ((dirichletExponential_hasSum (2*t+M) hz).mul_left
      (Complex.exp (-(spectralConstant : ℂ)*t)*(complexResiduePolynomial M).eval t))
  have hterm : HasSum (fun n : ℕ => spectralRemainderTerm M (n+1) t)
      (spectralRemainder (M+1) t +
        Complex.exp (-(spectralConstant : ℂ)*t)*(complexResiduePolynomial M).eval t*
          riemannZeta (2*t+M)) := by
    apply hsum.congr_fun
    intro n
    rw [spectralRemainderTerm_eq (M+1) (n+1) (by omega),
      spectralRemainderTerm_eq M (n+1) (by omega), sum_range_succ]
    ring
  exact hterm.tsum_eq

theorem regularizedKernel_succ (M : ℕ) (hM : 0 < M) (t : ℂ)
    (ht : 1 < 2*t.re+(M : ℝ)) : regularizedKernel M t = regularizedKernel (M+1) t := by
  rw [regularizedKernel, spectralRemainder_succ M hM t ht, regularizedKernel, sum_range_succ]
  ring

theorem regularizedKernel_overlap (M L : ℕ) (hM : 0 < M) (hML : M ≤ L) (t : ℂ)
    (ht : 1 < 2*t.re+(M : ℝ)) : regularizedKernel M t = regularizedKernel L t := by
  induction L, hML using Nat.le_induction with
  | base => rfl
  | succ L hML ih =>
    exact ih.trans (regularizedKernel_succ L (by omega) t (by
      have hc : (M : ℝ) ≤ L := by exact_mod_cast hML
      linarith))

end CircleKernel
