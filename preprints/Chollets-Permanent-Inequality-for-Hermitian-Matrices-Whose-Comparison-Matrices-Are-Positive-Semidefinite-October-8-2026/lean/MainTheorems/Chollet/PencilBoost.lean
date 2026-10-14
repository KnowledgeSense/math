import MainTheorems.Chollet.PencilCoefficients
import Mathlib.Algebra.MvPolynomial.PDeriv

noncomputable section

namespace ResearchMain.Chollet

open MvPolynomial

variable {K : Type*}

def polynomialBoost (p : MvPolynomial K ℂ) (k : K) : MvPolynomial K ℂ :=
  p + X k * pderiv k p

theorem polynomialBoost_monomial (d : K →₀ ℕ) (a : ℂ) (k : K) :
    polynomialBoost (monomial d a) k = monomial d ((1 + d k : ℕ) * a) := by
  rw [polynomialBoost, X_mul_pderiv_monomial, nsmul_eq_mul]
  rw [← C_mul_monomial]
  norm_num
  ring

theorem multivariate_real_eval (p : MvPolynomial K ℂ) (w : K → ℝ) :
    (eval (fun k => (w k : ℂ)) p).re =
      ∑ d ∈ p.support, (p.coeff d).re * d.prod (fun k n => w k ^ n) := by
  classical
  conv_lhs => rw [p.as_sum]
  simp only [map_sum, Complex.re_sum, eval_monomial]
  apply Finset.sum_congr rfl
  intro d _
  have he : d.prod (fun k n => (w k : ℂ) ^ n) =
      (d.prod (fun k n => w k ^ n) : ℝ) := by
    simp only [Finsupp.prod, Complex.ofReal_prod, Complex.ofReal_pow]
  rw [he]
  simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero]

theorem polynomialBoost_eval_one (p : MvPolynomial K ℂ) (k : K) :
    (eval (fun _ => (1 : ℂ)) (polynomialBoost p k)).re =
      ∑ d ∈ p.support, (1 + d k : ℕ) * (p.coeff d).re := by
  classical
  conv_lhs => rw [p.as_sum]
  simp only [polynomialBoost, map_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  rw [Complex.re_sum]
  apply Finset.sum_congr rfl
  intro d _
  change (eval (fun _ => (1 : ℂ))
    (polynomialBoost (monomial d (p.coeff d)) k)).re = _
  rw [polynomialBoost_monomial, eval_monomial]
  simp [Finsupp.prod, Complex.mul_re]

theorem polynomialBoost_bound (p : MvPolynomial K ℂ) (k : K) (w : K → ℝ)
    (hp : ∀ d, 0 ≤ (p.coeff d).re)
    (hw : ∀ d : K →₀ ℕ, (1 + d k : ℕ) ≤ d.prod (fun j n => w j ^ n)) :
    (eval (fun _ => (1 : ℂ)) (polynomialBoost p k)).re ≤
      (eval (fun j => (w j : ℂ)) p).re := by
  rw [polynomialBoost_eval_one, multivariate_real_eval p w]
  apply Finset.sum_le_sum
  intro d _
  simpa only [mul_comm] using mul_le_mul_of_nonneg_right (hw d) (hp d)

end ResearchMain.Chollet
