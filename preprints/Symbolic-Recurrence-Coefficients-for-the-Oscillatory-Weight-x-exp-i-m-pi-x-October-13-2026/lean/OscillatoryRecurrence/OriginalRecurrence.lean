import OscillatoryRecurrence.RealCoefficients

noncomputable section
open Polynomial
namespace OscillatoryRecurrence

/-- The original recurrence, with its real coefficients and original degree index. -/
theorem original_three_term_recurrence (m : ℤ) (hm : m≠0) (n : ℕ) (hn : 1≤n) :
    X*orthogonalPolynomial ((m:ℝ)*Real.pi) n =
      orthogonalPolynomial ((m:ℝ)*Real.pi) (n+1)+
      C (Complex.I*(alpha ((m:ℝ)*Real.pi) n:ℂ))*orthogonalPolynomial ((m:ℝ)*Real.pi) n+
      C (beta ((m:ℝ)*Real.pi) n:ℂ)*orthogonalPolynomial ((m:ℝ)*Real.pi) (n-1) := by
  have h := three_term_recurrence m hm (n-1)
  rw [recurrenceDiagonal_alpha m hm,recurrenceLower_beta m hm,
    show n-1+1=n by omega,show n-1+2=n+1 by omega] at h
  exact h

theorem realFamily_denominator_ne_zero (m : ℤ) (hm : m≠0) {n : ℕ} (hn : 1≤n) :
    realFamily ((m:ℝ)*Real.pi) (hankelDegree n)≠0 := by
  intro h
  have hc := evaluatedFamily_hankel_ne_zero m hm hn
  rw [← realFamily_cast,h,Complex.ofReal_zero] at hc
  exact hc rfl

theorem realFamily_even_denominator_ne_zero (m : ℤ) (hm : m≠0) (k : ℕ) (hk : 1≤k) :
    realFamily ((m:ℝ)*Real.pi) (k^2)≠0 := by
  simpa only [hankelDegree_even] using
    realFamily_denominator_ne_zero m hm (by omega : 1≤2*k)

theorem realFamily_odd_denominator_ne_zero (m : ℤ) (hm : m≠0) (k : ℕ) :
    realFamily ((m:ℝ)*Real.pi) (k*(k+1))≠0 := by
  simpa only [hankelDegree_odd] using
    realFamily_denominator_ne_zero m hm (by omega : 1≤2*k+1)

end OscillatoryRecurrence
