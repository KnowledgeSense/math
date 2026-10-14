import OscillatoryRecurrence.NormalizedFamily
import OscillatoryRecurrence.HankelLeadingRatios
import OscillatoryRecurrence.CoefficientDeterminants

noncomputable section
open Polynomial
namespace OscillatoryRecurrence

/-- Evaluation of the common rational polynomial family at the squared frequency. -/
def evaluatedFamily (η : ℝ) (j : ℕ) : ℂ :=
  (recurrenceFamily j).eval₂ (Rat.castHom ℂ) ((η:ℂ)^2)

theorem evaluatedHankel_as_family (η : ℝ) {n : ℕ} (hn : 1 ≤ n) :
    evaluatedHankel η n = ((polynomialHankel n).leadingCoeff : ℂ) *
      evaluatedFamily η (hankelDegree n) := by
  have h := congrArg (fun p : ℚ[X] => p.eval₂ (Rat.castHom ℂ) ((η:ℂ)^2))
    (recurrenceFamily_hankel_identity hn)
  simpa only [evaluatedHankel, evaluatedFamily, eval₂_mul, eval₂_C, Rat.coe_castHom] using h.symm

theorem evaluatedFamily_hankel_ne_zero (m : ℤ) (hm : m ≠ 0) {n : ℕ} (hn : 1 ≤ n) :
    evaluatedFamily ((m:ℝ)*Real.pi) (hankelDegree n) ≠ 0 := by
  have h := evaluatedHankel_ne_zero m hm n
  rw [evaluatedHankel_as_family _ hn] at h
  exact (mul_ne_zero_iff.mp h).2

private theorem normalized_quotient (a b c x y z w : ℂ) (hc : c ≠ 0) :
    -(a*x)*(b*y)/(z*(c*w)^2) = -(a*b/c^2)*(x*y/(z*w^2)) := by
  by_cases hz : z=0
  · simp [hz]
  by_cases hw : w=0
  · simp [hw]
  field_simp

/-- The odd lower recurrence coefficient, for every nonzero integral frequency. -/
theorem recurrenceLower_odd_family (m : ℤ) (hm : m ≠ 0) (k : ℕ) (hk : 1 ≤ k) :
    recurrenceLower ((m:ℝ)*Real.pi) (2*k) =
      evaluatedFamily ((m:ℝ)*Real.pi) (k^2) *
        evaluatedFamily ((m:ℝ)*Real.pi) ((k+1)^2) /
      (((((m:ℝ)*Real.pi):ℂ)^2) *
        evaluatedFamily ((m:ℝ)*Real.pi) (k*(k+1))^2) := by
  rw [recurrenceLower_polynomials m hm]
  rw [evaluatedHankel_as_family _ (by omega : 1 ≤ 2*k+2),
    evaluatedHankel_as_family _ (by omega : 1 ≤ 2*k),
    evaluatedHankel_as_family _ (by omega : 1 ≤ 2*k+1)]
  have hc : ((polynomialHankel (2*k+1)).leadingCoeff : ℂ) ≠ 0 := by
    exact_mod_cast (leadingCoeff_ne_zero.mpr (polynomialHankel_ne_zero (2*k+1)))
  rw [normalized_quotient _ _ _ _ _ _ _ hc]
  have hh : ((polynomialHankel (2*k+2)).leadingCoeff : ℂ) *
      ((polynomialHankel (2*k)).leadingCoeff : ℂ) =
      -((polynomialHankel (2*k+1)).leadingCoeff : ℂ)^2 := by
    exact_mod_cast polynomialHankel_leading_odd_recurrence k
  rw [hh, neg_div, div_self (pow_ne_zero 2 hc), neg_neg, one_mul,
    show 2*k+2=2*(k+1) by omega, hankelDegree_even, hankelDegree_even, hankelDegree_odd]
  ring

/-- The even lower recurrence coefficient, with its original negative square factor. -/
theorem recurrenceLower_even_family (m : ℤ) (hm : m ≠ 0) (k : ℕ) :
    recurrenceLower ((m:ℝ)*Real.pi) (2*k+1) =
      -(2*(k+1):ℂ)^2 * evaluatedFamily ((m:ℝ)*Real.pi) (k*(k+1)) *
        evaluatedFamily ((m:ℝ)*Real.pi) ((k+1)*(k+2)) /
      (((((m:ℝ)*Real.pi):ℂ)^2) *
        evaluatedFamily ((m:ℝ)*Real.pi) ((k+1)^2)^2) := by
  rw [recurrenceLower_polynomials m hm]
  rw [evaluatedHankel_as_family _ (by omega : 1 ≤ 2*k+1+2),
    evaluatedHankel_as_family _ (by omega : 1 ≤ 2*k+1),
    evaluatedHankel_as_family _ (by omega : 1 ≤ 2*k+1+1)]
  have hc : ((polynomialHankel (2*k+1+1)).leadingCoeff : ℂ) ≠ 0 := by
    exact_mod_cast (leadingCoeff_ne_zero.mpr (polynomialHankel_ne_zero (2*k+1+1)))
  rw [normalized_quotient _ _ _ _ _ _ _ hc]
  have hh : ((polynomialHankel (2*k+1+2)).leadingCoeff : ℂ) *
      ((polynomialHankel (2*k+1)).leadingCoeff : ℂ) =
      (2*(k+1):ℂ)^2 * ((polynomialHankel (2*k+1+1)).leadingCoeff : ℂ)^2 := by
    exact_mod_cast polynomialHankel_leading_even_recurrence k
  rw [hh, mul_div_cancel_right₀ _ (pow_ne_zero 2 hc),
    show 2*k+1+2=2*(k+1)+1 by omega, show 2*k+1+1=2*(k+1) by omega,
    hankelDegree_odd, hankelDegree_odd, hankelDegree_even]
  ring

end OscillatoryRecurrence
