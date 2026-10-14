import SphericalTreeFailures.PolynomialCharacteristic

namespace SphericalTreeFailures
open Polynomial Finset MeasureTheory
variable {V : Type*} [Fintype V]

theorem hardCore_characteristic (G : SimpleGraph V) (activity : ℝ) (ha : 0 < activity) (t : ℝ) :
    (∫ s : IndependentConfiguration G,
      Complex.exp ((s.val.card : ℂ) * ((t : ℂ) * Complex.I)) ∂(hardCore G activity ha).toMeasure) =
    polynomialCharacteristic (independencePolynomial G univ) activity t := by
  classical
  have hz := configurationPartition_pos G ha
  rw [PMF.integral_eq_sum]
  simp only [hardCore_apply]
  have hw (s : IndependentConfiguration G) :
      (ENNReal.ofReal (activity ^ s.val.card / configurationPartition G activity)).toReal =
        activity ^ s.val.card / configurationPartition G activity := ENNReal.toReal_ofReal (by positivity)
  simp_rw [hw, Complex.exp_nat_mul]
  unfold polynomialCharacteristic
  rw [← configurationPartition_polynomial]
  simp only [independencePolynomial, eval₂_finsetSum, eval₂_X_pow]
  trans ∑ s ∈ independentSetsWithin G univ,
    (activity ^ s.card / configurationPartition G activity) • Complex.exp ((t : ℂ) * Complex.I) ^ s.card
  · exact Finset.sum_coe_sort (independentSetsWithin G univ)
      (fun s : Finset V => (activity ^ s.card / configurationPartition G activity) •
        Complex.exp ((t : ℂ) * Complex.I) ^ s.card)
  rw [Finset.sum_div]
  apply sum_congr rfl
  intro s hs
  simp only [Complex.real_smul, Complex.ofReal_div, Complex.ofReal_pow, mul_pow]
  ring

end SphericalTreeFailures
