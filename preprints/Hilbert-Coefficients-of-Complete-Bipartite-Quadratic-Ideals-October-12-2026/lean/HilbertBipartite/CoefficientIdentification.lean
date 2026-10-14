import HilbertBipartite.HilbertSamuel
import HilbertBipartite.CorrectionIdentification
import HilbertBipartite.SignClassification

open Finset Polynomial
namespace HilbertBipartite

/-- The translated numerator coefficients equal the explicit extraction formula. -/
theorem hilbertCoefficient_eq_formula (p q i : ℕ) (hp : 1 ≤ p) (hq : 1 ≤ q) :
    hilbertCoefficient p q i = coefficientFormula p q i := by
  by_cases hi0 : i=0
  · subst i
    rw [hilbertCoefficient_zero]
    simp [coefficientFormula]
  · by_cases hin : i < p+q
    · rw [hilbertCoefficient_decomposition,
        correctionTranslated_coeff q p i hq (by omega) (by omega),
        correctionTranslated_coeff p q i hp (by omega) hin,
        coefficientFormula, ite_eq_right hi0, ite_eq_left hin,
        weightedCoeff_sub, weightedCoeff_sub]
      have hs : weightedCoeff ((X : Polynomial ℚ)^(i-1)) i (p+q-i-1) =
          (squareCoefficient (p+q) i : ℚ) := by
        unfold weightedCoeff
        simp only [coeff_X_pow, ite_mul, zero_mul]
        rw [sum_ite_eq']
        by_cases h2 : 2*i ≤ p+q
        · rw [ite_eq_left (by simp only [mem_range]; omega)]
          unfold squareCoefficient
          rw [show p+q-i-1-(i-1)=p+q-2*i by omega,
            show p+q-2*i+i=p+q-i by omega]
          push_cast
          ring
        · rw [ite_eq_right (by simp only [mem_range]; omega),
            squareCoefficient_eq_zero (p+q) i (by omega), Nat.cast_zero]
      rw [hs, Nat.add_comm q p]
      ring
    · rw [hilbertCoefficient_high p q i hp hq (by omega),
        coefficientFormula_eq_zero_of_ge p q i hp (by omega)]

end HilbertBipartite
