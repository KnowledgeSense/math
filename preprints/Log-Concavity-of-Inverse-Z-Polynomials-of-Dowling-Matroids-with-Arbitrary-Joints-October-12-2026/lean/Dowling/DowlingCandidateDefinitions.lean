import Mathlib.RingTheory.PowerSeries.Log
import Mathlib.Algebra.Polynomial.Degree.Operations
import Mathlib.Tactic

noncomputable section
namespace Dowling
open PowerSeries

/-- The inverse-logarithm coordinate, with division by the polynomial parameter
removed coefficientwise. Its linear coefficient is one. -/
def dowlingLogCoordinate : PowerSeries (Polynomial ℝ) :=
  mk fun n => if n = 0 then 0 else
    Polynomial.C ((-1 : ℝ) ^ (n+1) / n) * (Polynomial.X ^ (n-1) + 1) -
      if n = 1 then 1 else 0

@[simp] theorem dowlingLogCoordinate_constantCoeff :
    dowlingLogCoordinate.constantCoeff = 0 := by
  simp [dowlingLogCoordinate, ← coeff_zero_eq_constantCoeff_apply]

@[simp] theorem dowlingLogCoordinate_coeff_one :
    dowlingLogCoordinate.coeff 1 = 1 := by
  norm_num [dowlingLogCoordinate]

/-- The unique compositional inverse of the actual logarithmic coordinate. -/
def dowlingLogInverse : PowerSeries (Polynomial ℝ) :=
  dowlingLogCoordinate.substInvOfIsUnit (by simp)

@[simp] theorem dowlingLogInverse_constantCoeff :
    dowlingLogInverse.constantCoeff = 0 := by simp [dowlingLogInverse]

@[simp] theorem dowlingLogInverse_coeff_one :
    dowlingLogInverse.coeff 1 = 1 := by
  simp [dowlingLogInverse, coeff_one_substInvOfIsUnit]

theorem dowlingLogCoordinate_subst_inverse :
    dowlingLogCoordinate.subst dowlingLogInverse = X :=
  subst_substInvOfIsUnit_right _ dowlingLogCoordinate_constantCoeff _

theorem dowlingLogInverse_subst_coordinate :
    dowlingLogInverse.subst dowlingLogCoordinate = X :=
  subst_substInvOfIsUnit_left _ dowlingLogCoordinate_constantCoeff _

/-- The primitive with zero constant coefficient, over real polynomial coefficients. -/
def candidatePrimitive (f : PowerSeries (Polynomial ℝ)) : PowerSeries (Polynomial ℝ) :=
  mk fun n => Polynomial.C ((n : ℝ)⁻¹) * coeff (n-1) f

@[simp] theorem candidatePrimitive_constantCoeff (f : PowerSeries (Polynomial ℝ)) :
    (candidatePrimitive f).constantCoeff = 0 := by
  rw [← coeff_zero_eq_constantCoeff_apply]
  simp only [candidatePrimitive, coeff_mk, Nat.cast_zero, inv_zero, Polynomial.C_0, zero_mul]

theorem derivative_candidatePrimitive (f : PowerSeries (Polynomial ℝ)) :
    derivative (candidatePrimitive f) = f := by
  apply PowerSeries.ext
  intro n
  simp only [coeff_derivative, candidatePrimitive, coeff_mk, Nat.add_sub_cancel]
  have h : Polynomial.C (((n+1 : ℕ) : ℝ)⁻¹) * (n+1 : Polynomial ℝ) = 1 := by
    have hc : (n+1 : Polynomial ℝ) = Polynomial.C ((n+1 : ℕ) : ℝ) := by simp
    rw [hc, ← map_mul, inv_mul_cancel₀ (by positivity), map_one]
  calc
    _ = (Polynomial.C (((n+1 : ℕ) : ℝ)⁻¹) * (n+1 : Polynomial ℝ)) * coeff n f := by ring
    _ = coeff n f := by rw [h, one_mul]

/-- The braid logarithmic Z-series in the source normalization. -/
def braidLogZCandidate : PowerSeries (Polynomial ℝ) :=
  X * C (1 + Polynomial.X) + C Polynomial.X * candidatePrimitive dowlingLogInverse

/-- The full Dowling Z candidate; `m` is the cardinality of the gain group. -/
def dowlingZCandidate (m : ℝ) : PowerSeries (Polynomial ℝ) :=
  (exp (Polynomial ℝ)).subst
    (C (Polynomial.C m⁻¹) * braidLogZCandidate.subst (C (Polynomial.C m) * X))

@[simp] theorem braidLogZCandidate_constantCoeff :
    braidLogZCandidate.constantCoeff = 0 := by simp [braidLogZCandidate]

@[simp] theorem dowlingZCandidate_constantCoeff (m : ℝ) :
    (dowlingZCandidate m).constantCoeff = 1 := by
  change MvPowerSeries.constantCoeff _ = 1
  rw [dowlingZCandidate, constantCoeff_subst_of_constantCoeff_zero]
  · exact constantCoeff_exp
  · rw [map_mul]
    have hz : (C (Polynomial.C m) * (X : PowerSeries (Polynomial ℝ))).constantCoeff = 0 := by simp
    rw [constantCoeff_subst_of_constantCoeff_zero hz]
    change _ * braidLogZCandidate.constantCoeff = 0
    rw [braidLogZCandidate_constantCoeff, mul_zero]

end Dowling
