import Mathlib.NumberTheory.Bernoulli
import Mathlib.RingTheory.PowerSeries.Exp
import Mathlib.RingTheory.PowerSeries.Substitution

noncomputable section
open PowerSeries
namespace CircleResidues

/-- The rational sequence in the circle logarithmic-Laplacian residue formula. -/
def sourceCoefficient (k : ℕ) : ℚ :=
  (1 - (2 : ℚ) ^ (1 - (k : ℤ))) * 2 * bernoulli k / k

/-- The ordinary Bell normalization: the generating series is `exp(-t ∑ sₖ Xᵏ)`. -/
def residuePolynomial (t : ℚ) (j : ℕ) : ℚ :=
  coeff j ((exp ℚ).subst (mk fun k => -t * sourceCoefficient k))

/-- The even-degree exponent after the change of variable `x = z²`. -/
def evenExponent (a : ℚ) : PowerSeries ℚ :=
  mk fun r => a * (1 - (2 : ℚ) ^ (1 - 2 * (r : ℤ))) * bernoulli (2 * r) / r

/-- Coefficients of the reduced exponential series. -/
def evenResidue (a : ℚ) (n : ℕ) : ℚ :=
  coeff n ((exp ℚ).subst (evenExponent a))

@[simp] theorem sourceCoefficient_zero : sourceCoefficient 0 = 0 := by
  simp [sourceCoefficient]

@[simp] theorem evenExponent_constant (a : ℚ) : constantCoeff (evenExponent a) = 0 := by
  simp [evenExponent, constantCoeff_mk]

theorem evenExponent_hasSubst (a : ℚ) : HasSubst (evenExponent a) :=
  HasSubst.of_constantCoeff_zero' (evenExponent_constant a)

@[simp] theorem evenResidue_zero (a : ℚ) : evenResidue a 0 = 1 := by
  rw [evenResidue, coeff_subst' (evenExponent_hasSubst a)]
  rw [finsum_eq_single _ 0]
  · simp
  · intro n hn
    simp [coeff_zero_eq_constantCoeff, hn]

end CircleResidues
