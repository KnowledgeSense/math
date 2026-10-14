import CircleResidues.BellNormalization
import Mathlib.RingTheory.PowerSeries.Trunc
import Mathlib.Analysis.Complex.Polynomial.Basic

noncomputable section
open Finset
namespace CircleKernel

def complexResiduePolynomial (j : ℕ) : Polynomial ℂ :=
  ∑ ell ∈ range (j+1), Polynomial.C ((CircleResidues.ordinaryBell j ell : ℂ)/(ell.factorial : ℂ)) *
    (-Polynomial.X)^ell

def exponentPolynomial (M : ℕ) : Polynomial ℚ :=
  (PowerSeries.mk CircleResidues.sourceCoefficient).trunc (M+1)

def exponentialTaylorPolynomial (M : ℕ) (t : ℂ) : Polynomial ℂ :=
  ∑ ell ∈ range M, Polynomial.C ((-t)^ell/(ell.factorial : ℂ)) *
    ((exponentPolynomial M).map (Rat.castHom ℂ))^ell

theorem complexResiduePolynomial_eval (j : ℕ) (t : ℂ) :
    (complexResiduePolynomial j).eval t = ∑ ell ∈ range (j+1),
      (-t)^ell/(ell.factorial : ℂ)*(CircleResidues.ordinaryBell j ell : ℂ) := by
  simp only [complexResiduePolynomial, Polynomial.eval_finsetSum, Polynomial.eval_mul,
    Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_neg, Polynomial.eval_X]
  apply sum_congr rfl
  intro ell hell
  ring

theorem complexResiduePolynomial_rat (j : ℕ) (t : ℚ) :
    (complexResiduePolynomial j).eval (t : ℂ) = (CircleResidues.residuePolynomial t j : ℂ) := by
  rw [complexResiduePolynomial_eval, CircleResidues.residuePolynomial_eq_bell_sum]
  push_cast
  rfl

theorem exponentPolynomial_pow_coeff (M j ell : ℕ) (hj : j ≤ M) :
    ((exponentPolynomial M)^ell).coeff j = CircleResidues.ordinaryBell j ell := by
  have h := congrArg (fun p : Polynomial ℚ => p.coeff j)
    (PowerSeries.trunc_trunc_pow (PowerSeries.mk CircleResidues.sourceCoefficient) (M+1) ell)
  simpa only [PowerSeries.coeff_trunc, show j < M+1 by omega, ite_true,
    ← Polynomial.coe_pow, Polynomial.coeff_coe, exponentPolynomial, CircleResidues.ordinaryBell] using h

theorem ordinaryBell_above (j ell : ℕ) (h : j < ell) : CircleResidues.ordinaryBell j ell = 0 := by
  apply PowerSeries.X_pow_dvd_iff.mp _ j h
  apply pow_dvd_pow_of_dvd
  apply PowerSeries.X_dvd_iff.mpr
  simp [PowerSeries.constantCoeff_mk]

theorem exponentialTaylorPolynomial_coeff (M j : ℕ) (hj : j < M) (t : ℂ) :
    (exponentialTaylorPolynomial M t).coeff j = (complexResiduePolynomial j).eval t := by
  rw [exponentialTaylorPolynomial, Polynomial.finsetSum_coeff, complexResiduePolynomial_eval]
  simp only [Polynomial.coeff_C_mul, ← Polynomial.map_pow, Polynomial.coeff_map,
    exponentPolynomial_pow_coeff M j _ (le_of_lt hj), Rat.coe_castHom]
  symm
  apply sum_subset (range_mono (by omega))
  intro ell hell hout
  have hout' : ¬ ell < j+1 := by simpa only [mem_range] using hout
  have hjl : j < ell := by omega
  rw [ordinaryBell_above j ell hjl, Rat.cast_zero, mul_zero]

end CircleKernel
