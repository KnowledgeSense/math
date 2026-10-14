import MainTheorems.DiagonalSchatten.RayFunctional
import MainTheorems.DiagonalSchatten.GramStationarity
import Mathlib.Analysis.Calculus.Deriv.Polynomial
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Tactic.ComputeDegree

namespace ResearchMain.DiagonalSchatten

noncomputable section

open Polynomial
open scoped Polynomial

def rayQuadraticPolynomial (q : Fin 3 → ℝ) : ℝ[X] :=
  C (q 0) + C (q 2) * X + C (q 1) * X ^ 2

theorem rayQuadraticPolynomial_eval (q : Fin 3 → ℝ) (r : ℝ) :
    (rayQuadraticPolynomial q).eval r = q 0 + q 2 * r + q 1 * r ^ 2 := by
  simp [rayQuadraticPolynomial]

theorem rayQuadraticPolynomial_derivative_eval (q : Fin 3 → ℝ) (r : ℝ) :
    (rayQuadraticPolynomial q).derivative.eval r = 2 * q 1 * r + q 2 := by
  simp [rayQuadraticPolynomial, Polynomial.derivative_pow]
  ring

namespace RayParameters

variable (g : RayParameters)

def denominatorPolynomial : ℝ[X] :=
  C g.k * (C ((g.k + 1) * g.a * g.c) +
    C (g.k * g.a * g.b + (g.k + 2) * g.c ^ 2) * X + C ((g.k + 1) * g.b * g.c) * X ^ 2)

def numeratorPolynomial : ℝ[X] :=
  (C (g.k * g.b) * X + C ((g.k + 1) * g.c)) * (C g.z1 + C g.z12 * X) ^ 2 +
    C (2 * g.c) * X * (C g.z1 + C g.z12 * X) * (C g.z12 + C g.z2 * X) +
    (C (g.k * g.a) * X + C ((g.k + 1) * g.c) * X ^ 2) * (C g.z12 + C g.z2 * X) ^ 2

def contactPolynomial (s : ℝ) (q : Fin 3 → ℝ) : ℝ[X] :=
  rayQuadraticPolynomial q * g.denominatorPolynomial - C s * g.numeratorPolynomial

theorem denominatorPolynomial_eval (r : ℝ) :
    g.denominatorPolynomial.eval r = g.denominator ![1, r] := by
  simp only [denominatorPolynomial, eval_mul, eval_add, eval_C, eval_X, eval_pow,
    denominator, Matrix.cons_val_zero, Matrix.cons_val_one]
  ring

theorem numeratorPolynomial_eval (r : ℝ) :
    g.numeratorPolynomial.eval r = g.numerator ![1, r] := by
  simp only [numeratorPolynomial, eval_mul, eval_add, eval_C, eval_X, eval_pow,
    numerator, image, Matrix.cons_val_zero, Matrix.cons_val_one]
  ring

theorem functional_polynomial_quotient (s r : ℝ) :
    s * g.functional ![1, r] = (C s * g.numeratorPolynomial).eval r /
      g.denominatorPolynomial.eval r := by
  rw [eval_mul, eval_C, g.numeratorPolynomial_eval, g.denominatorPolynomial_eval, functional]
  ring

theorem contactPolynomial_degree (s : ℝ) (q : Fin 3 → ℝ) :
    (g.contactPolynomial s q).natDegree ≤ 4 := by
  unfold contactPolynomial rayQuadraticPolynomial denominatorPolynomial numeratorPolynomial
  compute_degree!

theorem contactPolynomial_eval_zero (s : ℝ) (q : Fin 3 → ℝ) :
    (g.contactPolynomial s q).eval 0 =
      (g.k + 1) * g.c * (g.k * g.a * q 0 - s * g.z1 ^ 2) := by
  simp [contactPolynomial, rayQuadraticPolynomial, denominatorPolynomial, numeratorPolynomial]
  ring

theorem numeratorPolynomial_coeff_four :
    g.numeratorPolynomial.coeff 4 = (g.k + 1) * g.c * g.z2 ^ 2 := by
  let U : ℝ[X] := (C (g.k * g.b) * X + C ((g.k + 1) * g.c)) *
    (C g.z1 + C g.z12 * X) ^ 2
  let V : ℝ[X] := C (2 * g.c) * X * (C g.z1 + C g.z12 * X) *
    (C g.z12 + C g.z2 * X)
  let A : ℝ[X] := C (g.k * g.a) * X + C ((g.k + 1) * g.c) * X ^ 2
  let B : ℝ[X] := C g.z12 + C g.z2 * X
  have hU : U.natDegree ≤ 3 := by dsimp [U]; compute_degree!
  have hV : V.natDegree ≤ 3 := by dsimp [V]; compute_degree!
  have hA : A.natDegree ≤ 2 := by dsimp [A]; compute_degree!
  have hB : B.natDegree ≤ 1 := by dsimp [B]; compute_degree!
  have hB2 : (B ^ 2).natDegree ≤ 2 := by dsimp [B]; compute_degree!
  have hBcoeff : (B ^ 2).coeff 2 = B.coeff 1 ^ 2 := by
    simpa using (coeff_pow_of_natDegree_le (m := 2) hB)
  change (U + V + A * B ^ 2).coeff 4 = _
  rw [coeff_add, coeff_add, coeff_eq_zero_of_natDegree_lt (by omega : U.natDegree < 4),
    coeff_eq_zero_of_natDegree_lt (by omega : V.natDegree < 4), zero_add, zero_add]
  rw [show 4 = 2 + 2 by rfl, coeff_mul_add_eq_of_natDegree_le hA hB2, hBcoeff]
  simp [A, B, coeff_mul_X_pow', coeff_mul_X]

theorem contactPolynomial_coeff_four (s : ℝ) (q : Fin 3 → ℝ) :
    (g.contactPolynomial s q).coeff 4 =
      (g.k + 1) * g.c * (g.k * g.b * q 1 - s * g.z2 ^ 2) := by
  have hQ : (rayQuadraticPolynomial q).natDegree ≤ 2 := by
    unfold rayQuadraticPolynomial
    compute_degree!
  have hD : g.denominatorPolynomial.natDegree ≤ 2 := by
    unfold denominatorPolynomial
    compute_degree!
  rw [contactPolynomial, coeff_sub, coeff_C_mul, show 4 = 2 + 2 by rfl,
    coeff_mul_add_eq_of_natDegree_le hQ hD, g.numeratorPolynomial_coeff_four]
  simp only [rayQuadraticPolynomial, denominatorPolynomial, coeff_add, coeff_C_mul,
    coeff_mul_X_pow', coeff_mul_X, coeff_C]
  norm_num
  ring

theorem contactPolynomial_degree_lt_four (s : ℝ) (q : Fin 3 → ℝ)
    (h : g.k * g.b * q 1 - s * g.z2 ^ 2 = 0) :
    (g.contactPolynomial s q).natDegree < 4 := by
  have hcoeff : (g.contactPolynomial s q).coeff 4 = 0 := by
    rw [g.contactPolynomial_coeff_four, h, mul_zero]
  have hdeg := Polynomial.natDegree_le_pred (g.contactPolynomial_degree s q) hcoeff
  omega

theorem contactPolynomial_of_quotient_match (s : ℝ) (q : Fin 3 → ℝ) (r : ℝ)
    (hD : g.denominator ![1, r] ≠ 0)
    (hv : s * g.functional ![1, r] = (rayQuadraticPolynomial q).eval r)
    (hd : HasDerivAt (fun x => s * g.functional ![1, x])
      ((rayQuadraticPolynomial q).derivative.eval r) r) :
    (g.contactPolynomial s q).eval r = 0 ∧ (g.contactPolynomial s q).derivative.eval r = 0 := by
  let P := C s * g.numeratorPolynomial
  let D := g.denominatorPolynomial
  let Q := rayQuadraticPolynomial q
  have hDn : D.eval r ≠ 0 := by simpa only [D, g.denominatorPolynomial_eval] using hD
  have hvalue : P.eval r = Q.eval r * D.eval r := by
    rw [g.functional_polynomial_quotient] at hv
    exact (div_eq_iff hDn).mp hv
  have hquot : HasDerivAt (fun x => P.eval x / D.eval x)
      ((P.derivative.eval r * D.eval r - P.eval r * D.derivative.eval r) / D.eval r ^ 2) r := by
    convert! (P.hasDerivAt r).div (D.hasDerivAt r) hDn using 1
  have hfunc : (fun x => s * g.functional ![1, x]) = (fun x => P.eval x / D.eval x) :=
    funext (g.functional_polynomial_quotient s)
  rw [hfunc] at hd
  have he := hquot.unique hd
  have he' : P.derivative.eval r * D.eval r - P.eval r * D.derivative.eval r =
      Q.derivative.eval r * D.eval r ^ 2 := (div_eq_iff (pow_ne_zero 2 hDn)).mp he
  have hmul : (P.derivative.eval r - Q.derivative.eval r * D.eval r -
      Q.eval r * D.derivative.eval r) * D.eval r = 0 := by
    linear_combination he' + D.derivative.eval r * hvalue
  have hder : P.derivative.eval r = Q.derivative.eval r * D.eval r +
      Q.eval r * D.derivative.eval r := by
    have hz := (mul_eq_zero.mp hmul).resolve_right hDn
    linarith
  exact polynomial_contact_of_value_derivative P D Q r hvalue hder

end RayParameters

end

end ResearchMain.DiagonalSchatten
