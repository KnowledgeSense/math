import Mathlib.Analysis.Calculus.LagrangeMultipliers
import Mathlib.Algebra.Polynomial.Derivative
import Mathlib.Tactic

namespace ResearchMain.DiagonalSchatten

open scoped Polynomial

theorem gramDual_zero_from_nonparallel (a b c u v x y : ℝ)
    (hu : u ≠ 0) (hv : v ≠ 0) (hdet : u * y - v * x ≠ 0)
    (hux : 2 * a * u + c * v = 0) (hvx : c * u + 2 * b * v = 0)
    (huy : 2 * a * x + c * y = 0) :
    a = 0 ∧ b = 0 ∧ c = 0 := by
  have hcprod : c * (u * y - v * x) = 0 := by
    linear_combination u * huy - x * hux
  have hc : c = 0 := (mul_eq_zero.mp hcprod).resolve_right hdet
  rw [hc] at hux hvx
  have ha : a = 0 := by
    have h : a * u = 0 := by nlinarith [hux]
    exact (mul_eq_zero.mp h).resolve_right hu
  have hb : b = 0 := by
    have h : b * v = 0 := by nlinarith [hvx]
    exact (mul_eq_zero.mp h).resolve_right hv
  exact ⟨ha, hb, hc⟩

theorem gramDual_zero_from_first_axis (a b c u v t : ℝ)
    (hv : v ≠ 0) (ht : t ≠ 0)
    (hux : 2 * a * u + c * v = 0) (hvx : c * u + 2 * b * v = 0)
    (haxis : 2 * a * t = 0) :
    a = 0 ∧ b = 0 ∧ c = 0 := by
  have ha : a = 0 := by
    have h : a * t = 0 := by nlinarith [haxis]
    exact (mul_eq_zero.mp h).resolve_right ht
  rw [ha] at hux
  have hc : c = 0 := by
    have h : c * v = 0 := by nlinarith [hux]
    exact (mul_eq_zero.mp h).resolve_right hv
  rw [hc] at hvx
  have hb : b = 0 := by
    have h : b * v = 0 := by nlinarith [hvx]
    exact (mul_eq_zero.mp h).resolve_right hv
  exact ⟨ha, hb, hc⟩

theorem gramDual_zero_from_second_axis (a b c u v t : ℝ)
    (hu : u ≠ 0) (ht : t ≠ 0)
    (hux : 2 * a * u + c * v = 0) (hvx : c * u + 2 * b * v = 0)
    (haxis : 2 * b * t = 0) :
    a = 0 ∧ b = 0 ∧ c = 0 := by
  have hb : b = 0 := by
    have h : b * t = 0 := by nlinarith [haxis]
    exact (mul_eq_zero.mp h).resolve_right ht
  rw [hb] at hvx
  have hc : c = 0 := by
    have h : c * u = 0 := by nlinarith [hvx]
    exact (mul_eq_zero.mp h).resolve_right hu
  rw [hc] at hux
  have ha : a = 0 := by
    have h : a * u = 0 := by nlinarith [hux]
    exact (mul_eq_zero.mp h).resolve_right hu
  exact ⟨ha, hb, hc⟩

theorem polynomial_contact_of_value_derivative (P D Q : ℝ[X]) (r : ℝ)
    (hv : P.eval r = Q.eval r * D.eval r)
    (hd : P.derivative.eval r = Q.derivative.eval r * D.eval r +
      Q.eval r * D.derivative.eval r) :
    (Q * D - P).eval r = 0 ∧ (Q * D - P).derivative.eval r = 0 := by
  constructor
  · simp only [Polynomial.eval_sub, Polynomial.eval_mul]
    linarith
  · simp only [Polynomial.derivative_sub, Polynomial.derivative_mul,
      Polynomial.eval_sub, Polynomial.eval_add, Polynomial.eval_mul]
    linarith

end ResearchMain.DiagonalSchatten
