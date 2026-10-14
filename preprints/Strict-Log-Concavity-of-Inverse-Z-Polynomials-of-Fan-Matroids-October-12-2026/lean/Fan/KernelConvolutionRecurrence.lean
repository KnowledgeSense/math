import Fan.DelannoyKernel
import Mathlib.RingTheory.PowerSeries.Basic

noncomputable section
open scoped BigOperators
namespace Fan

theorem delannoyPolynomial_cross (a b : ℕ) :
    delannoyPolynomial (a+1) (b+1) = delannoyPolynomial (a+1) b +
      delannoyPolynomial a (b+1) + (Polynomial.X-1)*delannoyPolynomial a b := by
  ext k
  cases k with
  | zero => simp [sub_mul,Polynomial.coeff_add,Polynomial.coeff_sub]
  | succ k =>
    simp only [Polynomial.coeff_add,sub_mul,Polynomial.coeff_sub,
      Polynomial.coeff_X_mul,one_mul,delannoyPolynomial_coeff,
      Nat.choose_succ_succ,Nat.cast_add]
    ring

theorem delannoy_cross (z : ℝ) (a b : ℕ) :
    delannoy z (a+1) (b+1) = delannoy z (a+1) b +
      delannoy z a (b+1) + (z-1)*delannoy z a b := by
  have h := congrArg (Polynomial.eval z) (delannoyPolynomial_cross a b)
  simpa only [Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_sub,
    Polynomial.eval_X,Polynomial.eval_one,delannoyPolynomial_eval] using h

def imbalanceSeries (z : ℝ) (e : ℕ) : PowerSeries ℝ :=
  PowerSeries.mk fun m => delannoy z m (m+e)

@[simp] theorem imbalanceSeries_coeff (z : ℝ) (e m : ℕ) :
    PowerSeries.coeff m (imbalanceSeries z e) = delannoy z m (m+e) := by simp [imbalanceSeries]

@[simp] theorem imbalanceSeries_zero_coeff (z : ℝ) (e : ℕ) :
    PowerSeries.coeff 0 (imbalanceSeries z e) = 1 := by simp

theorem imbalanceSeries_recurrence (z : ℝ) (e : ℕ) :
    imbalanceSeries z (e+1) = imbalanceSeries z e + PowerSeries.X*imbalanceSeries z (e+2) +
      PowerSeries.C (z-1)*PowerSeries.X*imbalanceSeries z (e+1) := by
  ext m
  cases m with
  | zero => simp [imbalanceSeries]
  | succ m =>
    rw [mul_assoc]
    simp only [map_add,PowerSeries.coeff_succ_X_mul,PowerSeries.coeff_C_mul,
      imbalanceSeries_coeff]
    simpa only [Nat.add_assoc,Nat.succ_eq_add_one,Nat.add_comm,Nat.add_left_comm] using
      delannoy_cross z m (m+e+1)

end Fan
