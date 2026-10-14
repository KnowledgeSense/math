import MainTheorems.EulerianPencil.EndpointValues
import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas

namespace ResearchMain.EulerianPencil

open Polynomial
open scoped Topology

noncomputable def tangentOperator (f : ℝ[X]) : ℝ[X] := (1 + X ^ 2) * derivative f

noncomputable def tangentPolynomial : ℕ → ℝ[X]
  | 0 => X
  | n + 1 => tangentOperator (tangentPolynomial n)

noncomputable def tangentSubstitution : ℝ[X] := C (-(1 / 4 : ℝ)) * (1 + X ^ 2)

theorem tangentOperator_C_mul (a : ℝ) (f : ℝ[X]) :
    tangentOperator (C a * f) = C a * tangentOperator f := by
  simp [tangentOperator, derivative_mul]
  ring

theorem tangentOperator_odd (f : ℝ[X]) :
    tangentOperator ((1 + X ^ 2) * f.comp tangentSubstitution) =
      C 2 * X * (1 + X ^ 2) * (U f).comp tangentSubstitution := by
  simp only [tangentOperator, derivative_mul, derivative_add, derivative_one,
    derivative_pow, derivative_X, mul_one, zero_add, derivative_comp, U, add_comp,
    mul_comp, X_comp, tangentSubstitution, derivative_C, zero_mul]
  norm_num
  ring

theorem tangentOperator_even (f : ℝ[X]) :
    tangentOperator (C 2 * X * (1 + X ^ 2) * f.comp tangentSubstitution) =
      C (-4) * (1 + X ^ 2) * (T f).comp tangentSubstitution := by
  simp only [tangentOperator, derivative_mul, derivative_add, derivative_one,
    derivative_pow, derivative_X, mul_one, zero_add, derivative_comp, T, add_comp,
    mul_comp, X_comp, tangentSubstitution, derivative_C, zero_mul, C_comp, one_comp]
  norm_num
  norm_num [show C (2 : ℝ) = (2 : ℝ[X]) from map_ofNat C 2,
    show C (4 : ℝ) = (4 : ℝ[X]) from map_ofNat C 4,
    show C (6 : ℝ) = (6 : ℝ[X]) from map_ofNat C 6]
  have hq : C (1 / 4 : ℝ) * (4 : ℝ[X]) = 1 := by
    rw [← C_ofNat, ← map_mul]
    norm_num
  linear_combination
    (-6 * (1 + X ^ 2) ^ 2 * f.comp (-(C (1 / 4) * (1 + X ^ 2))) +
      4 * C (1 / 4) * (1 + X ^ 2) ^ 3 *
        (derivative f).comp (-(C (1 / 4) * (1 + X ^ 2)))) * hq

theorem tangentPolynomial_form (m : ℕ) :
    tangentPolynomial (2 * m + 1) =
      C ((-4 : ℝ) ^ m) * ((1 + X ^ 2) * (oddF m).comp tangentSubstitution) ∧
    tangentPolynomial (2 * m + 2) =
      C ((-4 : ℝ) ^ m) * (C 2 * X * (1 + X ^ 2) * (evenF m).comp tangentSubstitution) := by
  induction m with
  | zero =>
    constructor
    · norm_num [tangentPolynomial, tangentOperator, oddF, evenF, U]
    · norm_num [tangentPolynomial, tangentOperator, oddF, evenF, U]; ring
  | succ m ih =>
    have ho : tangentPolynomial (2 * (m + 1) + 1) =
        C ((-4 : ℝ) ^ (m + 1)) *
          ((1 + X ^ 2) * (oddF (m + 1)).comp tangentSubstitution) := by
      rw [show 2 * (m + 1) + 1 = (2 * m + 2) + 1 by omega,
        tangentPolynomial, ih.2, tangentOperator_C_mul, tangentOperator_even, oddF,
        ← evenF]
      simp only [pow_succ, map_mul]
      ring
    refine ⟨ho, ?_⟩
    rw [show 2 * (m + 1) + 2 = (2 * (m + 1) + 1) + 1 by omega,
      tangentPolynomial, ho, tangentOperator_C_mul, tangentOperator_odd]
    rfl

theorem tangent_hasDerivAt {x : ℝ} (hx : Real.cos x ≠ 0) :
    HasDerivAt Real.tan (1 + Real.tan x ^ 2) x := by
  convert Real.hasDerivAt_tan hx using 1
  rw [Real.tan_eq_sin_div_cos]
  field_simp
  nlinarith [Real.sin_sq_add_cos_sq x]

theorem tangent_iteratedDeriv (n : ℕ) {x : ℝ} (hx : Real.cos x ≠ 0) :
    iteratedDeriv n Real.tan x = (tangentPolynomial n).eval (Real.tan x) := by
  induction n generalizing x with
  | zero => simp [tangentPolynomial]
  | succ n ih =>
    have he : iteratedDeriv n Real.tan =ᶠ[𝓝 x]
        (fun y => (tangentPolynomial n).eval (Real.tan y)) := by
      filter_upwards [Real.continuous_cos.continuousAt.eventually_ne hx] with y hy
      exact ih hy
    rw [iteratedDeriv_succ, he.deriv_eq]
    have hd := ((tangentPolynomial n).hasDerivAt (Real.tan x)).comp x
      (tangent_hasDerivAt hx)
    change HasDerivAt (fun y => (tangentPolynomial n).eval (Real.tan y)) _ x at hd
    rw [hd.deriv]
    simp [tangentPolynomial, tangentOperator, mul_comm]

theorem tangentPolynomial_odd_zero (m : ℕ) :
    (tangentPolynomial (2 * m + 1)).eval 0 = (oddH m).eval (-2) := by
  rw [(tangentPolynomial_form m).1]
  simp only [eval_mul, eval_C, eval_add, eval_one, eval_pow, eval_X,
    eval_comp, tangentSubstitution]
  rw [oddH, reduction_eval (oddF_degree_le m) (by norm_num)]
  norm_num

theorem oddH_eq_tangent_derivative (m : ℕ) :
    (oddH m).eval (-2) = iteratedDeriv (2 * m + 1) Real.tan 0 := by
  rw [tangent_iteratedDeriv _ (by simp), Real.tan_zero, tangentPolynomial_odd_zero]

end ResearchMain.EulerianPencil
