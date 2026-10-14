import MainTheorems.EulerianPencil.Degree
import MainTheorems.EulerianPencil.Operators
import Mathlib.Algebra.Polynomial.Homogenize

namespace ResearchMain.EulerianPencil

open Polynomial

noncomputable def E (n : ℕ) (f : ℝ[X]) : ℝ[X] :=
  (1 + (n : ℝ[X]) * X) * f + X * (1 - X) * derivative f

noncomputable def basis (j s : ℕ) : ℝ[X] := X ^ j * (1 - X) ^ (2 * s)

noncomputable def lift (m : ℕ) (f : ℝ[X]) : ℝ[X] :=
  MvPolynomial.eval₂ C ![X, (1 - X) ^ 2] (f.homogenize m)

theorem weighted_derivative_X (j : ℕ) :
    (X : ℝ[X]) * derivative (X ^ j) = (j : ℝ[X]) * X ^ j := by
  cases j with
  | zero => simp
  | succ j =>
    rw [derivative_X_pow_succ, pow_succ]
    simp only [map_add, map_natCast, map_one]
    push_cast
    ring

theorem weighted_derivative_one_sub_X (s : ℕ) :
    (1 - X : ℝ[X]) * derivative ((1 - X) ^ s) = -(s : ℝ[X]) * (1 - X) ^ s := by
  cases s with
  | zero => simp
  | succ s =>
    rw [derivative_pow, derivative_sub, derivative_one, derivative_X]
    simp only [Nat.add_sub_cancel, zero_sub, mul_neg, mul_one, pow_succ, map_natCast]
    ring

theorem weighted_derivative_basis (j s : ℕ) :
    X * (1 - X) * derivative (basis j s) =
      ((j : ℝ[X]) * (1 - X) - (2 * s : ℝ[X]) * X) * basis j s := by
  unfold basis
  rw [derivative_mul]
  calc
    (X : ℝ[X]) * (1 - X) * (derivative (X ^ j) * (1 - X) ^ (2 * s) +
        X ^ j * derivative ((1 - X) ^ (2 * s))) =
        (1 - X) * (X * derivative (X ^ j)) * (1 - X) ^ (2 * s) +
          X * X ^ j * ((1 - X) * derivative ((1 - X) ^ (2 * s))) := by ring
    _ = _ := by
      rw [weighted_derivative_X, weighted_derivative_one_sub_X]
      push_cast
      ring

theorem E_odd_basis (j s : ℕ) :
    E (2 * (j + s) + 1) (basis j s) = (1 + X) * ((j + 1 : ℕ) : ℝ[X]) * basis j s := by
  unfold E
  rw [weighted_derivative_basis]
  push_cast
  ring

theorem E_even_basis (j s : ℕ) :
    E (2 * (j + s + 1)) ((1 + X) * basis j s) =
      ((j + 1 : ℕ) : ℝ[X]) * basis j (s + 1) +
        ((4 * j + 6 : ℕ) : ℝ[X]) * basis (j + 1) s := by
  unfold E
  rw [derivative_mul]
  simp only [derivative_add, derivative_one, derivative_X, zero_add, one_mul]
  rw [show X * (1 - X) * (basis j s + (1 + X) * derivative (basis j s)) =
    X * (1 - X) * basis j s + (1 + X) * (X * (1 - X) * derivative (basis j s)) by ring,
    weighted_derivative_basis]
  unfold basis
  rw [show 2 * (s + 1) = 2 * s + 2 by omega, pow_add, pow_succ]
  push_cast
  ring

@[simp] theorem lift_zero (m : ℕ) : lift m 0 = 0 := by simp [lift]

@[simp] theorem lift_add (m : ℕ) (f g : ℝ[X]) : lift m (f + g) = lift m f + lift m g := by
  simp [lift]

@[simp] theorem lift_C_mul (m : ℕ) (a : ℝ) (f : ℝ[X]) :
    lift m (C a * f) = C a * lift m f := by simp [lift]

theorem lift_X_pow {j m : ℕ} (h : j ≤ m) : lift m (X ^ j) = basis j (m - j) := by
  simp only [lift, homogenize_X_pow h, MvPolynomial.eval₂_mul, MvPolynomial.eval₂_pow,
    MvPolynomial.eval₂_X, Matrix.cons_val_zero, Matrix.cons_val_one, pow_mul, basis]

@[simp] theorem E_zero (n : ℕ) : E n 0 = 0 := by simp [E]

theorem E_add (n : ℕ) (f g : ℝ[X]) : E n (f + g) = E n f + E n g := by
  simp [E, mul_add]
  ring

theorem E_C_mul (n : ℕ) (a : ℝ) (f : ℝ[X]) : E n (C a * f) = C a * E n f := by
  simp [E, derivative_mul]
  ring

theorem U_add (f g : ℝ[X]) : U (f + g) = U f + U g := by
  simp [U, mul_add]
  ring

theorem U_C_mul (a : ℝ) (f : ℝ[X]) : U (C a * f) = C a * U f := by
  simp [U, derivative_mul]
  ring

theorem T_add (f g : ℝ[X]) : T (f + g) = T f + T g := by
  simp [T, mul_add]
  ring

theorem T_C_mul (a : ℝ) (f : ℝ[X]) : T (C a * f) = C a * T f := by
  simp [T, derivative_mul]
  ring

theorem U_X_pow (j : ℕ) : U (X ^ j) = ((j + 1 : ℕ) : ℝ[X]) * X ^ j := by
  rw [U, weighted_derivative_X]
  push_cast
  ring

theorem T_X_pow (j : ℕ) : T (X ^ j) =
    ((j + 1 : ℕ) : ℝ[X]) * X ^ j + ((4 * j + 6 : ℕ) : ℝ[X]) * X ^ (j + 1) := by
  rw [T, show X * (1 + C 4 * X) * derivative (X ^ j : ℝ[X]) =
      (1 + C 4 * X) * (X * derivative (X ^ j)) by ring, weighted_derivative_X, pow_succ]
  simp only [map_ofNat]
  push_cast
  ring

theorem lift_U {m : ℕ} {f : ℝ[X]} (hf : f.natDegree ≤ m) :
    E (2 * m + 1) (lift m f) = (1 + X) * lift m (U f) := by
  apply Polynomial.induction_with_natDegree_le
    (fun f => E (2 * m + 1) (lift m f) = (1 + X) * lift m (U f)) m
  · simp [U]
  · intro j a _ hj
    rw [lift_C_mul, E_C_mul, U_C_mul, lift_C_mul, lift_X_pow hj,
      U_X_pow, ← map_natCast C, lift_C_mul, lift_X_pow hj]
    rw [show 2 * m + 1 = 2 * (j + (m - j)) + 1 by omega, E_odd_basis]
    simp only [map_natCast]
    ring
  · intro f g _ _ ihf ihg
    rw [lift_add, E_add, U_add, lift_add, ihf, ihg, mul_add]
  · exact hf

theorem lift_T {m : ℕ} {f : ℝ[X]} (hf : f.natDegree ≤ m) :
    E (2 * (m + 1)) ((1 + X) * lift m f) = lift (m + 1) (T f) := by
  apply Polynomial.induction_with_natDegree_le
    (fun f => E (2 * (m + 1)) ((1 + X) * lift m f) = lift (m + 1) (T f)) m
  · simp [T]
  · intro j a _ hj
    rw [lift_C_mul, show (1 + X) * (C a * lift m (X ^ j)) =
      C a * ((1 + X) * lift m (X ^ j)) by ring, E_C_mul, T_C_mul, lift_C_mul]
    rw [lift_X_pow hj, T_X_pow, lift_add, ← map_natCast C, lift_C_mul,
      ← map_natCast C, lift_C_mul, lift_X_pow (by omega : j ≤ m + 1),
      lift_X_pow (by omega : j + 1 ≤ m + 1)]
    rw [show m + 1 = j + (m - j) + 1 by omega, E_even_basis]
    simp only [map_natCast]
    rw [show j + (m - j) + 1 - j = m - j + 1 by omega,
      show j + (m - j) + 1 - (j + 1) = m - j by omega]
  · intro f g _ _ ihf ihg
    rw [lift_add, mul_add (1 + X) (lift m f) (lift m g), E_add, T_add, lift_add, ihf, ihg]
  · exact hf

end ResearchMain.EulerianPencil
