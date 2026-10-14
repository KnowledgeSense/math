import PowerWeights.Path

namespace PowerWeights

open Polynomial

@[simp] theorem constant_mul {N : ℕ} (F G : Matrix (Fin N) (Fin N) ℂ) :
    constant (F*G) = constant F * constant G :=
  (Polynomial.C.mapMatrix).map_mul F G

@[simp] theorem constant_zero (N : ℕ) : constant (0 : Matrix (Fin N) (Fin N) ℂ) = 0 :=
  (Polynomial.C.mapMatrix).map_zero

@[simp] theorem constant_one (N : ℕ) : constant (1 : Matrix (Fin N) (Fin N) ℂ) = 1 :=
  (Polynomial.C.mapMatrix).map_one

@[simp] theorem constant_add {N : ℕ} (F G : Matrix (Fin N) (Fin N) ℂ) :
    constant (F+G) = constant F + constant G :=
  (Polynomial.C.mapMatrix).map_add F G

@[simp] theorem constant_sub {N : ℕ} (F G : Matrix (Fin N) (Fin N) ℂ) :
    constant (F-G) = constant F - constant G :=
  (Polynomial.C.mapMatrix).map_sub F G

@[simp] theorem conjugate_C (z : ℂ) : conjugate (C z) = C (star z) := by
  simp [conjugate]

@[simp] theorem conjugate_X : conjugate (X : ℂ[X]) = X := by
  simp [conjugate]

@[simp] theorem conjugate_involutive (p : ℂ[X]) : conjugate (conjugate p) = p := by
  ext n
  simp [conjugate, Polynomial.coeff_map]

@[simp] theorem adjoint_involutive {N : ℕ} (P : PolynomialMatrix N) :
    adjoint (adjoint P) = P := by
  apply Matrix.ext
  intro i j
  exact conjugate_involutive _

 theorem adjoint_mul {N : ℕ} (P Q : PolynomialMatrix N) :
    adjoint (P*Q) = adjoint Q * adjoint P := by
  ext i j
  simp [adjoint, conjugate, Matrix.mul_apply, Polynomial.map_sum, mul_comm]

@[simp] theorem adjoint_constant {N : ℕ} (F : Matrix (Fin N) (Fin N) ℂ) :
    adjoint (constant F) = constant F.conjTranspose := by
  ext i j
  simp [adjoint, constant, Matrix.conjTranspose_apply]

 theorem factor_inverse_left (N : ℕ) (a : ℕ → ℝ) :
    (1 - (X : ℂ[X]) • constant (pathMatrix N a)) * factor N a = 1 := by
  have hz : constant (pathMatrix N a) * constant (pathMatrix N a) = 0 := by
    rw [← constant_mul, path_square_zero, constant_zero]
  simp [factor, sub_mul, mul_add, hz]

 theorem factor_inverse_right (N : ℕ) (a : ℕ → ℝ) :
    factor N a * (1 - (X : ℂ[X]) • constant (pathMatrix N a)) = 1 := by
  have hz : constant (pathMatrix N a) * constant (pathMatrix N a) = 0 := by
    rw [← constant_mul, path_square_zero, constant_zero]
  simp [factor, mul_sub, add_mul, hz]

end PowerWeights
