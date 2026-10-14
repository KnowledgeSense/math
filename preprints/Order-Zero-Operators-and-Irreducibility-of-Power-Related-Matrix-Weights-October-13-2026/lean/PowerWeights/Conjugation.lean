import PowerWeights.FactorAlgebra
import PowerWeights.PolynomialCoefficients

namespace PowerWeights

open Polynomial

noncomputable def inverseFactor (N : ℕ) (a : ℕ → ℝ) : PolynomialMatrix N :=
  1 - (X : ℂ[X]) • constant (pathMatrix N a)

noncomputable def transformed {N : ℕ} (a : ℕ → ℝ)
    (F : Matrix (Fin N) (Fin N) ℂ) : PolynomialMatrix N :=
  inverseFactor N a * constant F * factor N a

@[simp] theorem adjoint_one (N : ℕ) : adjoint (1 : PolynomialMatrix N) = 1 := by
  apply Matrix.ext
  intro i j
  by_cases hij : i=j <;> simp [adjoint, conjugate, Matrix.one_apply, hij, eq_comm]

 theorem transformed_symmetry {N : ℕ} (s : Schedule) (a : ℕ → ℝ)
    (F : Matrix (Fin N) (Fin N) ℂ)
    (h : constant F * polynomialWeight N s a =
      polynomialWeight N s a * adjoint (constant F)) :
    transformed a F * diagonal N s = diagonal N s * adjoint (transformed a F) := by
  let T := factor N a
  let U := inverseFactor N a
  let D := diagonal N s
  have hut : U*T=1 := factor_inverse_left N a
  have hstar : adjoint T * adjoint U = 1 := by
    rw [← adjoint_mul, hut, adjoint_one]
  have hx := congrArg (fun M : PolynomialMatrix N => U*M*adjoint U) h
  have hl : U*(constant F*polynomialWeight N s a)*adjoint U = transformed a F*D := by
    change U*(constant F*(T*D*adjoint T))*adjoint U = (U*constant F*T)*D
    calc
      _ = (U*constant F*T)*D*(adjoint T*adjoint U) := by simp only [mul_assoc]
      _ = _ := by rw [hstar, mul_one]
  have hr : U*(polynomialWeight N s a*adjoint (constant F))*adjoint U =
      D*adjoint (transformed a F) := by
    change U*((T*D*adjoint T)*adjoint (constant F))*adjoint U =
      D*adjoint (U*constant F*T)
    rw [adjoint_mul, adjoint_mul]
    calc
      _ = (U*T)*(D*(adjoint T*(adjoint (constant F)*adjoint U))) := by
        simp only [mul_assoc]
      _ = _ := by rw [hut, one_mul]
  exact hl.symm.trans (hx.trans hr)

 theorem transformed_expansion {N : ℕ} (a : ℕ → ℝ)
    (F : Matrix (Fin N) (Fin N) ℂ) :
    transformed a F = constant F +
      (X : ℂ[X]) • constant (F*pathMatrix N a-pathMatrix N a*F) -
      (X : ℂ[X])^2 • constant (pathMatrix N a*F*pathMatrix N a) := by
  simp only [transformed, inverseFactor, factor, sub_mul, mul_add, one_mul, mul_one,
    Matrix.smul_mul, Matrix.mul_smul, constant_sub, constant_mul, smul_sub,
    smul_smul, pow_two]
  abel

 theorem transformed_entry {N : ℕ} (a : ℕ → ℝ)
    (F : Matrix (Fin N) (Fin N) ℂ) (i j : Fin N) :
    transformed a F i j = quadratic (F i j)
      ((F*pathMatrix N a-pathMatrix N a*F) i j)
      (-(pathMatrix N a*F*pathMatrix N a) i j) := by
  rw [transformed_expansion]
  simp only [Matrix.sub_apply, Matrix.add_apply, Matrix.smul_apply, constant,
    Matrix.map_apply, smul_eq_mul, quadratic, map_neg]
  ring

 theorem transformed_entry_relation {N : ℕ} (s : Schedule) (a : ℕ → ℝ)
    (F : Matrix (Fin N) (Fin N) ℂ)
    (h : constant F * polynomialWeight N s a =
      polynomialWeight N s a * adjoint (constant F)) (i j : Fin N) :
    transformed a F i j * X ^ exponent s j.val =
      conjugate (transformed a F j i) * X ^ exponent s i.val := by
  have hh := congrArg (fun M : PolynomialMatrix N => M i j) (transformed_symmetry s a F h)
  simpa [diagonal, Matrix.mul_diagonal, Matrix.diagonal_mul, adjoint, mul_comm] using hh

end PowerWeights
