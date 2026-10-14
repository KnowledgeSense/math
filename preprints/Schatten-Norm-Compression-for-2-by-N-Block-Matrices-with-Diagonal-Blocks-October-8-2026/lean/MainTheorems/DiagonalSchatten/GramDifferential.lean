import MainTheorems.DiagonalSchatten.GramFiber
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul

namespace ResearchMain.DiagonalSchatten

open scoped BigOperators Matrix.Norms.Elementwise

variable {J : Type*} [Fintype J]

def rowDirection (X Y : Matrix (Fin 2) J ℝ) (t : ℝ) : Matrix (Fin 2) J ℝ :=
  Matrix.of fun i j => X i j + t * Y i j

omit [Fintype J] in
theorem rowDirection_zero (X Y : Matrix (Fin 2) J ℝ) : rowDirection X Y 0 = X := by
  ext i j
  simp [rowDirection]

theorem rowDirection_hasDerivAt (X Y : Matrix (Fin 2) J ℝ) :
    HasDerivAt (rowDirection X Y) Y 0 := by
  change HasDerivAt (fun t : ℝ => X + t • Y) Y 0
  convert! (hasDerivAt_const (0 : ℝ) X).add ((hasDerivAt_id (0 : ℝ)).smul_const Y) using 1
  simp

theorem gramFirst_direction_deriv (X Y : Matrix (Fin 2) J ℝ) :
    HasDerivAt (fun t : ℝ => gramFirst (rowDirection X Y t))
      (2 * ∑ j, X 0 j * Y 0 j) 0 := by
  have hterm (j : J) : HasDerivAt (fun t : ℝ => (X 0 j + t * Y 0 j) ^ 2)
      (2 * (X 0 j * Y 0 j)) 0 := by
    simpa [mul_assoc] using
      (((hasDerivAt_const (0 : ℝ) (X 0 j)).add ((hasDerivAt_id (0 : ℝ)).mul_const (Y 0 j))).fun_pow 2)
  simpa only [gramFirst, rowDirection, Matrix.of_apply, ← Finset.mul_sum] using
    HasDerivAt.fun_sum (u := Finset.univ) (fun j _ => hterm j)

theorem gramSecond_direction_deriv (X Y : Matrix (Fin 2) J ℝ) :
    HasDerivAt (fun t : ℝ => gramSecond (rowDirection X Y t))
      (2 * ∑ j, X 1 j * Y 1 j) 0 := by
  have hterm (j : J) : HasDerivAt (fun t : ℝ => (X 1 j + t * Y 1 j) ^ 2)
      (2 * (X 1 j * Y 1 j)) 0 := by
    simpa [mul_assoc] using
      (((hasDerivAt_const (0 : ℝ) (X 1 j)).add ((hasDerivAt_id (0 : ℝ)).mul_const (Y 1 j))).fun_pow 2)
  simpa only [gramSecond, rowDirection, Matrix.of_apply, ← Finset.mul_sum] using
    HasDerivAt.fun_sum (u := Finset.univ) (fun j _ => hterm j)

theorem gramCross_direction_deriv (X Y : Matrix (Fin 2) J ℝ) :
    HasDerivAt (fun t : ℝ => gramCross (rowDirection X Y t))
      (∑ j, (Y 0 j * X 1 j + X 0 j * Y 1 j)) 0 := by
  have hterm (j : J) :
      HasDerivAt (fun t : ℝ => (X 0 j + t * Y 0 j) * (X 1 j + t * Y 1 j))
        (Y 0 j * X 1 j + X 0 j * Y 1 j) 0 := by
    convert! ((hasDerivAt_const (0 : ℝ) (X 0 j)).add ((hasDerivAt_id (0 : ℝ)).mul_const (Y 0 j))).mul
      ((hasDerivAt_const (0 : ℝ) (X 1 j)).add ((hasDerivAt_id (0 : ℝ)).mul_const (Y 1 j)))
      using 1
    simp
  convert! HasDerivAt.fun_sum (u := Finset.univ) (fun j _ => hterm j) using 1

theorem fderiv_gramFirst (X Y : Matrix (Fin 2) J ℝ) :
    fderiv ℝ gramFirst X Y = 2 * ∑ j, X 0 j * Y 0 j := by
  have hd : DifferentiableAt ℝ gramFirst X := by unfold gramFirst; fun_prop
  have h := hd.hasFDerivAt.comp_hasDerivAt_of_eq 0 (rowDirection_hasDerivAt X Y)
    (rowDirection_zero X Y).symm
  exact h.unique (gramFirst_direction_deriv X Y)

theorem fderiv_gramSecond (X Y : Matrix (Fin 2) J ℝ) :
    fderiv ℝ gramSecond X Y = 2 * ∑ j, X 1 j * Y 1 j := by
  have hd : DifferentiableAt ℝ gramSecond X := by unfold gramSecond; fun_prop
  have h := hd.hasFDerivAt.comp_hasDerivAt_of_eq 0 (rowDirection_hasDerivAt X Y)
    (rowDirection_zero X Y).symm
  exact h.unique (gramSecond_direction_deriv X Y)

theorem fderiv_gramCross (X Y : Matrix (Fin 2) J ℝ) :
    fderiv ℝ gramCross X Y = ∑ j, (Y 0 j * X 1 j + X 0 j * Y 1 j) := by
  have hd : DifferentiableAt ℝ gramCross X := by unfold gramCross; fun_prop
  have h := hd.hasFDerivAt.comp_hasDerivAt_of_eq 0 (rowDirection_hasDerivAt X Y)
    (rowDirection_zero X Y).symm
  exact h.unique (gramCross_direction_deriv X Y)

end ResearchMain.DiagonalSchatten
