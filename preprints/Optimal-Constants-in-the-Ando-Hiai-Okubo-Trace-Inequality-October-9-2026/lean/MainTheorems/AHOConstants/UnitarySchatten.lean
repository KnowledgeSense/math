import MainTheorems.DiagonalSchatten.GramSpectrum
import Mathlib.Algebra.Star.Unitary

namespace ResearchMain.AHOConstants

open ResearchMain.DiagonalSchatten

variable {I : Type*} [Fintype I] [DecidableEq I]

theorem schattenPower_unitary_left {U : Matrix I I ℂ}
    (hU : U ∈ unitary (Matrix I I ℂ)) (p : ℝ) (X : Matrix I I ℂ) :
    schattenPower p (U * X) = schattenPower p X := by
  have hG : (U * X).conjTranspose * (U * X) = X.conjTranspose * X := by
    rw [Matrix.conjTranspose_mul]
    change (star X * star U) * (U * X) = star X * X
    calc
      (star X * star U) * (U * X) = star X * (star U * U) * X := by
        simp only [Matrix.mul_assoc]
      _ = star X * X := by rw [Unitary.star_mul_self_of_mem hU, Matrix.mul_one]
  rw [schattenPower_eq_gram_roots, hG, schattenPower_eq_gram_roots]

theorem schattenPower_unitary_right {U : Matrix I I ℂ}
    (hU : U ∈ unitary (Matrix I I ℂ)) {p : ℝ} (hp : 0 < p) (X : Matrix I I ℂ) :
    schattenPower p (X * U) = schattenPower p X := by
  have hG : (X * U) * (X * U).conjTranspose = X * X.conjTranspose := by
    rw [Matrix.conjTranspose_mul]
    change (X * U) * (star U * star X) = X * star X
    calc
      (X * U) * (star U * star X) = X * (U * star U) * star X := by
        simp only [Matrix.mul_assoc]
      _ = X * star X := by rw [Unitary.mul_star_self_of_mem hU, Matrix.mul_one]
  rw [schattenPower_eq_row_gram_roots hp, hG, schattenPower_eq_row_gram_roots hp]

theorem schattenNorm_unitary_left {U : Matrix I I ℂ}
    (hU : U ∈ unitary (Matrix I I ℂ)) (p : ℝ) (X : Matrix I I ℂ) :
    schattenNorm p (U * X) = schattenNorm p X := by
  unfold schattenNorm
  rw [schattenPower_unitary_left hU]

theorem schattenNorm_unitary_right {U : Matrix I I ℂ}
    (hU : U ∈ unitary (Matrix I I ℂ)) {p : ℝ} (hp : 0 < p) (X : Matrix I I ℂ) :
    schattenNorm p (X * U) = schattenNorm p X := by
  unfold schattenNorm
  rw [schattenPower_unitary_right hU hp]

end ResearchMain.AHOConstants
