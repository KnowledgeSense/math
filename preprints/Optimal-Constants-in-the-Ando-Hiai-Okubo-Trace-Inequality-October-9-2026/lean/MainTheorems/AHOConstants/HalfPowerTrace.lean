import MainTheorems.AHOConstants.HilbertSchmidt
import MainTheorems.AHOConstants.SpectralPowers

namespace ResearchMain.AHOConstants

open scoped BigOperators ComplexOrder MatrixOrder
open ResearchMain.DiagonalSchatten

variable {I : Type*} [Fintype I] [DecidableEq I]

theorem schattenPower_two_trace_gram (X : Matrix I I ℂ) :
    schattenPower 2 X = (Matrix.trace (star X * X)).re := by
  rw [schattenPower_two]
  simp only [Matrix.trace, Matrix.diag_apply, Matrix.mul_apply,
    Matrix.star_eq_conjTranspose, Matrix.conjTranspose_apply, Complex.re_sum]
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro i _
  simpa only [RCLike.star_def, ← Complex.ofReal_pow, Complex.ofReal_re] using
    (congrArg Complex.re (Complex.conj_mul' (X i j))).symm

theorem halfPower_square {A : Matrix I I ℂ} (hA : A.PosSemidef) :
    spectralPower A (1 / 2) * spectralPower A (1 / 2) = A := by
  rw [← spectralPower_add A hA (by norm_num) (by norm_num)]
  rw [show (1 / 2 : ℝ) + 1 / 2 = 1 by norm_num, spectralPower_one A hA]

theorem halfPower_product_trace {A B : Matrix I I ℂ}
    (hA : A.PosSemidef) (hB : B.PosSemidef) :
    schattenPower 2 (spectralPower A (1 / 2) * spectralPower B (1 / 2)) =
      (Matrix.trace (A * B)).re := by
  let P := spectralPower A (1 / 2)
  let Q := spectralPower B (1 / 2)
  have hP : star P = P := (spectralPower_positiveSemidefinite A (1 / 2)).isHermitian.isSelfAdjoint.star_eq
  have hQ : star Q = Q := (spectralPower_positiveSemidefinite B (1 / 2)).isHermitian.isSelfAdjoint.star_eq
  have hPP : P * P = A := halfPower_square hA
  have hQQ : Q * Q = B := halfPower_square hB
  have hG : star (P * Q) * (P * Q) = Q * A * Q := by
    rw [star_mul, hP, hQ]
    calc
      Q * P * (P * Q) = Q * (P * P) * Q := by simp only [Matrix.mul_assoc]
      _ = Q * A * Q := by rw [hPP]
  change schattenPower 2 (P * Q) = _
  rw [schattenPower_two_trace_gram, hG, Matrix.trace_mul_cycle,
    hQQ, Matrix.trace_mul_comm]

theorem halfPower_product_norm_square {A B : Matrix I I ℂ}
    (hA : A.PosSemidef) (hB : B.PosSemidef) :
    schattenNorm 2 (spectralPower A (1 / 2) * spectralPower B (1 / 2)) ^ 2 =
      (Matrix.trace (A * B)).re := by
  rw [schattenNorm_two_square, halfPower_product_trace hA hB]

theorem halfPower_norm_square {A : Matrix I I ℂ} (hA : A.PosSemidef) :
    schattenNorm 2 (spectralPower A (1 / 2)) ^ 2 = (Matrix.trace A).re := by
  rw [schattenNorm_two_square, schattenPower_two_trace_gram,
    (spectralPower_positiveSemidefinite A (1 / 2)).isHermitian.isSelfAdjoint.star_eq,
    halfPower_square hA]

end ResearchMain.AHOConstants
