import MainTheorems.AHOConstants.ComplexPowers
import MainTheorems.AHOConstants.UnitarySchatten

namespace ResearchMain.AHOConstants

open scoped ComplexOrder MatrixOrder
open ResearchMain.DiagonalSchatten

variable {I : Type*} [Fintype I] [DecidableEq I]

theorem complexPower_vertical_line {A : Matrix I I ℂ} (hA : A.PosDef) (z : ℂ) :
    complexPower hA z =
      spectralPower A z.re * complexPower hA ((z.im : ℂ) * Complex.I) := by
  rw [← complexPower_real hA z.re, ← complexPower_add]
  congr 1
  apply Complex.ext <;> simp

theorem complexPower_vertical_line_left {A : Matrix I I ℂ} (hA : A.PosDef) (z : ℂ) :
    complexPower hA z =
      complexPower hA ((z.im : ℂ) * Complex.I) * spectralPower A z.re := by
  rw [← complexPower_real hA z.re, ← complexPower_add]
  congr 1
  apply Complex.ext <;> simp

theorem complexPower_product_half_boundary {A B : Matrix I I ℂ}
    (hA : A.PosDef) (hB : B.PosDef) {z : ℂ} (hz : z.re = 1) :
    schattenNorm 2 (complexPower hA (z / 2) * complexPower hB (z / 2)) =
      schattenNorm 2 (spectralPower A (1 / 2) * spectralPower B (1 / 2)) := by
  rw [complexPower_vertical_line_left hA (z / 2), complexPower_vertical_line hB (z / 2)]
  have hr : (z / 2).re = (1 / 2 : ℝ) := by simp [hz]
  rw [hr]
  rw [Matrix.mul_assoc, ← Matrix.mul_assoc (spectralPower A (1 / 2))
    (spectralPower B (1 / 2))]
  rw [schattenNorm_unitary_left (complexPower_imaginary_unitary hA _),
    schattenNorm_unitary_right (complexPower_imaginary_unitary hB _) (by norm_num)]

theorem complexPower_product_zero_boundary {A B : Matrix I I ℂ}
    (hA : A.PosDef) (hB : B.PosDef) {z : ℂ} (hz : z.re = 0) :
    complexPower hA (z / 2) * complexPower hB (z / 2) ∈ unitary (Matrix I I ℂ) := by
  rw [complexPower_vertical_line hA (z / 2), complexPower_vertical_line hB (z / 2)]
  have hr : (z / 2).re = 0 := by simp [hz]
  rw [hr, spectralPower_zero A hA.posSemidef, spectralPower_zero B hB.posSemidef,
    Matrix.one_mul, Matrix.one_mul]
  exact (unitary (Matrix I I ℂ)).mul_mem (complexPower_imaginary_unitary hA _)
    (complexPower_imaginary_unitary hB _)

theorem complexPower_half_boundary {A : Matrix I I ℂ}
    (hA : A.PosDef) {z : ℂ} (hz : z.re = 1 / 2) :
    schattenNorm 2 (complexPower hA z) = schattenNorm 2 (spectralPower A (1 / 2)) := by
  rw [complexPower_vertical_line hA z, hz,
    schattenNorm_unitary_right (complexPower_imaginary_unitary hA _) (by norm_num)]

end ResearchMain.AHOConstants
