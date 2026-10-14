import MainTheorems.AHOConstants.PositivePowers

namespace ResearchMain.AHOConstants

open scoped ComplexOrder MatrixOrder

variable {I : Type*} [Fintype I] [DecidableEq I]

noncomputable def polarAbsolute (X : Matrix I I ℂ) : Matrix I I ℂ :=
  spectralPower (star X * X) (1 / 2)

noncomputable def polarInverse (X : Matrix I I ℂ) : Matrix I I ℂ :=
  spectralPower (star X * X) (-(1 / 2))

noncomputable def polarUnitary (X : Matrix I I ℂ) : Matrix I I ℂ :=
  X * polarInverse X

theorem gram_posDef {X : Matrix I I ℂ} (hX : IsUnit X) : (star X * X).PosDef := by
  have h := (Matrix.IsUnit.posDef_star_left_conjugate_iff hX).mpr
    (Matrix.PosDef.one (n := I) (R := ℂ))
  simpa only [Matrix.mul_one] using h

theorem polarAbsolute_posDef {X : Matrix I I ℂ} (hX : IsUnit X) :
    (polarAbsolute X).PosDef := spectralPower_posDef (gram_posDef hX) _

theorem polarInverse_posDef {X : Matrix I I ℂ} (hX : IsUnit X) :
    (polarInverse X).PosDef := spectralPower_posDef (gram_posDef hX) _

theorem polarAbsolute_square {X : Matrix I I ℂ} (hX : IsUnit X) :
    polarAbsolute X * polarAbsolute X = star X * X := by
  unfold polarAbsolute
  rw [← spectralPower_add_real (gram_posDef hX)]
  rw [show (1 / 2 : ℝ) + 1 / 2 = 1 by norm_num]
  exact spectralPower_one _ (gram_posDef hX).posSemidef

theorem polarInverse_right {X : Matrix I I ℂ} (hX : IsUnit X) :
    polarAbsolute X * polarInverse X = 1 :=
  spectralPower_inverse_right (gram_posDef hX) (1 / 2)

theorem polarInverse_left {X : Matrix I I ℂ} (hX : IsUnit X) :
    polarInverse X * polarAbsolute X = 1 :=
  spectralPower_inverse_left (gram_posDef hX) (1 / 2)

theorem polarUnitary_mem {X : Matrix I I ℂ} (hX : IsUnit X) :
    polarUnitary X ∈ unitary (Matrix I I ℂ) := by
  have hP := (polarInverse_posDef hX).isHermitian
  have hI : IsUnit (polarInverse X) := spectralPower_isUnit (gram_posDef hX) _
  have hU : IsUnit (polarUnitary X) := hX.mul hI
  have hPstar : star (polarInverse X) = polarInverse X := hP.isSelfAdjoint.star_eq
  apply hU.mem_unitary_of_star_mul_self
  unfold polarUnitary
  rw [star_mul, hPstar]
  calc
    polarInverse X * star X * (X * polarInverse X) =
        polarInverse X * (star X * X) * polarInverse X := by simp only [Matrix.mul_assoc]
    _ = polarInverse X * (polarAbsolute X * polarAbsolute X) * polarInverse X := by
      rw [polarAbsolute_square hX]
    _ = (polarInverse X * polarAbsolute X) * (polarAbsolute X * polarInverse X) := by
      simp only [Matrix.mul_assoc]
    _ = 1 := by rw [polarInverse_left hX, polarInverse_right hX, Matrix.one_mul]

theorem polar_decomposition {X : Matrix I I ℂ} (hX : IsUnit X) :
    X = polarUnitary X * polarAbsolute X := by
  unfold polarUnitary
  rw [Matrix.mul_assoc, polarInverse_left hX, Matrix.mul_one]

end ResearchMain.AHOConstants
