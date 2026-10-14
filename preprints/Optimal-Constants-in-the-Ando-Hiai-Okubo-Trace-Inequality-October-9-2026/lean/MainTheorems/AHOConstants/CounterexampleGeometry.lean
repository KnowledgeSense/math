import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Tactic

namespace ResearchMain.AHOConstants

open scoped BigOperators

noncomputable def rotationCos (z : ℝ) : ℝ := (1 - z ^ 2) / (1 + z ^ 2)

noncomputable def rotationSin (z : ℝ) : ℝ := 2 * z / (1 + z ^ 2)

noncomputable def smallEigenvector (z : ℝ) : Fin 3 → ℝ :=
  ![rotationCos z / 2 - rotationSin z / Real.sqrt 2,
    -(1 / 2), rotationSin z / 2 + rotationCos z / Real.sqrt 2]

noncomputable def largeEigenvector (z : ℝ) : Fin 3 → ℝ :=
  ![rotationCos z / Real.sqrt 2, 1 / Real.sqrt 2, rotationSin z / Real.sqrt 2]

theorem rotation_denominator_positive (z : ℝ) : 0 < 1 + z ^ 2 := by
  positivity

theorem rotation_circle (z : ℝ) : rotationCos z ^ 2 + rotationSin z ^ 2 = 1 := by
  have hd : 1 + z ^ 2 ≠ 0 := ne_of_gt (rotation_denominator_positive z)
  dsimp [rotationCos, rotationSin]
  field_simp
  ring

theorem square_root_two_bounds : (4 / 3 : ℝ) < Real.sqrt 2 ∧ Real.sqrt 2 < 3 / 2 := by
  have hs := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)
  have hp : 0 ≤ Real.sqrt (2 : ℝ) := Real.sqrt_nonneg _
  constructor <;> nlinarith

theorem smallEigenvector_norm (z : ℝ) :
    ∑ i : Fin 3, smallEigenvector z i ^ 2 = 1 := by
  have hs := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)
  have hp : Real.sqrt (2 : ℝ) ≠ 0 := ne_of_gt (Real.sqrt_pos.2 (by norm_num))
  have hc := rotation_circle z
  simp only [Fin.sum_univ_succ, smallEigenvector, Matrix.cons_val_zero,
    Matrix.cons_val_succ, Fin.isValue, Fin.sum_univ_zero, add_zero]
  field_simp
  nlinarith

theorem largeEigenvector_norm (z : ℝ) :
    ∑ i : Fin 3, largeEigenvector z i ^ 2 = 1 := by
  have hs := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)
  have hp : Real.sqrt (2 : ℝ) ≠ 0 := ne_of_gt (Real.sqrt_pos.2 (by norm_num))
  have hc := rotation_circle z
  simp only [Fin.sum_univ_succ, largeEigenvector, Matrix.cons_val_zero,
    Matrix.cons_val_succ, Fin.isValue, Fin.sum_univ_zero, add_zero]
  field_simp
  nlinarith

theorem eigenvectors_orthogonal (z : ℝ) :
    ∑ i : Fin 3, smallEigenvector z i * largeEigenvector z i = 0 := by
  have hs := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)
  have hp : Real.sqrt (2 : ℝ) ≠ 0 := ne_of_gt (Real.sqrt_pos.2 (by norm_num))
  have hc := congrArg (fun r : ℝ => r * Real.sqrt 2) (rotation_circle z)
  simp only [Fin.sum_univ_succ, smallEigenvector, largeEigenvector,
    Matrix.cons_val_zero, Matrix.cons_val_succ, Fin.isValue,
    Fin.sum_univ_zero, add_zero]
  field_simp
  nlinarith

theorem rotation_small_bounds {z : ℝ} (hz : 0 < z) (hz' : z ≤ 1 / 8) :
    (63 / 65 : ℝ) ≤ rotationCos z ∧
      0 < rotationSin z ∧ rotationSin z ≤ 1 / 4 := by
  have hd := rotation_denominator_positive z
  have hzsq : z ^ 2 ≤ (1 / 64 : ℝ) := by nlinarith
  constructor
  · dsimp [rotationCos]
    apply (le_div_iff₀ hd).2
    nlinarith
  constructor
  · exact div_pos (by linarith) hd
  · dsimp [rotationSin]
    apply (div_le_iff₀ hd).2
    nlinarith

theorem active_overlaps_positive {z : ℝ} (hz : 0 < z) (hz' : z ≤ 1 / 8) :
    (1 / 4 : ℝ) < smallEigenvector z 0 ∧
      (1 / 2 : ℝ) < smallEigenvector z 2 ∧
      (1 / 2 : ℝ) < largeEigenvector z 0 ∧
      z < largeEigenvector z 2 := by
  obtain ⟨hc, ha, ha'⟩ := rotation_small_bounds hz hz'
  obtain ⟨hslo, hshi⟩ := square_root_two_bounds
  have hspos : 0 < Real.sqrt (2 : ℝ) := Real.sqrt_pos.2 (by norm_num)
  have hdiva : rotationSin z / Real.sqrt 2 < (3 / 16 : ℝ) := by
    apply (div_lt_iff₀ hspos).2
    nlinarith
  have hdivc : (1 / 2 : ℝ) < rotationCos z / Real.sqrt 2 := by
    apply (lt_div_iff₀ hspos).2
    linarith
  have hzsq : z ^ 2 ≤ (1 / 64 : ℝ) := by nlinarith
  have hsin : z * Real.sqrt 2 < rotationSin z := by
    dsimp [rotationSin]
    apply (lt_div_iff₀ (rotation_denominator_positive z)).2
    have hprod : Real.sqrt 2 * (1 + z ^ 2) < (3 / 2 : ℝ) * (65 / 64) := by
      calc
        Real.sqrt 2 * (1 + z ^ 2) < (3 / 2 : ℝ) * (1 + z ^ 2) :=
          mul_lt_mul_of_pos_right hshi (rotation_denominator_positive z)
        _ ≤ (3 / 2 : ℝ) * (65 / 64) := by nlinarith
    nlinarith [mul_pos hz (by norm_num : (0 : ℝ) < 61 / 128)]
  have hdivsin : z < rotationSin z / Real.sqrt 2 := (lt_div_iff₀ hspos).2 hsin
  change (1 / 4 : ℝ) < rotationCos z / 2 - rotationSin z / Real.sqrt 2 ∧
    (1 / 2 : ℝ) < rotationSin z / 2 + rotationCos z / Real.sqrt 2 ∧
    (1 / 2 : ℝ) < rotationCos z / Real.sqrt 2 ∧
    z < rotationSin z / Real.sqrt 2
  exact ⟨by linarith, by linarith, hdivc, hdivsin⟩

end ResearchMain.AHOConstants
