import HankelAutomaticity.DeterminantRecurrences

noncomputable section
namespace HankelAutomaticity
open Matrix

@[simp] theorem digitSum_two : digitSum 2=1 := by decide
@[simp] theorem digitSum_three : digitSum 3=2 := by decide
@[simp] theorem digitSum_four : digitSum 4=1 := by decide
@[simp] theorem digitSum_five : digitSum 5=2 := by decide
@[simp] theorem digitSum_six : digitSum 6=2 := by decide

 theorem perturbed_two (x z : ℚ) : perturbed 0 2 x z= -1+z*(x-2) := by
  rw [perturbed, Matrix.det_fin_two]
  norm_num [hankelMatrix, weightedMoment]
  ring

 theorem perturbed_three (x z : ℚ) : perturbed 1 3 x z=3-x+z*(2-x) := by
  rw [perturbed, Matrix.det_fin_three]
  norm_num [hankelMatrix, weightedMoment]
  ring

 theorem perturbed_four (x z : ℚ) :
    perturbed 1 4 x z=(x-2)*(3*x-8)-z*(x-2)^2*(x-4) := by
  rw [perturbed, Matrix.det_succ_row_zero]
  simp only [Fin.sum_univ_succ, Matrix.det_fin_three]
  norm_num [hankelMatrix, weightedMoment, Matrix.submatrix, Fin.succAbove, Fin.insertNth]
  ring

 theorem pair_two (x : ℚ) : hankel 0 2 x= -1 ∧ derivativeCompanion 0 2 x=x-2 := by
  have h0 := perturbed_two x 0
  have h1 := perturbed_two x 1
  simp only [perturbed_affine, zero_mul, add_zero, one_mul] at h0 h1
  constructor
  · exact h0
  · linear_combination h1-h0

 theorem pair_three (x : ℚ) : hankel 1 3 x=3-x ∧ derivativeCompanion 1 3 x=2-x := by
  have h0 := perturbed_three x 0
  have h1 := perturbed_three x 1
  simp only [perturbed_affine, zero_mul, add_zero, one_mul] at h0 h1
  constructor
  · exact h0
  · linear_combination h1-h0

 theorem pair_four (x : ℚ) : hankel 1 4 x=(x-2)*(3*x-8) ∧
    derivativeCompanion 1 4 x= -(x-2)^2*(x-4) := by
  have h0 := perturbed_four x 0
  have h1 := perturbed_four x 1
  simp only [perturbed_affine, zero_mul, add_zero, one_mul, sub_zero] at h0 h1
  constructor
  · exact h0
  · linear_combination h1-h0

end HankelAutomaticity
