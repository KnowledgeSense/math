import MainTheorems.AHOConstants.SpectralPowers
import Mathlib.Analysis.Complex.Exponential
import Mathlib.Analysis.Calculus.ContDiff.Operations

namespace ResearchMain.AHOConstants

open scoped ComplexOrder MatrixOrder

variable {I : Type*} [Fintype I] [DecidableEq I]

noncomputable def complexPower {A : Matrix I I ℂ} (hA : A.PosDef) (z : ℂ) :
    Matrix I I ℂ :=
  Unitary.conjStarAlgAut ℂ (Matrix I I ℂ) hA.isHermitian.eigenvectorUnitary
    (Matrix.diagonal (fun i => Complex.exp ((Real.log (hA.isHermitian.eigenvalues i) : ℂ) * z)))

theorem complexPower_zero {A : Matrix I I ℂ} (hA : A.PosDef) :
    complexPower hA 0 = 1 := by
  simp [complexPower]

theorem complexPower_add {A : Matrix I I ℂ} (hA : A.PosDef) (z w : ℂ) :
    complexPower hA (z + w) = complexPower hA z * complexPower hA w := by
  unfold complexPower
  rw [← map_mul, Matrix.diagonal_mul_diagonal]
  apply congrArg (Unitary.conjStarAlgAut ℂ (Matrix I I ℂ) hA.isHermitian.eigenvectorUnitary)
  apply congrArg Matrix.diagonal
  funext i
  rw [mul_add, Complex.exp_add]

theorem complexPower_real {A : Matrix I I ℂ} (hA : A.PosDef) (r : ℝ) :
    complexPower hA (r : ℂ) = spectralPower A r := by
  change complexPower hA (r : ℂ) = A ^ r
  rw [CFC.rpow_eq_cfc_real hA.posSemidef.nonneg, hA.isHermitian.cfc_eq]
  unfold complexPower Matrix.IsHermitian.cfc
  apply congrArg (Unitary.conjStarAlgAut ℂ (Matrix I I ℂ) hA.isHermitian.eigenvectorUnitary)
  apply congrArg Matrix.diagonal
  funext i
  change Complex.exp ((Real.log (hA.isHermitian.eigenvalues i) : ℂ) * r) =
    ((hA.isHermitian.eigenvalues i ^ r : ℝ) : ℂ)
  rw [Real.rpow_def_of_pos (hA.eigenvalues_pos i)]
  simp only [Complex.ofReal_exp, Complex.ofReal_mul]

theorem complexPower_star {A : Matrix I I ℂ} (hA : A.PosDef) (z : ℂ) :
    star (complexPower hA z) = complexPower hA (star z) := by
  unfold complexPower
  rw [← map_star]
  apply congrArg (Unitary.conjStarAlgAut ℂ (Matrix I I ℂ) hA.isHermitian.eigenvectorUnitary)
  ext i j
  by_cases hij : i = j
  · subst j
    simp only [Matrix.star_eq_conjTranspose, Matrix.conjTranspose_apply,
      Matrix.diagonal_apply_eq]
    simp only [RCLike.star_def]
    rw [← Complex.exp_conj, map_mul, Complex.conj_ofReal]
  · simp [
      Matrix.diagonal_apply_ne _ hij, Matrix.diagonal_apply_ne _ (Ne.symm hij)]

theorem complexPower_imaginary_unitary {A : Matrix I I ℂ} (hA : A.PosDef) (t : ℝ) :
    complexPower hA ((t : ℂ) * Complex.I) ∈ unitary (Matrix I I ℂ) := by
  rw [Unitary.mem_iff, complexPower_star, ← complexPower_add, ← complexPower_add]
  have ht : star ((t : ℂ) * Complex.I) + (t : ℂ) * Complex.I = 0 := by
    simp
  have ht' : (t : ℂ) * Complex.I + star ((t : ℂ) * Complex.I) = 0 := by
    rw [add_comm]
    exact ht
  rw [ht, ht', complexPower_zero]
  exact ⟨rfl, rfl⟩

end ResearchMain.AHOConstants
