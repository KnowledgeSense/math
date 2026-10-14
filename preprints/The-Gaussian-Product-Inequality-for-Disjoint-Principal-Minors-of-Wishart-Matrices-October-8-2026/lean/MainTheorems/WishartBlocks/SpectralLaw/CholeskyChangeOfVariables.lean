import MainTheorems.WishartBlocks.SpectralLaw.CholeskyUniqueness
import Mathlib.MeasureTheory.Function.Jacobian
import Mathlib.LinearAlgebra.Determinant

namespace ResearchMain.WishartBlocks

open MeasureTheory
open scoped BigOperators

def positiveLowerCoordinates (n : ℕ) : Set (LowerIndex n → ℝ) :=
  {x | ∀ i : Fin n, 0 < lowerMatrix x i i}

def positiveSymmetricCoordinates (n : ℕ) : Set (LowerIndex n → ℝ) :=
  {x | (symmetricMatrix x).PosDef}

theorem measurableSet_positiveLowerCoordinates (n : ℕ) :
    MeasurableSet (positiveLowerCoordinates n) := by
  have he : positiveLowerCoordinates n =
      ⋂ i : Fin n, {x : LowerIndex n → ℝ | 0 < lowerEntry i i x} := by
    ext x
    simp only [positiveLowerCoordinates, Set.mem_ofPred_eq, Set.mem_iInter, lowerMatrix]
  rw [he]
  exact MeasurableSet.iInter fun i =>
    (isOpen_lt continuous_const (lowerEntry i i).continuous).measurableSet

theorem lowerGram_posDef {n : ℕ} {x : LowerIndex n → ℝ}
    (hx : x ∈ positiveLowerCoordinates n) :
    (lowerMatrix x * (lowerMatrix x).transpose).PosDef := by
  have hd : 0 < (lowerMatrix x).det := by
    rw [Matrix.det_of_isLowerTriangular _ (lowerMatrix_lowerTriangular x)]
    exact Finset.prod_pos fun i _ => hx i
  have hu : IsUnit (lowerMatrix x) := (Matrix.isUnit_iff_isUnit_det _).mpr
    (isUnit_iff_ne_zero.mpr hd.ne')
  simpa only [Matrix.conjTranspose_eq_transpose_of_trivial] using
    Matrix.PosDef.mul_conjTranspose_self (lowerMatrix x)
      (Matrix.vecMul_injective_of_isUnit hu)

theorem choleskyCoordinates_image_positive (n : ℕ) :
    choleskyCoordinates '' positiveLowerCoordinates n = positiveSymmetricCoordinates n := by
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    rw [positiveSymmetricCoordinates, Set.mem_ofPred_eq, symmetricMatrix_choleskyCoordinates]
    exact lowerGram_posDef hx
  · intro hy
    obtain ⟨x, hx, hxy⟩ := choleskyCoordinates_surjective_positive y hy
    exact ⟨x, hx, hxy⟩

noncomputable def choleskyJacobianWeight {n : ℕ} (x : LowerIndex n → ℝ) : ℝ :=
  ∏ e : LowerIndex n,
    if e.val.1 = e.val.2 then 2 * lowerMatrix x e.val.2 e.val.2
      else lowerMatrix x e.val.2 e.val.2

theorem choleskyDerivative_det_eq_weight {n : ℕ} (x : LowerIndex n → ℝ) :
    (choleskyDerivative x).det = choleskyJacobianWeight x := by
  change LinearMap.det (choleskyDerivative x).toLinearMap = _
  rw [← LinearMap.det_toMatrix', choleskyDerivative_det]
  rfl

theorem choleskyJacobianWeight_pos {n : ℕ} {x : LowerIndex n → ℝ}
    (hx : x ∈ positiveLowerCoordinates n) : 0 < choleskyJacobianWeight x := by
  unfold choleskyJacobianWeight
  apply Finset.prod_pos
  intro e _
  split_ifs
  · exact mul_pos (by norm_num) (hx e.val.2)
  · exact hx e.val.2

theorem cholesky_integral_changeOfVariables {n : ℕ}
    (g : (LowerIndex n → ℝ) → ℝ) :
    (∫ y in positiveSymmetricCoordinates n, g y) =
      ∫ x in positiveLowerCoordinates n, choleskyJacobianWeight x * g (choleskyCoordinates x) := by
  rw [← choleskyCoordinates_image_positive]
  rw [integral_image_eq_integral_abs_det_fderiv_smul volume
    (measurableSet_positiveLowerCoordinates n)
    (fun x _ => (choleskyCoordinates_hasFDerivAt x).hasFDerivWithinAt)
    choleskyCoordinates_injOn_positive]
  apply setIntegral_congr_fun (measurableSet_positiveLowerCoordinates n)
  intro x hx
  change |(choleskyDerivative x).det| * g (choleskyCoordinates x) =
    choleskyJacobianWeight x * g (choleskyCoordinates x)
  rw [choleskyDerivative_det_eq_weight, abs_of_pos (choleskyJacobianWeight_pos hx)]

end ResearchMain.WishartBlocks
