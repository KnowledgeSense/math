import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.Algebra.Group.AddChar

namespace ResearchMain.SIBO

variable {K : Type*} [Field K]

/-- A lower triangular kernel with nonzero diagonal cannot factor through fewer columns. -/
theorem triangular_factor_bound {m : ℕ} {I : Type*} [Fintype I]
    (L : Matrix (Fin (m + 1)) I K)
    (R : Matrix I (Fin (m + 1)) K)
    (hupper : ∀ i j, i < j → (L * R) i j = 0)
    (hdiag : ∀ i, (L * R) i i ≠ 0) : m + 1 ≤ Fintype.card I := by
  classical
  have htri : (L * R).IsLowerTriangular := by
    intro i j hij
    exact hupper i j hij
  have hdet : (L * R).det ≠ 0 := by
    rw [Matrix.det_of_isLowerTriangular (L * R) htri]
    exact Finset.prod_ne_zero_iff.mpr (fun i _ => hdiag i)
  calc
    m + 1 = (L * R).rank := by
      simpa using (Matrix.rank_of_det_ne_zero hdet).symm
    _ ≤ L.rank := Matrix.rank_mul_le_left L R
    _ ≤ Fintype.card I := Matrix.rank_le_card_width L

theorem interval_distance_bound {m : ℕ} {I : Type*} [Fintype I]
    (L : Matrix (Fin (m + 1)) I K)
    (R : Matrix I (Fin (m + 1)) K)
    (hupper : ∀ i j, i < j → (L * R) i j = 0)
    (hdiag : ∀ i, (L * R) i i ≠ 0) : m ≤ Fintype.card I - 1 := by
  have h := triangular_factor_bound L R hupper hdiag
  omega

variable {A : Type*} [AddCommGroup A]

def characterKernel {m : ℕ} {I : Type*} [Fintype I]
    (χ : I → AddChar A K) (c : I → K)
    (s : Fin (m + 1) → A) : Matrix (Fin (m + 1)) (Fin (m + 1)) K :=
  fun i j => ∑ t, c t * χ t (s j - s i)

/-- Every finite character sum gives a kernel of rank at most its number of terms. -/
theorem character_interval_bound {m : ℕ} {I : Type*} [Fintype I]
    (χ : I → AddChar A K) (c : I → K) (s : Fin (m + 1) → A)
    (hzero : ∀ i j, i < j → characterKernel χ c s i j = 0)
    (hcoeff : (∑ t, c t) ≠ 0) : m ≤ Fintype.card I - 1 := by
  classical
  let L : Matrix (Fin (m + 1)) I K := fun i t => c t * χ t (-s i)
  let R : Matrix I (Fin (m + 1)) K := fun t j => χ t (s j)
  have hfactor : L * R = characterKernel χ c s := by
    ext i j
    rw [Matrix.mul_apply]
    simp only [L, R, characterKernel, sub_eq_add_neg,
      AddChar.map_add_eq_mul]
    apply Finset.sum_congr rfl
    intro t _
    ring
  apply interval_distance_bound L R
  · simpa only [hfactor] using hzero
  · intro i
    simpa [hfactor, characterKernel] using hcoeff

end ResearchMain.SIBO
