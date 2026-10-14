import MainTheorems.DiagonalSchatten.FaceExtremizer
import MainTheorems.DiagonalSchatten.GramDifferential
import Mathlib.Topology.Algebra.Module.FiniteDimension

namespace ResearchMain.DiagonalSchatten

noncomputable section

open scoped BigOperators Matrix.Norms.Elementwise

variable {J : Type*} [Fintype J]

local instance : DecidableEq J := Classical.decEq J
local instance (X : Matrix (Fin 2) J ℝ) : DecidableEq (FaceIndex X) := Classical.decEq _

def faceEmbedding (X : Matrix (Fin 2) J ℝ) :
    (FaceIndex X → ℝ) →L[ℝ] Matrix (Fin 2) J ℝ :=
  LinearMap.toContinuousLinearMap {
    toFun := faceRows X
    map_add' := by
      classical
      intro v w
      ext i j
      simp only [faceRows, Matrix.of_apply]
      split_ifs with h <;> simp [h]
    map_smul' := by
      classical
      intro t v
      ext i j
      simp only [faceRows, Matrix.of_apply]
      split_ifs with h <;> simp [h]
  }

theorem fderiv_face_comp (X : Matrix (Fin 2) J ℝ)
    (f : Matrix (Fin 2) J ℝ → ℝ) (v w : FaceIndex X → ℝ)
    (hf : DifferentiableAt ℝ f (faceRows X v)) :
    fderiv ℝ (fun q => f (faceRows X q)) v w =
      fderiv ℝ f (faceRows X v) (faceRows X w) := by
  have hd : HasFDerivAt (fun q => f (faceRows X q))
      ((fderiv ℝ f (faceRows X v)).comp (faceEmbedding X)) v := by
    convert! hf.hasFDerivAt.comp v (faceEmbedding X).hasFDerivAt using 1
  rw [hd.fderiv]
  rfl

theorem fderiv_faceGram_first (X : Matrix (Fin 2) J ℝ) (hX : ∀ i j, 0 ≤ X i j)
    (v : FaceIndex X → ℝ) :
    fderiv ℝ (faceGram X 0) (facePoint X) v = 2 * ∑ j, X 0 j * faceRows X v 0 j := by
  change fderiv ℝ (fun q => gramFirst (faceRows X q)) (facePoint X) v = _
  rw [fderiv_face_comp X gramFirst _ v (by unfold gramFirst; fun_prop),
    faceRows_point X hX, fderiv_gramFirst]

theorem fderiv_faceGram_second (X : Matrix (Fin 2) J ℝ) (hX : ∀ i j, 0 ≤ X i j)
    (v : FaceIndex X → ℝ) :
    fderiv ℝ (faceGram X 1) (facePoint X) v = 2 * ∑ j, X 1 j * faceRows X v 1 j := by
  change fderiv ℝ (fun q => gramSecond (faceRows X q)) (facePoint X) v = _
  rw [fderiv_face_comp X gramSecond _ v (by unfold gramSecond; fun_prop),
    faceRows_point X hX, fderiv_gramSecond]

theorem fderiv_faceGram_cross (X : Matrix (Fin 2) J ℝ) (hX : ∀ i j, 0 ≤ X i j)
    (v : FaceIndex X → ℝ) :
    fderiv ℝ (faceGram X 2) (facePoint X) v =
      ∑ j, (faceRows X v 0 j * X 1 j + X 0 j * faceRows X v 1 j) := by
  change fderiv ℝ (fun q => gramCross (faceRows X q)) (facePoint X) v = _
  rw [fderiv_face_comp X gramCross _ v (by unfold gramCross; fun_prop),
    faceRows_point X hX, fderiv_gramCross]

omit [Fintype J] in
theorem faceRows_single (X : Matrix (Fin 2) J ℝ) (i : Fin 2) (j : J) (hp : 0 < X i j)
    (k : Fin 2) (l : J) :
    faceRows X (Pi.single ⟨(i, j), hp⟩ 1) k l = if k = i then if l = j then 1 else 0 else 0 := by
  classical
  by_cases h : 0 < X k l
  · by_cases hk : k = i <;> by_cases hl : l = j <;>
      simp_all [faceRows, Pi.single_apply, Subtype.ext_iff, Prod.ext_iff, eq_comm]
    all_goals aesop
  · have hne : ¬(k = i ∧ l = j) := by
      rintro ⟨rfl, rfl⟩
      exact h hp
    simp [faceRows, h]
    by_cases hk : k = i
    · have hl : l ≠ j := fun hl => hne ⟨hk, hl⟩
      simp [hk, hl]
    · simp [hk]

theorem faceGram_first_coordinate (X : Matrix (Fin 2) J ℝ) (hX : ∀ i j, 0 ≤ X i j)
    (j : J) (hp : 0 < X 0 j) :
    (fderiv ℝ (faceGram X 0) (facePoint X) (Pi.single ⟨(0, j), hp⟩ 1),
      fderiv ℝ (faceGram X 1) (facePoint X) (Pi.single ⟨(0, j), hp⟩ 1),
      fderiv ℝ (faceGram X 2) (facePoint X) (Pi.single ⟨(0, j), hp⟩ 1)) =
        (2 * X 0 j, 0, X 1 j) := by
  classical
  rw [fderiv_faceGram_first X hX, fderiv_faceGram_second X hX, fderiv_faceGram_cross X hX]
  simp [faceRows_single]

theorem faceGram_second_coordinate (X : Matrix (Fin 2) J ℝ) (hX : ∀ i j, 0 ≤ X i j)
    (j : J) (hp : 0 < X 1 j) :
    (fderiv ℝ (faceGram X 0) (facePoint X) (Pi.single ⟨(1, j), hp⟩ 1),
      fderiv ℝ (faceGram X 1) (facePoint X) (Pi.single ⟨(1, j), hp⟩ 1),
      fderiv ℝ (faceGram X 2) (facePoint X) (Pi.single ⟨(1, j), hp⟩ 1)) =
        (0, 2 * X 1 j, X 0 j) := by
  classical
  rw [fderiv_faceGram_first X hX, fderiv_faceGram_second X hX, fderiv_faceGram_cross X hX]
  simp [faceRows_single]

end

end ResearchMain.DiagonalSchatten
