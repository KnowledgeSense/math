import MainTheorems.DiagonalSchatten.FaceEuler

namespace ResearchMain.DiagonalSchatten

noncomputable section

open scoped BigOperators Matrix.Norms.Elementwise

variable {J : Type*} [Fintype J]

local instance : DecidableEq J := Classical.decEq J
local instance (X : Matrix (Fin 2) J ℝ) : DecidableEq (FaceIndex X) := Classical.decEq _

theorem faceRows_coordinateCurve (X : Matrix (Fin 2) J ℝ) (hX : ∀ i j, 0 ≤ X i j)
    (i : Fin 2) (j : J) (hp : 0 < X i j) (t : ℝ) (k : Fin 2) (l : J) :
    faceRows X (facePoint X + t • Pi.single ⟨(i, j), hp⟩ 1) k l =
      X k l + t * (if k = i then if l = j then 1 else 0 else 0) := by
  have he : faceRows X (facePoint X + t • Pi.single ⟨(i, j), hp⟩ 1) =
      faceRows X (facePoint X) + t • faceRows X (Pi.single ⟨(i, j), hp⟩ 1) := by
    change faceEmbedding X (facePoint X + t • Pi.single ⟨(i, j), hp⟩ 1) =
      faceEmbedding X (facePoint X) + t • faceEmbedding X (Pi.single ⟨(i, j), hp⟩ 1)
    rw [map_add, map_smul]
  rw [he, faceRows_point X hX]
  simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, faceRows_single]

theorem faceObjective_coordinateCurve (X : Matrix (Fin 2) J ℝ) (hX : ∀ i j, 0 ≤ X i j)
    (h : (Fin 2 → ℝ) → ℝ) (i : Fin 2) (j : J) (hp : 0 < X i j) (t : ℝ) :
    faceObjective h X (facePoint X + t • Pi.single ⟨(i, j), hp⟩ 1) =
      faceObjective h X (facePoint X) + h ((fun k => X k j) + t • Pi.single i 1) -
        h (fun k => X k j) := by
  have he (l : J) : h (fun k => faceRows X (facePoint X + t • Pi.single ⟨(i, j), hp⟩ 1) k l) =
      h (fun k => X k l) + if l = j then
        h ((fun k => X k j) + t • Pi.single i 1) - h (fun k => X k j) else 0 := by
    by_cases hl : l = j
    · subst l
      have hc : (fun k => faceRows X (facePoint X + t • Pi.single ⟨(i, j), hp⟩ 1) k j) =
          (fun k => X k j) + t • Pi.single i 1 := by
        funext k
        simp [faceRows_coordinateCurve X hX, Pi.single_apply, eq_comm]
      rw [hc]
      simp
    · have hc : (fun k => faceRows X (facePoint X + t • Pi.single ⟨(i, j), hp⟩ 1) k l) =
          (fun k => X k l) := by
        funext k
        simp [faceRows_coordinateCurve X hX, hl]
      rw [hc]
      simp [hl]
  unfold faceObjective columnObjective
  simp_rw [he]
  rw [Finset.sum_add_distrib]
  simp only [Finset.sum_ite_eq', Finset.mem_univ, ite_true, faceRows_point X hX]
  ring

theorem faceObjective_partial (X : Matrix (Fin 2) J ℝ) (hX : ∀ i j, 0 ≤ X i j)
    {h : (Fin 2 → ℝ) → ℝ} (i : Fin 2) (j : J) (hp : 0 < X i j)
    (hΦ : DifferentiableAt ℝ (faceObjective h X) (facePoint X))
    (hh : DifferentiableAt ℝ h (fun k => X k j)) :
    fderiv ℝ (faceObjective h X) (facePoint X) (Pi.single ⟨(i, j), hp⟩ 1) =
      fderiv ℝ h (fun k => X k j) (Pi.single i 1) := by
  have hc : HasDerivAt (fun t : ℝ => faceObjective h X
      (facePoint X + t • Pi.single ⟨(i, j), hp⟩ 1))
      (fderiv ℝ (faceObjective h X) (facePoint X) (Pi.single ⟨(i, j), hp⟩ 1)) 0 := by
    convert! hΦ.hasFDerivAt.comp_hasDerivAt_of_eq 0
      ((hasDerivAt_const (0 : ℝ) (facePoint X)).add
        ((hasDerivAt_id (0 : ℝ)).smul_const (Pi.single ⟨(i, j), hp⟩ 1))) (by simp) using 1
    simp
  have hs : HasDerivAt (fun t : ℝ => h ((fun k => X k j) + t • Pi.single i 1))
      (fderiv ℝ h (fun k => X k j) (Pi.single i 1)) 0 := by
    convert! hh.hasFDerivAt.comp_hasDerivAt_of_eq 0
      ((hasDerivAt_const (0 : ℝ) (fun k => X k j)).add
        ((hasDerivAt_id (0 : ℝ)).smul_const (Pi.single i 1))) (by simp) using 1
    simp
  have hr : HasDerivAt (fun t : ℝ => faceObjective h X (facePoint X) +
      h ((fun k => X k j) + t • Pi.single i 1) - h (fun k => X k j))
      (fderiv ℝ h (fun k => X k j) (Pi.single i 1)) 0 := by
    convert! ((hasDerivAt_const (0 : ℝ) (faceObjective h X (facePoint X))).add hs).sub_const
      (h (fun k => X k j)) using 1
    simp
  have heq : (fun t : ℝ => faceObjective h X (facePoint X + t • Pi.single ⟨(i, j), hp⟩ 1)) =
      (fun t => faceObjective h X (facePoint X) + h ((fun k => X k j) + t • Pi.single i 1) -
        h (fun k => X k j)) := funext (faceObjective_coordinateCurve X hX h i j hp)
  rw [heq] at hc
  exact hc.unique hr

theorem faceObjective_second_contact (X : Matrix (Fin 2) J ℝ) (hX : ∀ i j, 0 ≤ X i j)
    {h : (Fin 2 → ℝ) → ℝ} (j : J) (hp : 0 < X 1 j)
    (hΦ : DifferentiableAt ℝ (faceObjective h X) (facePoint X))
    (hh : DifferentiableAt ℝ h (fun k => X k j)) (q : Fin 3 → ℝ)
    (hs : fderiv ℝ (faceObjective h X) (facePoint X) =
      ∑ i, q i • fderiv ℝ (faceGram X i) (facePoint X)) :
    fderiv ℝ h (fun k => X k j) (Pi.single 1 1) = 2 * q 1 * X 1 j + q 2 * X 0 j := by
  have he := congrArg (fun L : (FaceIndex X → ℝ) →L[ℝ] ℝ => L (Pi.single ⟨(1, j), hp⟩ 1)) hs
  simp only [Fin.sum_univ_three, add_apply, smul_apply,
    smul_eq_mul] at he
  rw [faceObjective_partial X hX 1 j hp hΦ hh] at he
  have hg := faceGram_second_coordinate X hX j hp
  have h0 := congrArg Prod.fst hg
  have h1 := congrArg (fun p => p.2.1) hg
  have h2 := congrArg (fun p => p.2.2) hg
  dsimp only at h0 h1 h2
  rw [h0, h1, h2] at he
  nlinarith

end

end ResearchMain.DiagonalSchatten
