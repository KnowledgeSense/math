import MainTheorems.DiagonalSchatten.FaceRank
import MainTheorems.DiagonalSchatten.HomogeneousEuler

namespace ResearchMain.DiagonalSchatten

noncomputable section

open scoped BigOperators Matrix.Norms.Elementwise

variable {J : Type*} [Fintype J]

local instance : DecidableEq J := Classical.decEq J

def faceColumnDirection (X : Matrix (Fin 2) J ℝ) (j : J) : FaceIndex X → ℝ :=
  fun e => if e.1.2 = j then X e.1.1 e.1.2 else 0

omit [Fintype J] in
theorem faceRows_columnDirection (X : Matrix (Fin 2) J ℝ) (hX : ∀ i j, 0 ≤ X i j)
    (j : J) (i : Fin 2) (k : J) :
    faceRows X (faceColumnDirection X j) i k = if k = j then X i k else 0 := by
  classical
  by_cases hp : 0 < X i k
  · simp [faceRows, faceColumnDirection, hp]
  · have hz : X i k = 0 := le_antisymm (not_lt.mp hp) (hX i k)
    simp [faceRows, hz]

theorem faceRows_columnCurve (X : Matrix (Fin 2) J ℝ) (hX : ∀ i j, 0 ≤ X i j)
    (j : J) (t : ℝ) (i : Fin 2) (k : J) :
    faceRows X (facePoint X + t • faceColumnDirection X j) i k =
      if k = j then (1 + t) * X i k else X i k := by
  have he : faceRows X (facePoint X + t • faceColumnDirection X j) =
      faceRows X (facePoint X) + t • faceRows X (faceColumnDirection X j) := by
    change faceEmbedding X (facePoint X + t • faceColumnDirection X j) =
      faceEmbedding X (facePoint X) + t • faceEmbedding X (faceColumnDirection X j)
    rw [map_add, map_smul]
  rw [he, faceRows_point X hX]
  simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, faceRows_columnDirection X hX]
  by_cases hk : k = j
  · simp only [hk, ite_true]
    ring
  · simp [hk]

theorem faceGram_columnDirection (X : Matrix (Fin 2) J ℝ) (hX : ∀ i j, 0 ≤ X i j)
    (j : J) :
    (fderiv ℝ (faceGram X 0) (facePoint X) (faceColumnDirection X j),
      fderiv ℝ (faceGram X 1) (facePoint X) (faceColumnDirection X j),
      fderiv ℝ (faceGram X 2) (facePoint X) (faceColumnDirection X j)) =
        (2 * X 0 j ^ 2, 2 * X 1 j ^ 2, 2 * X 0 j * X 1 j) := by
  rw [fderiv_faceGram_first X hX, fderiv_faceGram_second X hX, fderiv_faceGram_cross X hX]
  simp [faceRows_columnDirection X hX, pow_two, mul_comm, mul_assoc,
    Finset.sum_add_distrib]
  ring

theorem faceObjective_columnCurve (X : Matrix (Fin 2) J ℝ) (hX : ∀ i j, 0 ≤ X i j)
    {h : (Fin 2 → ℝ) → ℝ}
    (hh : ∀ (x : Fin 2 → ℝ) (t : ℝ), h (t • x) = t ^ 2 * h x) (j : J) (t : ℝ) :
    faceObjective h X (facePoint X + t • faceColumnDirection X j) =
      faceObjective h X (facePoint X) + ((1 + t) ^ 2 - 1) * h (fun i => X i j) := by
  have he (k : J) : h (fun i => faceRows X (facePoint X + t • faceColumnDirection X j) i k) =
      h (fun i => X i k) + if k = j then ((1 + t) ^ 2 - 1) * h (fun i => X i j) else 0 := by
    by_cases hk : k = j
    · subst k
      have hc : (fun i => faceRows X (facePoint X + t • faceColumnDirection X j) i j) =
          (1 + t) • (fun i => X i j) := by
        funext i
        simp [faceRows_columnCurve X hX]
      rw [hc, hh]
      simp only [ite_true]
      ring
    · have hc : (fun i => faceRows X (facePoint X + t • faceColumnDirection X j) i k) =
          (fun i => X i k) := by
        funext i
        simp [faceRows_columnCurve X hX, hk]
      rw [hc]
      simp [hk]
  unfold faceObjective columnObjective
  simp_rw [he]
  rw [Finset.sum_add_distrib]
  simp only [Finset.sum_ite_eq', Finset.mem_univ, ite_true, faceRows_point X hX]

theorem faceObjective_columnEuler (X : Matrix (Fin 2) J ℝ) (hX : ∀ i j, 0 ≤ X i j)
    {h : (Fin 2 → ℝ) → ℝ}
    (hh : ∀ (x : Fin 2 → ℝ) (t : ℝ), h (t • x) = t ^ 2 * h x)
    (hd : DifferentiableAt ℝ (faceObjective h X) (facePoint X)) (j : J) :
    fderiv ℝ (faceObjective h X) (facePoint X) (faceColumnDirection X j) =
      2 * h (fun i => X i j) := by
  have hc : HasDerivAt (fun t : ℝ => faceObjective h X
      (facePoint X + t • faceColumnDirection X j))
      (fderiv ℝ (faceObjective h X) (facePoint X) (faceColumnDirection X j)) 0 := by
    convert! hd.hasFDerivAt.comp_hasDerivAt_of_eq 0
      ((hasDerivAt_const (0 : ℝ) (facePoint X)).add
        ((hasDerivAt_id (0 : ℝ)).smul_const (faceColumnDirection X j))) (by simp) using 1
    simp
  have hp : HasDerivAt (fun t : ℝ => faceObjective h X (facePoint X) +
      ((1 + t) ^ 2 - 1) * h (fun i => X i j)) (2 * h (fun i => X i j)) 0 := by
    convert! (hasDerivAt_const (0 : ℝ) (faceObjective h X (facePoint X))).add
      (((((hasDerivAt_const (0 : ℝ) (1 : ℝ)).add (hasDerivAt_id (0 : ℝ))).fun_pow 2).sub_const 1).mul_const
        (h (fun i => X i j))) using 1
    simp
  have heq : (fun t : ℝ => faceObjective h X (facePoint X + t • faceColumnDirection X j)) =
      (fun t => faceObjective h X (facePoint X) + ((1 + t) ^ 2 - 1) * h (fun i => X i j)) :=
    funext (faceObjective_columnCurve X hX hh j)
  rw [heq] at hc
  exact hc.unique hp

theorem faceObjective_value_contact (X : Matrix (Fin 2) J ℝ) (hX : ∀ i j, 0 ≤ X i j)
    {h : (Fin 2 → ℝ) → ℝ}
    (hh : ∀ (x : Fin 2 → ℝ) (t : ℝ), h (t • x) = t ^ 2 * h x)
    (hd : DifferentiableAt ℝ (faceObjective h X) (facePoint X))
    (q : Fin 3 → ℝ)
    (hs : fderiv ℝ (faceObjective h X) (facePoint X) =
      ∑ i, q i • fderiv ℝ (faceGram X i) (facePoint X)) (j : J) :
    h (fun i => X i j) = q 0 * X 0 j ^ 2 + q 1 * X 1 j ^ 2 + q 2 * X 0 j * X 1 j := by
  have he := congrArg (fun L : (FaceIndex X → ℝ) →L[ℝ] ℝ => L (faceColumnDirection X j)) hs
  simp only [Fin.sum_univ_three, add_apply,
    smul_apply, smul_eq_mul] at he
  rw [faceObjective_columnEuler X hX hh hd j] at he
  have hg := faceGram_columnDirection X hX j
  have h0 := congrArg Prod.fst hg
  have h1 := congrArg (fun p => p.2.1) hg
  have h2 := congrArg (fun p => p.2.2) hg
  dsimp only at h0 h1 h2
  rw [h0, h1, h2] at he
  nlinarith

end

end ResearchMain.DiagonalSchatten
