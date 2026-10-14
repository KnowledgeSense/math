import MainTheorems.DiagonalSchatten.FaceDifferential
import MainTheorems.DiagonalSchatten.GramStationarity

namespace ResearchMain.DiagonalSchatten

noncomputable section

open scoped BigOperators Matrix.Norms.Elementwise

variable {J : Type*} [Fintype J]

local instance : DecidableEq J := Classical.decEq J
local instance (X : Matrix (Fin 2) J ℝ) : DecidableEq (FaceIndex X) := Classical.decEq _

theorem exists_nonparallel_column_of_positive_gramdet (X : Matrix (Fin 2) J ℝ)
    (j : J) (hj : X 0 j ≠ 0)
    (hdet : 0 < gramFirst X * gramSecond X - gramCross X ^ 2) :
    ∃ k, X 0 j * X 1 k - X 1 j * X 0 k ≠ 0 := by
  by_contra h
  push Not at h
  have hr (k : J) : X 1 k = (X 1 j / X 0 j) * X 0 k := by
    field_simp [hj]
    nlinarith [h k]
  have hB : gramSecond X = (X 1 j / X 0 j) ^ 2 * gramFirst X := by
    unfold gramSecond gramFirst
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro k _
    rw [hr k, mul_pow]
  have hC : gramCross X = (X 1 j / X 0 j) * gramFirst X := by
    unfold gramCross gramFirst
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro k _
    rw [hr k]
    ring
  rw [hB, hC] at hdet
  nlinarith

theorem faceGram_dual_first {X : Matrix (Fin 2) J ℝ} (hX : ∀ i j, 0 ≤ X i j)
    {Λ : Fin 3 → ℝ} (hΛ : (∑ i, Λ i • fderiv ℝ (faceGram X i) (facePoint X)) = 0)
    (j : J) (hp : 0 < X 0 j) : 2 * Λ 0 * X 0 j + Λ 2 * X 1 j = 0 := by
  have he := congrArg (fun L : (FaceIndex X → ℝ) →L[ℝ] ℝ =>
    L (Pi.single ⟨(0, j), hp⟩ 1)) hΛ
  simp only [Fin.sum_univ_three, add_apply, smul_apply,
    zero_apply, smul_eq_mul] at he
  have hc := faceGram_first_coordinate X hX j hp
  have h0 := congrArg Prod.fst hc
  have h1 := congrArg (fun p => p.2.1) hc
  have h2 := congrArg (fun p => p.2.2) hc
  dsimp only at h0 h1 h2
  rw [h0, h1, h2] at he
  nlinarith

theorem faceGram_dual_second {X : Matrix (Fin 2) J ℝ} (hX : ∀ i j, 0 ≤ X i j)
    {Λ : Fin 3 → ℝ} (hΛ : (∑ i, Λ i • fderiv ℝ (faceGram X i) (facePoint X)) = 0)
    (j : J) (hp : 0 < X 1 j) : Λ 2 * X 0 j + 2 * Λ 1 * X 1 j = 0 := by
  have he := congrArg (fun L : (FaceIndex X → ℝ) →L[ℝ] ℝ =>
    L (Pi.single ⟨(1, j), hp⟩ 1)) hΛ
  simp only [Fin.sum_univ_three, add_apply, smul_apply,
    zero_apply, smul_eq_mul] at he
  have hc := faceGram_second_coordinate X hX j hp
  have h0 := congrArg Prod.fst hc
  have h1 := congrArg (fun p => p.2.1) hc
  have h2 := congrArg (fun p => p.2.2) hc
  dsimp only at h0 h1 h2
  rw [h0, h1, h2] at he
  nlinarith

theorem faceGram_dual_zero {X : Matrix (Fin 2) J ℝ} (hX : ∀ i j, 0 ≤ X i j)
    {Λ : Fin 3 → ℝ} (hΛ : (∑ i, Λ i • fderiv ℝ (faceGram X i) (facePoint X)) = 0)
    (j k : J) (hj0 : 0 < X 0 j) (hj1 : 0 < X 1 j)
    (hdet : X 0 j * X 1 k - X 1 j * X 0 k ≠ 0) : Λ = 0 := by
  have h0j := faceGram_dual_first hX hΛ j hj0
  have h1j := faceGram_dual_second hX hΛ j hj1
  have hcoeff : Λ 0 = 0 ∧ Λ 1 = 0 ∧ Λ 2 = 0 := by
    by_cases hk0 : 0 < X 0 k
    · exact gramDual_zero_from_nonparallel (Λ 0) (Λ 1) (Λ 2)
        (X 0 j) (X 1 j) (X 0 k) (X 1 k) hj0.ne' hj1.ne' hdet h0j h1j
        (faceGram_dual_first hX hΛ k hk0)
    · have hkz : X 0 k = 0 := le_antisymm (not_lt.mp hk0) (hX 0 k)
      have hk1 : 0 < X 1 k := by
        by_contra h
        have hz : X 1 k = 0 := le_antisymm (not_lt.mp h) (hX 1 k)
        exact hdet (by simp [hkz, hz])
      have haxis : 2 * Λ 1 * X 1 k = 0 := by
        simpa only [hkz, mul_zero, zero_add] using faceGram_dual_second hX hΛ k hk1
      exact gramDual_zero_from_second_axis (Λ 0) (Λ 1) (Λ 2)
        (X 0 j) (X 1 j) (X 1 k) hj0.ne' hk1.ne' h0j h1j haxis
  funext i
  fin_cases i <;> simp [hcoeff.1, hcoeff.2.1, hcoeff.2.2]

theorem faceObjective_multiplier_ne_zero {X : Matrix (Fin 2) J ℝ}
    (hX : ∀ i j, 0 ≤ X i j) (j k : J) (hj0 : 0 < X 0 j) (hj1 : 0 < X 1 j)
    (hdet : X 0 j * X 1 k - X 1 j * X 0 k ≠ 0)
    {Λ : Fin 3 → ℝ} {Λ0 : ℝ} {φ' : (FaceIndex X → ℝ) →L[ℝ] ℝ}
    (hne : (Λ, Λ0) ≠ 0)
    (hs : (∑ i, Λ i • fderiv ℝ (faceGram X i) (facePoint X)) + Λ0 • φ' = 0) :
    Λ0 ≠ 0 := by
  intro hzero
  rw [hzero, zero_smul, add_zero] at hs
  have hz := faceGram_dual_zero hX hs j k hj0 hj1 hdet
  exact hne (by simp [hz, hzero])

theorem faceObjective_normalized_lagrange {a b c : ℝ} {h : (Fin 2 → ℝ) → ℝ}
    {X : Matrix (Fin 2) J ℝ} (hX : X ∈ gramFiber a b c)
    (hmax : ∀ Y ∈ gramFiber (J := J) a b c, columnObjective h Y ≤ columnObjective h X)
    (hd : ContDiffAt ℝ 1 (faceObjective h X) (facePoint X))
    (j k : J) (hj0 : 0 < X 0 j) (hj1 : 0 < X 1 j)
    (hdet : X 0 j * X 1 k - X 1 j * X 0 k ≠ 0) :
    ∃ q : Fin 3 → ℝ, fderiv ℝ (faceObjective h X) (facePoint X) =
      ∑ i, q i • fderiv ℝ (faceGram X i) (facePoint X) := by
  obtain ⟨Λ, Λ0, hne, hs⟩ := faceObjective_lagrange hX hmax hd
  have hΛ0 := faceObjective_multiplier_ne_zero hX.1 j k hj0 hj1 hdet hne hs
  refine ⟨fun i => -Λ i / Λ0, ?_⟩
  ext v
  have he := congrArg (fun L : (FaceIndex X → ℝ) →L[ℝ] ℝ => L v) hs
  simp only [Fin.sum_univ_three, add_apply, smul_apply,
    zero_apply, smul_eq_mul] at he ⊢
  field_simp [hΛ0]
  linarith

end

end ResearchMain.DiagonalSchatten
