import MainTheorems.DiagonalSchatten.GramReduction
import MainTheorems.DiagonalSchatten.RayExtremizer
import MainTheorems.DiagonalSchatten.FaceRank

namespace ResearchMain.DiagonalSchatten

noncomputable section

open scoped BigOperators Matrix.Norms.Elementwise

variable {J : Type*} [Fintype J]

theorem exists_interior_column (X : Matrix (Fin 2) J ℝ)
    (hX : ∀ i j, 0 ≤ X i j) (hc : 0 < gramCross X) :
    ∃ j, 0 < X 0 j ∧ 0 < X 1 j := by
  classical
  by_contra hn
  have hz : gramCross X = 0 := by
    unfold gramCross
    apply Finset.sum_eq_zero
    intro j _
    by_cases h0 : 0 < X 0 j
    · have h1 : X 1 j = 0 := by
        apply le_antisymm
        · by_contra h
          exact hn ⟨j, h0, lt_of_not_ge h⟩
        · exact hX 1 j
      simp [h1]
    · have hz : X 0 j = 0 := le_antisymm (not_lt.mp h0) (hX 0 j)
      simp [hz]
  exact hc.ne' hz

namespace RayParameters

variable (g : RayParameters)

theorem stationary_maximum_reduction {a b c : ℝ} (s : ℝ)
    (hne : (gramFiber (J := J) a b c).Nonempty) (hc : 0 < c)
    (hdet : 0 < a * b - c ^ 2)
    (hD : ∀ x, 0 ≤ x 0 → 0 ≤ x 1 → (0 < x 0 ∨ 0 < x 1) → g.denominator x ≠ 0) :
    ∃ X ∈ gramFiber (J := J) a b c,
      (∀ Y ∈ gramFiber (J := J) a b c,
        columnObjective (fun x => s * g.functional x) Y ≤
          columnObjective (fun x => s * g.functional x) X) ∧
      ((raySupportCard X ≤ 2 ∨
        ((interiorSlopes X).card = 1 ∧ firstAxisPresent X ∧ secondAxisPresent X)) ∨
       ∃ T : Matrix (Fin 2) (Fin 2) ℝ,
         (∀ i j, 0 ≤ T i j) ∧ gramFirst T = a ∧ gramSecond T = b ∧ gramCross T = c ∧
         columnObjective (fun x => s * g.functional x) T =
           columnObjective (fun x => s * g.functional x) X) := by
  classical
  obtain ⟨X, hX, hmax⟩ := g.exists_functional_max hne
    (fun x hx => hD x hx.1 hx.2.1 (quarterCircle_has_positive_coordinate hx)) s
  have hcx : 0 < gramCross X := by rw [hX.2.2.2]; exact hc
  have hdx : 0 < gramFirst X * gramSecond X - gramCross X ^ 2 := by
    rw [hX.2.1, hX.2.2.1, hX.2.2.2]
    exact hdet
  obtain ⟨j, hj0, hj1⟩ := exists_interior_column X hX.1 hcx
  obtain ⟨k, hk⟩ := exists_nonparallel_column_of_positive_gramdet X j hj0.ne' hdx
  obtain ⟨q, hs⟩ := faceObjective_normalized_lagrange hX hmax
    (g.signed_faceObjective_contDiffAt X hX.1 hD s) j k hj0 hj1 hk
  refine ⟨X, hX, hmax, ?_⟩
  by_cases hp : g.contactPolynomial s q = 0
  · right
    obtain ⟨T, hT, ha, hb, hcross, he⟩ :=
      g.zero_contactPolynomial_two_column_reduction s q hp hD X hX.1
    exact ⟨T, hT, ha.trans hX.2.1, hb.trans hX.2.2.1,
      hcross.trans hX.2.2.2, he⟩
  · left
    exact g.stationary_support_classification s X hX.1 hD q hs hp

end RayParameters

end

end ResearchMain.DiagonalSchatten
