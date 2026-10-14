import R34.ChargeSites
import R34.ExpandedWords
import R34.SchurIsing

open scoped BigOperators

namespace R34.NormalizedWords

noncomputable section

open ChargeSites ExpandedWords Transfer

abbrev Atom := ExpandedWords.Atom ChargedSite

def residualValue (initial : List Atom) (word : List ℕ) : Poly :=
  Transfer.value (initial.map (atomMatrix ChargedSite.matrix) ++
    word.map normalizedMatrix)

theorem residual_cons (initial : List Atom) (j : ℕ) (word : List ℕ) :
    residualValue initial (j :: word) =
      Transfer.value (initial.map (atomMatrix ChargedSite.matrix) ++
        [normalizedMatrix j] ++ word.map normalizedMatrix) := by
  simp [residualValue, List.append_assoc]

theorem residual_append (initial : List Atom) (a : Atom) (word : List ℕ) :
    residualValue (initial ++ [a]) word =
      Transfer.value (initial.map (atomMatrix ChargedSite.matrix) ++
        [atomMatrix ChargedSite.matrix a] ++ word.map normalizedMatrix) := by
  simp [residualValue, List.map_append, List.append_assoc]

theorem neutral_matrix : normalizedMatrix 1 = (1 : Mat) := by
  apply Matrix.ext
  intro i j
  fin_cases i <;> fin_cases j <;>
    simp [normalizedMatrix, normalizedWeight ]

/-- The three-leaf split reduces every normalized word to charged words and C/B gaps. -/
theorem normalized_schur_of_expanded
    (h : ∀ word : List Atom,
      SchurPositive (Transfer.value (word.map (atomMatrix ChargedSite.matrix))))
    (word : List ℕ) : SchurPositive (normalizedModel word) := by
  have hres : ∀ word : List ℕ, ∀ initial : List Atom,
      SchurPositive (residualValue initial word) := by
    intro word
    induction word with
    | nil =>
      intro initial
      simpa [residualValue] using h initial
    | cons j word ih =>
      intro initial
      rw [residual_cons]
      cases j with
      | zero =>
        have hi := ih (initial ++ [Sum.inr ChargedSite.point])
        rw [residual_append] at hi
        simpa [atomMatrix, ChargedSite.matrix] using hi
      | succ j =>
        cases j with
        | zero =>
          have hi := ih (initial ++ [Sum.inl false])
          rw [residual_append] at hi
          simpa [atomMatrix, neutralMatrix, neutral_matrix] using hi
        | succ j =>
          cases j with
          | zero =>
            have hi := ih (initial ++ [Sum.inr (ChargedSite.group 0)])
            rw [residual_append] at hi
            simpa [atomMatrix, ChargedSite.matrix] using hi
          | succ j =>
            cases j with
            | zero =>
              rw [three_site_contraction, value_scale_site, value_add_site,
                value_scale_site]
              apply schurPositive_scale (1 / 2 : ℝ) (by norm_num)
              apply schurPositive_add
              · have hi := ih (initial ++ [Sum.inr (ChargedSite.group 1)])
                rw [residual_append] at hi
                simpa [atomMatrix, ChargedSite.matrix] using hi
              · apply schurPositive_mul
                · exact schurPositive_V
                · have hi := ih (initial ++ [Sum.inl true])
                  rw [residual_append] at hi
                  simpa [atomMatrix, neutralMatrix] using hi
            | succ j =>
              have hi := ih (initial ++ [Sum.inr (ChargedSite.group (j + 2))])
              rw [residual_append] at hi
              have hn : j + 2 ≠ 1 := by omega
              simpa [atomMatrix, ChargedSite.matrix, hn, Nat.add_assoc] using hi
  simpa [normalizedModel, residualValue] using hres word []

end

end R34.NormalizedWords

