import MainTheorems.PureOSequences.ThreeVariableClassification
import MainTheorems.PureOSequences.HigherCounterexamples

namespace ResearchMain.PureOSequences

theorem classification_above_dimension_two (r t : ℕ) (hr : 3 ≤ r) (ht : 1 ≤ t) :
    UniversalLogConcavity r t ↔ t = 1 ∨ (r = 3 ∧ t = 2) := by
  constructor
  · intro h
    by_cases htype : t = 1
    · exact Or.inl htype
    · by_cases hdim : r = 3
      · subst r
        have ht2 := (three_variable_classification t ht).mp h
        exact Or.inr ⟨rfl, by omega⟩
      · obtain ⟨P, htypeP, hvars, hbad⟩ :=
          exists_counterexample_above_dimension_three r t (by omega) (by omega)
        exact False.elim (hbad (h P htypeP hvars))
  · rintro (rfl | ⟨rfl, rfl⟩) P htype _
    · exact type_one_logConcave P htype
    · exact TypeTwo.type_two_three_variables_logConcave P htype

theorem failure_types_above_dimension_two (r t : ℕ) (hr : 3 ≤ r) (ht : 1 ≤ t) :
    ¬ UniversalLogConcavity r t ↔ (r = 3 ∧ 3 ≤ t) ∨ (4 ≤ r ∧ 2 ≤ t) := by
  rw [classification_above_dimension_two r t hr ht]
  omega

end ResearchMain.PureOSequences
