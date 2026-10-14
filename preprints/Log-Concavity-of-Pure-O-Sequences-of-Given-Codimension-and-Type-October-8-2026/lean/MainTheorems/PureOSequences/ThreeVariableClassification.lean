import MainTheorems.PureOSequences.Counterexamples
import MainTheorems.PureOSequences.TypeTwo

namespace ResearchMain.PureOSequences

theorem three_variable_classification (t : ℕ) (ht : 1 ≤ t) :
    UniversalLogConcavity 3 t ↔ t ≤ 2 := by
  constructor
  · intro h
    by_contra hlarge
    obtain ⟨P, htype, hvars, hbad⟩ := exists_three_variable_counterexample t (by omega)
    exact hbad (h P htype hvars)
  · intro hsmall P htype _
    have hcases : t = 1 ∨ t = 2 := by omega
    rcases hcases with rfl | rfl
    · exact type_one_logConcave P htype
    · exact TypeTwo.type_two_three_variables_logConcave P htype

theorem three_variable_failure_types (t : ℕ) (ht : 1 ≤ t) :
    ¬ UniversalLogConcavity 3 t ↔ 3 ≤ t := by
  rw [three_variable_classification t ht]
  omega

end ResearchMain.PureOSequences
