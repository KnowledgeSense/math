import MainTheorems.PureOSequences.ThreeGenerators
import MainTheorems.PureOSequences.FourGenerators
import MainTheorems.PureOSequences.FatString

namespace ResearchMain.PureOSequences

theorem exists_three_variable_counterexample (t : ℕ) (ht : 3 ≤ t) :
    ∃ P : PureOrderIdeal 3, typePO P = t ∧ UsesEveryVariable P ∧
      ¬ IsLogConcaveUpTo (socleDegree P) (pureOSequence P.ideal) := by
  by_cases hlarge : 5 ≤ t
  · exact exists_large_type_counterexample t hlarge
  · have hsmall : t = 3 ∨ t = 4 := by omega
    rcases hsmall with rfl | rfl
    · exact exists_type_three_counterexample
    · exact exists_type_four_counterexample

end ResearchMain.PureOSequences
