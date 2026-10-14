import MainTheorems.PureOSequences.AboveDimensionTwo
import MainTheorems.PureOSequences.TwoVariables

namespace ResearchMain.PureOSequences

theorem type_one_in_dimension_one (P : PureOrderIdeal 1) : typePO P = 1 := by
  classical
  obtain ⟨g, hg⟩ := P.maximal_nonempty
  have hsingleton : maximalMonomials P.ideal = {g} := by
    ext m
    simp only [Finset.mem_singleton]
    constructor
    · intro hm
      have hdeg := P.isPure m g hm hg
      simp only [totalDeg_eq_sum_univ, Fin.sum_univ_one] at hdeg
      apply Finsupp.ext
      intro i
      fin_cases i
      exact hdeg
    · rintro rfl
      exact hg
  simp only [typePO, hsingleton, Finset.card_singleton]

theorem dimension_zero_logConcave (P : PureOrderIdeal 0) :
    IsLogConcaveUpTo (socleDegree P) (pureOSequence P.ideal) := by
  have he : socleDegree P = 0 := by
    simp [socleDegree, totalDeg_eq_sum_univ]
  rw [he]
  intro i hi
  simp at hi

theorem low_dimension_logConcave {r : ℕ} (P : PureOrderIdeal r) (hr : r ≤ 2) :
    IsLogConcaveUpTo (socleDegree P) (pureOSequence P.ideal) := by
  interval_cases r
  · exact dimension_zero_logConcave P
  · exact type_one_logConcave P (type_one_in_dimension_one P)
  · exact two_variable_logConcave P

theorem classification (r t : ℕ) (ht : 1 ≤ t) :
    UniversalLogConcavity r t ↔ r ≤ 2 ∨ t = 1 ∨ (r = 3 ∧ t = 2) := by
  by_cases hr : r ≤ 2
  · constructor
    · intro _
      exact Or.inl hr
    · intro _ P _ _
      exact low_dimension_logConcave P hr
  · rw [classification_above_dimension_two r t (by omega) ht]
    simp only [hr, false_or]

theorem counterexample_classification (r t : ℕ) (ht : 1 ≤ t) :
    (∃ P : PureOrderIdeal r, typePO P = t ∧ UsesEveryVariable P ∧
      ¬ IsLogConcaveUpTo (socleDegree P) (pureOSequence P.ideal)) ↔
      (r = 3 ∧ 3 ≤ t) ∨ (4 ≤ r ∧ 2 ≤ t) := by
  constructor
  · rintro ⟨P, htype, hvars, hbad⟩
    have hfail : ¬ UniversalLogConcavity r t := fun h => hbad (h P htype hvars)
    rw [classification r t ht] at hfail
    omega
  · rintro (⟨rfl, ht'⟩ | ⟨hr, ht'⟩)
    · exact exists_three_variable_counterexample t ht'
    · exact exists_counterexample_above_dimension_three r t hr ht'

theorem three_variable_minimum_failure_type :
    ¬ UniversalLogConcavity 3 3 ∧
      ∀ t : ℕ, 1 ≤ t → t < 3 → UniversalLogConcavity 3 t := by
  constructor
  · rw [classification 3 3 (by omega)]
    omega
  · intro t ht hsmall
    rw [classification 3 t ht]
    omega

theorem higher_minimum_failure_type (r : ℕ) (hr : 4 ≤ r) :
    ¬ UniversalLogConcavity r 2 ∧
      ∀ t : ℕ, 1 ≤ t → t < 2 → UniversalLogConcavity r t := by
  constructor
  · rw [classification r 2 (by omega)]
    omega
  · intro t ht hsmall
    rw [classification r t ht]
    omega

end ResearchMain.PureOSequences
