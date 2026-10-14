import MainTheorems.AHOConstants.TwoDimensionBound
import MainTheorems.AHOConstants.OneDimension
import MainTheorems.AHOConstants.DimensionPadding
import MainTheorems.AHOConstants.IntervalCriterion

namespace ResearchMain.AHOConstants

open scoped ENNReal

attribute [local instance] Classical.propDecidable

theorem optimalConstant_classification {w : TraceWord} (hw : WordNonnegative w)
    (hAmass : exponentMass true w = 1) (hBmass : exponentMass false w = 1)
    (n : ℕ) (hn : 0 < n) :
    optimalConstant n w = if n ≤ 2 ∨ FeasibleWord w then 1 else ∞ := by
  classical
  by_cases hsmall : n ≤ 2
  · rw [ite_eq_left (Or.inl hsmall)]
    have hcases : n = 1 ∨ n = 2 := by omega
    rcases hcases with rfl | rfl
    · exact optimalConstant_one_dimension hw hAmass hBmass
    · exact optimalConstant_two_dimension hw hAmass hBmass
  · by_cases hfeasible : FeasibleWord w
    · rw [ite_eq_left (Or.inr hfeasible)]
      exact optimalConstant_eq_one_of_feasibleWord n hn hfeasible
    · rw [ite_eq_right (not_or.mpr ⟨hsmall, hfeasible⟩)]
      exact optimalConstant_infinite_of_infeasibleWord hw hAmass hBmass hfeasible n (by omega)

theorem optimalConstant_eq_one_iff {w : TraceWord} (hw : WordNonnegative w)
    (hAmass : exponentMass true w = 1) (hBmass : exponentMass false w = 1)
    (n : ℕ) (hn : 3 ≤ n) :
    optimalConstant n w = 1 ↔ FeasibleWord w := by
  rw [optimalConstant_classification hw hAmass hBmass n (by omega)]
  have hn' : ¬n ≤ 2 := by omega
  simp [hn']

theorem ExponentData.feasible_iff_interval (d : ExponentData) :
    d.feasible ↔ ∀ i j, lowerEndpoint d.p d.q i ≤ upperEndpoint d.p d.q j := by
  exact feasible_iff_interval_pairs d.p d.q (d.p_total.trans d.q_total.symm)

theorem optimalConstant_reduced_classification {w : TraceWord} (hw : WordNonnegative w)
    (d : ExponentData) (hred : WordReduction w d.word) (n : ℕ) (hn : 3 ≤ n) :
    optimalConstant n w = if d.feasible then 1 else ∞ := by
  classical
  by_cases hf : d.feasible
  · rw [ite_eq_left hf]
    exact optimalConstant_eq_one_of_feasibleWord n (by omega) ⟨d, hred, hf⟩
  · rw [ite_eq_right hf]
    have hAmass : exponentMass true w = 1 := by
      rw [hred.mass true, ExponentData.word, pairWord_mass_true, List.map_ofFn,
        List.sum_ofFn]
      exact d.p_total
    have hBmass : exponentMass false w = 1 := by
      rw [hred.mass false, ExponentData.word, pairWord_mass_false, List.map_ofFn,
        List.sum_ofFn]
      exact d.q_total
    have hinfeasible : ¬FeasibleWord w := by
      intro hgood
      obtain ⟨A, B, hA, hB, _, hlarge⟩ :=
        word_infeasible_psd_counterexample d hred hf 1 (by norm_num)
      have hbound := feasibleWord_trace_bound_semidefinite hw hgood hA hB
      simp only [one_mul] at hlarge
      exact not_lt_of_ge hbound hlarge
    exact optimalConstant_infinite_of_infeasibleWord hw hAmass hBmass hinfeasible n hn

end ResearchMain.AHOConstants
