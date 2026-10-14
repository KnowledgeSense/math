import MainTheorems.AHOConstants.NormalizedReduction
import MainTheorems.AHOConstants.FlowDuality

namespace ResearchMain.AHOConstants

open scoped BigOperators

structure ExponentData where
  size : ℕ
  p : Fin (size + 1) → ℝ
  q : Fin (size + 1) → ℝ
  p_positive : ∀ i, 0 < p i
  q_positive : ∀ i, 0 < q i
  p_total : (∑ i, p i) = 1
  q_total : (∑ i, q i) = 1

def ExponentData.word (d : ExponentData) : TraceWord :=
  pairWord (List.ofFn (fun i => (d.p i, d.q i)))

def ExponentData.feasible (d : ExponentData) : Prop := Feasible d.p d.q

def FeasibleWord (w : TraceWord) : Prop :=
  ∃ d : ExponentData, WordReduction w d.word ∧ d.feasible

theorem normalized_reduced_data {w : TraceWord} (hw : WordNonnegative w)
    (hA : exponentMass true w = 1) (hB : exponentMass false w = 1) :
    ∃ d : ExponentData, WordReduction w d.word := by
  obtain ⟨xs, hred, hxs, hpos, hp, hq⟩ := normalized_pair_reduction hw hA hB
  have hn : xs.length ≠ 0 := fun h => hxs (List.length_eq_zero_iff.mp h)
  obtain ⟨m, hlen⟩ := Nat.exists_eq_succ_of_ne_zero hn
  let e : Fin xs.length ≃ Fin (m + 1) := finCongr hlen
  let p : Fin (m + 1) → ℝ := fun i => (xs.get (e.symm i)).1
  let q : Fin (m + 1) → ℝ := fun i => (xs.get (e.symm i)).2
  have hp₁ : (∑ i, p i) = 1 := by
    have hs := Equiv.sum_comp e.symm (fun i : Fin xs.length => (xs.get i).1)
    exact hs.trans ((pair_index_sum_first xs).trans hp)
  have hq₁ : (∑ i, q i) = 1 := by
    have hs := Equiv.sum_comp e.symm (fun i : Fin xs.length => (xs.get i).2)
    exact hs.trans ((pair_index_sum_second xs).trans hq)
  let d : ExponentData :=
    { size := m
      p := p
      q := q
      p_positive := fun i => (hpos _ (List.get_mem xs (e.symm i))).1
      q_positive := fun i => (hpos _ (List.get_mem xs (e.symm i))).2
      p_total := hp₁
      q_total := hq₁ }
  have hs : List.ofFn (fun i : Fin (m + 1) => xs.get (e.symm i)) = xs := by
    exact (List.ofFn_congr hlen xs.get).symm.trans (List.ofFn_get xs)
  refine ⟨d, ?_⟩
  change WordReduction w (pairWord (List.ofFn (fun i : Fin (m + 1) => xs.get (e.symm i))))
  rw [hs]
  exact hred

theorem ExponentData.infeasible_cut (d : ExponentData) (h : ¬d.feasible) :
    ∃ S T, cutCapacity d.p d.q S T < 1 :=
  infeasible_strict_cut d.p d.q (fun i => (d.q_positive i).le) d.p_total d.q_total h

end ResearchMain.AHOConstants
