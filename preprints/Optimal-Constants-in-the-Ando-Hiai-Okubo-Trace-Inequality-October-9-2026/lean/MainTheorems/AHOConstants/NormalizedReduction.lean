import MainTheorems.AHOConstants.PairWords
import Mathlib.Algebra.BigOperators.Fin

namespace ResearchMain.AHOConstants

open scoped BigOperators

theorem normalized_pair_reduction {w : TraceWord} (hw : WordNonnegative w)
    (hA : exponentMass true w = 1) (hB : exponentMass false w = 1) :
    ∃ xs : List (ℝ × ℝ), WordReduction w (pairWord xs) ∧ xs ≠ [] ∧
      (∀ pq ∈ xs, 0 < pq.1 ∧ 0 < pq.2) ∧
      (xs.map Prod.fst).sum = 1 ∧ (xs.map Prod.snd).sum = 1 := by
  obtain ⟨v, hv, hmin⟩ := exists_minimal_word w
  have hmA : exponentMass true v = 1 := (hv.mass true).symm.trans hA
  have hmB : exponentMass false v = 1 := (hv.mass false).symm.trans hB
  obtain ⟨p, hp⟩ := mass_nonzero_has_colour true v (by rw [hmA]; norm_num)
  obtain ⟨u, t, hword⟩ := List.mem_iff_append.mp hp
  let r : TraceWord := (true, p) :: (t ++ u)
  have hr : WordReduction v r := by
    rw [hword]
    simpa only [r, List.cons_append] using WordReduction.step (WordStep.rotate u ((true, p) :: t))
  have hlen : r.length = v.length := by
    simp only [r, hword, List.length_cons, List.length_append]
    omega
  have hminr : ∀ s, WordReduction r s → r.length ≤ s.length := by
    intro s hs
    rw [hlen]
    exact hmin s (hr.trans hs)
  have hnr := hr.nonnegative (hv.nonnegative hw)
  have hpr := minimal_word_positive hnr hminr
  have hcr := no_adjacent_chain (minimal_word_no_adjacent hnr hminr)
  have hbr : exponentMass false r = 1 := (hr.mass false).symm.trans hmB
  have hsr : StartsTrue r := by
    intro cr hcr
    simp only [r, List.head?_cons, Option.some.injEq] at hcr
    subst cr
    rfl
  have her : EndsFalse r := normalized_head_ends_false p (t ++ u)
    (minimal_word_no_cyclic hnr hminr) (by rw [hbr]; norm_num)
  obtain ⟨xs, hxs⟩ := paired_of_chain r hcr hsr her
  have hred : WordReduction w (pairWord xs) := by rw [← hxs]; exact hv.trans hr
  have hpa : (xs.map Prod.fst).sum = 1 := by
    rw [← pairWord_mass_true, (hred.mass true).symm, hA]
  have hpb : (xs.map Prod.snd).sum = 1 := by
    rw [← pairWord_mass_false, (hred.mass false).symm, hB]
  have hxsne : xs ≠ [] := by
    intro heq
    simp only [heq, List.map_nil, List.sum_nil] at hpa
    norm_num at hpa
  have hpos : WordPositive (pairWord xs) := by rw [← hxs]; exact hpr
  exact ⟨xs, hred, hxsne, pairWord_positive hpos, hpa, hpb⟩

theorem pair_index_sum_first (xs : List (ℝ × ℝ)) :
    (∑ i : Fin xs.length, (xs.get i).1) = (xs.map Prod.fst).sum := by
  rw [← List.sum_ofFn, List.ofFn_comp', List.ofFn_get]

theorem pair_index_sum_second (xs : List (ℝ × ℝ)) :
    (∑ i : Fin xs.length, (xs.get i).2) = (xs.map Prod.snd).sum := by
  rw [← List.sum_ofFn, List.ofFn_comp', List.ofFn_get]

end ResearchMain.AHOConstants
