import MeanMaximumForests.GraphConstruction

namespace MeanMaximumForests

/-- The rooted recursion gives the bipartite independence bound, with one unit
of extra room when some component root belongs to every maximum independent set. -/
theorem ForestExpr.order_flag_bound (A : ForestExpr) :
    A.statistics.vertices + (if flag A then 1 else 0) ≤ 2 * A.statistics.alpha := by
  induction A with
  | empty => decide
  | union A B hA hB =>
    cases ha : flag A <;> cases hb : flag B <;>
      simp_all [ForestExpr.statistics, flag]
    all_goals omega
  | root A hA =>
    cases ha : flag A <;> simp_all [ForestExpr.statistics, flag]
    all_goals omega

theorem ForestExpr.order_le_twice_alpha (A : ForestExpr) :
    A.statistics.vertices ≤ 2 * A.statistics.alpha := by
  have h := A.order_flag_bound
  omega

theorem ForestExpr.alpha_pos_of_order_pos (A : ForestExpr) (hA : 0 < A.statistics.vertices) :
    0 < A.statistics.alpha := by
  have h := A.order_le_twice_alpha
  omega

/-- The same bound holds inside every finite vertex subset of an acyclic graph. -/
theorem forest_card_le_twice_independenceNumber {V : Type*} [DecidableEq V]
    (G : SimpleGraph V) (hG : G.IsAcyclic) (s : Finset V) :
    s.card ≤ 2 * independenceNumber G s := by
  obtain ⟨rs, A, hA⟩ := exists_forestRealization G hG s
  rw [hA.card_statistics G, hA.alpha_statistics G]
  exact A.order_le_twice_alpha

/-- Every actual finite forest has an independent set containing at least half its vertices. -/
theorem forest_card_le_twice_indepNum {V : Type*} [Fintype V]
    (G : SimpleGraph V) (hG : G.IsAcyclic) : Fintype.card V ≤ 2 * G.indepNum := by
  classical
  obtain ⟨rs, A, hA⟩ := exists_forestRealization G hG Finset.univ
  have h := A.order_le_twice_alpha
  rw [← hA.card_statistics G, ← hA.alpha_statistics G, independenceNumber_univ] at h
  simpa only [Finset.card_univ] using h

end MeanMaximumForests
