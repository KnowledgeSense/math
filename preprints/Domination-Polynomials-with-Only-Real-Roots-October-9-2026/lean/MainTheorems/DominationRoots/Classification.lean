import MainTheorems.DominationRoots.LeafBounds

namespace ResearchMain.DominationRoots

open Classical Polynomial

variable {V : Type} [Fintype V]

def OneTwoLeafGraph (G : SimpleGraph V) : Prop :=
  ∀ v : CoreVertex G, (attachedLeaves G v.val).card = 1 ∨ (attachedLeaves G v.val).card = 2

theorem starFactor_one_realRooted : RealRooted (starFactor 1) := by
  have he : realPolynomial (starFactor 1) = X * (X + C 2) := by
    simp [realPolynomial, starFactor, map_ofNat]
    ring
  rw [RealRooted, he]
  exact Splits.X.mul (Splits.X_add_C 2)

theorem starFactor_two_realRooted : RealRooted (starFactor 2) := by
  have he : reflection (reducedStarFactor 2) = quadraticPolynomial := by
    rw [reflection, reducedStarFactor_natDegree 2 (by norm_num)]
    norm_num [reducedStarFactor, quadraticPolynomial]
    ring
  have hs : (realPolynomial (reducedStarFactor 2)).Splits := by
    apply (reflection_splits_iff _).mp
    rw [he, quadraticPolynomial_real_factor]
    exact (Splits.X_sub_C _).mul (Splits.X_sub_C _)
  rw [RealRooted, starFactor_eq 2 (by norm_num), realPolynomial_mul]
  simpa [realPolynomial] using (Splits.X (R := ℝ)).mul hs

theorem oneTwoLeafGraph_realRooted {G : SimpleGraph V} (hG : OneTwoLeafGraph G) :
    RealRooted (dominationPolynomial G) := by
  have hne (v : CoreVertex G) : (attachedLeaves G v.val).Nonempty := by
    apply Finset.card_pos.mp
    rcases hG v with h | h <;> omega
  rw [dominationPolynomial_support G hne]
  unfold RealRooted realPolynomial
  rw [Polynomial.map_mul, Polynomial.map_pow, Polynomial.map_X, Polynomial.map_prod]
  apply (Splits.X_pow _).mul
  apply Splits.prod
  intro v _
  rcases hG v with h | h
  · simpa only [h, RealRooted, realPolynomial] using starFactor_one_realRooted
  · simpa only [h, RealRooted, realPolynomial] using starFactor_two_realRooted

theorem small_graph_isolated (G : SimpleGraph V) (hn : Fintype.card V ≤ 1) (v : V) :
    v ∈ isolatedVertices G := by
  apply (mem_isolatedVertices G v).mpr
  ext u
  simp only [mem_closedNeighborhood, Finset.mem_singleton]
  exact iff_of_true (Or.inl (Fintype.card_le_one_iff.mp hn u v))
    (Fintype.card_le_one_iff.mp hn u v)

theorem realRooted_oneTwoLeafGraph {G : SimpleGraph V}
    (hr : RealRooted (dominationPolynomial G)) : OneTwoLeafGraph G := by
  intro v
  by_cases hn : 2 ≤ Fintype.card V
  · exact attachedLeaves_card_classification hr hn v
  · exact False.elim (core_not_isolated v (small_graph_isolated G (by omega) v.val))

theorem realRooted_domination_iff (G : SimpleGraph V) :
    RealRooted (dominationPolynomial G) ↔ OneTwoLeafGraph G :=
  ⟨realRooted_oneTwoLeafGraph, oneTwoLeafGraph_realRooted⟩

end ResearchMain.DominationRoots
