import MainTheorems.DominationRoots.SupportSets

namespace ResearchMain.DominationRoots

open Classical Polynomial ResearchMain.Domination

variable {V : Type} [Fintype V]

theorem dominationPolynomial_support (G : SimpleGraph V)
    (hne : ∀ v : CoreVertex G, (attachedLeaves G v.val).Nonempty) :
    dominationPolynomial G =
      X ^ (isolatedVertices G).card * ∏ v : CoreVertex G, starFactor (attachedLeaves G v.val).card := by
  have hsum :
      (∑ R : Finset (Σ i, SupportFiber G i),
        if Dominates G (supportSet G R) then (X : ℤ[X]) ^ R.card else 0) =
      ∑ S : Finset V, if Dominates G S then (X : ℤ[X]) ^ S.card else 0 := by
    apply Fintype.sum_equiv (supportVertexEquiv G).finsetCongr
    intro R
    simp only [Equiv.finsetCongr_apply, supportSet, Finset.card_map]
    by_cases hd : Dominates G (R.map (supportVertexEquiv G).toEmbedding) <;> simp [hd]
  calc
    _ = ∑ R : Finset (Σ i, SupportFiber G i),
        if Dominates G (supportSet G R) then (X : ℤ[X]) ^ R.card else 0 := by
      rw [hsum]
      simp [dominationPolynomial, allDominatingSets, Finset.sum_filter]
    _ = ∑ R : Finset (Σ i, SupportFiber G i),
        if ∀ i, CoversSupport G i (subsetFiber R i) then (X : ℤ[X]) ^ R.card else 0 := by
      simp_rw [supportSet_dominates_iff G hne]
    _ = ∏ i, ∑ S : Finset (SupportFiber G i),
        if CoversSupport G i S then (X : ℤ[X]) ^ S.card else 0 := polynomial_fiber_sum _
    _ = _ := by
      rw [Fintype.prod_option]
      simp only [CoversSupport]
      simp only [star_subset_polynomial, Fintype.card_coe]
      congr 1
      have hi := Fintype.sum_ite_eq' (Finset.univ : Finset ↥(isolatedVertices G))
        (fun S => (X : ℤ[X]) ^ S.card)
      convert (show (∑ S : Finset ↥(isolatedVertices G),
          if S = Finset.univ then (X : ℤ[X]) ^ S.card else 0) =
          X ^ (isolatedVertices G).card from
        by simpa only [Finset.card_univ, Fintype.card_coe] using hi) using 1
      apply Finset.sum_congr rfl
      intro S _
      by_cases hs : S = (isolatedVertices G).attach <;> simp [hs]

theorem dominationPolynomial_leaf_equality {G : SimpleGraph V}
    (hmin : dominationNumber G = Fintype.card V - (leafNeighborhoods G).card) :
    dominationPolynomial G =
      X ^ (isolatedVertices G).card * ∏ v : CoreVertex G, starFactor (attachedLeaves G v.val).card := by
  exact dominationPolynomial_support G (fun v => core_leaf_nonempty hmin v.property)

end ResearchMain.DominationRoots
