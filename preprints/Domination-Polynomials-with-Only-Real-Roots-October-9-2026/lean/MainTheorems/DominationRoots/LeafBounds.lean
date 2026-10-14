import MainTheorems.DominationRoots.SupportPolynomial
import Mathlib.RingTheory.Coprime.Lemmas

namespace ResearchMain.DominationRoots

open Classical Polynomial

theorem constant_one_coprime_X {f : ℤ[X]} (h0 : f.coeff 0 = 1) : IsCoprime f X := by
  refine ⟨1, -f.divX, ?_⟩
  have h := X_mul_divX_add f
  rw [h0, C_1] at h
  linear_combination -h

variable {V : Type} [Fintype V]

theorem reducedStarFactor_dvd_domination {G : SimpleGraph V}
    (hmin : dominationNumber G = Fintype.card V - (leafNeighborhoods G).card)
    (v : CoreVertex G) :
    reducedStarFactor (attachedLeaves G v.val).card ∣ dominationPolynomial G := by
  have hs : 1 ≤ (attachedLeaves G v.val).card :=
    Finset.one_le_card.mpr (core_leaf_nonempty hmin v.property)
  have hd : reducedStarFactor (attachedLeaves G v.val).card ∣
      starFactor (attachedLeaves G v.val).card := by
    rw [starFactor_eq _ hs]
    exact dvd_mul_left _ _
  rw [dominationPolynomial_leaf_equality hmin]
  exact dvd_mul_of_dvd_right (hd.trans
    (Finset.dvd_prod_of_mem (fun w : CoreVertex G => starFactor (attachedLeaves G w.val).card)
      (Finset.mem_univ v))) _

theorem attachedLeaves_card_classification {G : SimpleGraph V}
    (hr : RealRooted (dominationPolynomial G)) (hn : 2 ≤ Fintype.card V) (v : CoreVertex G) :
    (attachedLeaves G v.val).card = 1 ∨ (attachedLeaves G v.val).card = 2 := by
  obtain ⟨hmin, q, hqm, he, ht, ha⟩ := leaf_trace_equality hr hn
  have hs1 : 1 ≤ (attachedLeaves G v.val).card :=
    Finset.one_le_card.mpr (core_leaf_nonempty hmin v.property)
  by_cases hs : (attachedLeaves G v.val).card = 1
  · exact Or.inl hs
  · right
    have hs2 : 2 ≤ (attachedLeaves G v.val).card := by omega
    have hm := reducedStarFactor_monic (attachedLeaves G v.val).card hs2
    have hcop := constant_one_coprime_X (reducedStarFactor_constant _ hs2)
    have hd := reducedStarFactor_dvd_domination hmin v
    rw [he] at hd
    have hdq := hcop.pow_right.dvd_of_dvd_mul_left hd
    have hdr := reflection_dvd hm hqm hdq
    exact reducedStarFactor_classification hs2
      (totallyPositive_of_dvd (reflection_monic hqm) (reflection_monic hm) ht hdr)
      (allowedProduct_of_monic_dvd (reflection_monic hqm) (reflection_monic hm) ht ha hdr)

end ResearchMain.DominationRoots
