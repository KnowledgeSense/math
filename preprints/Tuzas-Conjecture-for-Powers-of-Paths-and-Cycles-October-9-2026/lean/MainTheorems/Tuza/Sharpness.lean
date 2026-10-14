import MainTheorems.Tuza.CompleteInequality

namespace ResearchMain.Tuza

theorem packingNumber_le_one {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (hV : Fintype.card V ≤ 4) : packingNumber G ≤ 1 := by
  classical
  obtain ⟨P, hP, hcard⟩ := exists_maximum_packing G
  rw [← hcard]
  by_contra h
  obtain ⟨t, ht, u, hu, htu⟩ := Finset.one_lt_card.mp (by omega : 1 < P.card)
  have htcard := (hP.1 t ht).card_eq
  have hucard := (hP.1 u hu).card_eq
  have hunion : (t ∪ u).card ≤ 4 := (Finset.card_le_univ _).trans hV
  have hinter : 1 < (t ∩ u).card := by
    have hi := Finset.card_union_add_card_inter t u
    omega
  obtain ⟨x, hx, y, hy, hxy⟩ := Finset.one_lt_card.mp hinter
  obtain ⟨hxt, hxu⟩ := Finset.mem_inter.mp hx
  obtain ⟨hyt, hyu⟩ := Finset.mem_inter.mp hy
  exact Finset.disjoint_left.mp (hP.2 ht hu htu)
    (mem_triangleEdges.mpr ⟨hxt, hyt, hxy⟩) (mem_triangleEdges.mpr ⟨hxu, hyu, hxy⟩)

theorem complete_four_packingNumber : packingNumber (⊤ : SimpleGraph (Fin 4)) = 1 := by
  obtain ⟨P, hP, hcard⟩ := complete_packing 4
  have hl := packing_le_number hP
  have hc : completeCount 4 = 1 := by decide
  rw [hcard, hc] at hl
  exact Nat.le_antisymm (packingNumber_le_one _ (by simp)) hl

theorem complete_four_cover_card {C : Finset (Sym2 (Fin 4))}
    (hC : Cover (⊤ : SimpleGraph (Fin 4)) C) : 2 ≤ C.card := by
  classical
  by_contra h
  obtain ⟨e, he⟩ := Finset.card_le_one_iff_subset_singleton.mp (by omega : C.card ≤ 1)
  induction e using Sym2.inductionOn with
  | hf a b =>
    let t := (Finset.univ : Finset (Fin 4)).erase a
    have ht : (⊤ : SimpleGraph (Fin 4)).IsNClique 3 t := by
      rw [SimpleGraph.isNClique_iff]
      refine ⟨?_, ?_⟩
      · intro x hx y hy hxy
        exact hxy
      · simp [t]
    obtain ⟨f, hf⟩ := hC.2 t ht
    obtain ⟨hft, hfC⟩ := Finset.mem_inter.mp hf
    have hfe : f = s(a, b) := Finset.mem_singleton.mp (he hfC)
    rw [hfe] at hft
    have ha := (mem_triangleEdges.mp hft).1
    exact (Finset.mem_erase.mp ha).1 rfl

theorem complete_four_coverNumber : coverNumber (⊤ : SimpleGraph (Fin 4)) = 2 := by
  obtain ⟨C, hC, hcard⟩ := exists_minimum_cover (⊤ : SimpleGraph (Fin 4))
  have hl := complete_four_cover_card hC
  rw [hcard] at hl
  have hu := complete_cover_bound 4
  have hc : (halfUp 4).choose 2 + (4 - halfUp 4).choose 2 = 2 := by decide
  rw [hc] at hu
  exact Nat.le_antisymm hu hl

theorem complete_isCoChain (V : Type*) : IsCoChain (⊤ : SimpleGraph V) := by
  refine ⟨Set.univ, ?_, ?_, ?_⟩
  · intro x hx y hy hxy
    exact hxy
  · intro x hx
    exact False.elim (hx (Set.mem_univ x))
  · intro x hx y hy
    left
    intro z hz
    exact False.elim (hz (Set.mem_univ z))

theorem coChain_sharpness : ∃ G : SimpleGraph (Fin 4), IsCoChain G ∧
    0 < packingNumber G ∧ coverNumber G = 2 * packingNumber G := by
  refine ⟨⊤, complete_isCoChain _, ?_, ?_⟩
  · rw [complete_four_packingNumber]
    decide
  · rw [complete_four_coverNumber, complete_four_packingNumber]

end ResearchMain.Tuza
