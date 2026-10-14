import MainTheorems.Chores.Deficiency

namespace ResearchMain.Chores

open scoped BigOperators

variable {A E : Type*} [Fintype A] [Fintype E] [DecidableEq A] [DecidableEq E]

omit [Fintype A] [Fintype E] [DecidableEq E] in
theorem mem_separatedAllowed (M : TwoCheapModel A E) (S : Finset A) (a : A) (e : E) :
    a ∈ separatedAllowed M S e ↔
      ((M.first e ∈ S ∨ M.second e ∈ S) ∧ M.Cheap a e ∧ a ∈ S) ∨
      (¬(M.first e ∈ S ∨ M.second e ∈ S) ∧ (M.Cheap a e ∨ a ∈ S)) := by
  by_cases h : M.first e ∈ S ∨ M.second e ∈ S <;>
    simp [separatedAllowed, h, mem_endpointAllowed]

omit [Fintype A] in
theorem separated_incident_union_subset (M : TwoCheapModel A E) (S U : Finset A) :
    incidentEdges M (S ∪ U) ⊆
      incidentEdges M S ∪ incidentAllowed (separatedAllowed M S) U := by
  intro e he
  by_cases hs : M.first e ∈ S ∨ M.second e ∈ S
  · exact Finset.mem_union_left _ ((mem_incidentEdges M S e).mpr hs)
  · apply Finset.mem_union_right
    simp only [incidentAllowed, Finset.mem_filter, Finset.mem_univ, true_and]
    rw [mem_incidentEdges] at he
    simp only [Finset.mem_union] at he
    rcases he with (hf | hf) | (ht | ht)
    · exact False.elim (hs (Or.inl hf))
    · exact ⟨M.first e, hf, (mem_separatedAllowed M S _ e).mpr
        (Or.inr ⟨hs, Or.inl (Or.inl rfl)⟩)⟩
    · exact False.elim (hs (Or.inr ht))
    · exact ⟨M.second e, ht, (mem_separatedAllowed M S _ e).mpr
        (Or.inr ⟨hs, Or.inl (Or.inr rfl)⟩)⟩

omit [Fintype A] in
theorem separated_incident_cover (M : TwoCheapModel A E) (S U : Finset A)
    (hUS : (U ∩ S).Nonempty) :
    Finset.univ ⊆ (incidentEdges M S \ incidentEdges M (U ∩ S)) ∪
      incidentAllowed (separatedAllowed M S) U := by
  intro e _
  by_cases hs : M.first e ∈ S ∨ M.second e ∈ S
  · by_cases ht : e ∈ incidentEdges M (U ∩ S)
    · apply Finset.mem_union_right
      simp only [incidentAllowed, Finset.mem_filter, Finset.mem_univ, true_and]
      rw [mem_incidentEdges] at ht
      rcases ht with hf | ht
      · have h := Finset.mem_inter.mp hf
        exact ⟨M.first e, h.1, (mem_separatedAllowed M S _ e).mpr
          (Or.inl ⟨hs, Or.inl rfl, h.2⟩)⟩
      · have h := Finset.mem_inter.mp ht
        exact ⟨M.second e, h.1, (mem_separatedAllowed M S _ e).mpr
          (Or.inl ⟨hs, Or.inr rfl, h.2⟩)⟩
    · exact Finset.mem_union_left _ (Finset.mem_sdiff.mpr
        ⟨(mem_incidentEdges M S e).mpr hs, ht⟩)
  · obtain ⟨a, ha⟩ := hUS
    have ha' := Finset.mem_inter.mp ha
    apply Finset.mem_union_right
    simp only [incidentAllowed, Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨a, ha'.1, (mem_separatedAllowed M S a e).mpr (Or.inr ⟨hs, Or.inr ha'.2⟩)⟩

omit [Fintype A] in
theorem separated_confined_subset (M : TwoCheapModel A E) (S U : Finset A)
    (hS : ¬S ⊆ U) : confinedAllowed (separatedAllowed M S) U ⊆
      incidentEdges M S \ incidentEdges M (S \ U) := by
  intro e he
  have hr : separatedAllowed M S e ⊆ U := (Finset.mem_filter.mp he).2
  have hs : M.first e ∈ S ∨ M.second e ∈ S := by
    by_contra hn
    apply hS
    intro a ha
    exact hr ((mem_separatedAllowed M S a e).mpr (Or.inr ⟨hn, Or.inr ha⟩))
  refine Finset.mem_sdiff.mpr ⟨(mem_incidentEdges M S e).mpr hs, ?_⟩
  intro ht
  rw [mem_incidentEdges] at ht
  rcases ht with hf | ht
  · have hf' := Finset.mem_sdiff.mp hf
    exact hf'.2 (hr ((mem_separatedAllowed M S _ e).mpr
      (Or.inl ⟨hs, Or.inl rfl, hf'.1⟩)))
  · have ht' := Finset.mem_sdiff.mp ht
    exact ht'.2 (hr ((mem_separatedAllowed M S _ e).mpr
      (Or.inl ⟨hs, Or.inr rfl, ht'.1⟩)))

theorem separated_unconfined_subset (M : TwoCheapModel A E) (S U : Finset A) :
    incidentEdges M (S ∪ Uᶜ) \ incidentEdges M S ⊆
      (confinedAllowed (separatedAllowed M S) U)ᶜ := by
  intro e he
  have he' := Finset.mem_sdiff.mp he
  have hn := (mem_incidentEdges M S e).not.mp he'.2
  have ht := (mem_incidentEdges M (S ∪ Uᶜ) e).mp he'.1
  rw [Finset.mem_compl]
  intro hc
  have hr : separatedAllowed M S e ⊆ U := (Finset.mem_filter.mp hc).2
  have hfirst : M.first e ∈ separatedAllowed M S e :=
    (mem_separatedAllowed M S _ e).mpr (Or.inr ⟨hn, Or.inl (Or.inl rfl)⟩)
  have hsecond : M.second e ∈ separatedAllowed M S e :=
    (mem_separatedAllowed M S _ e).mpr (Or.inr ⟨hn, Or.inl (Or.inr rfl)⟩)
  simp only [Finset.mem_union, Finset.mem_compl] at ht
  tauto

theorem separated_incident_bound (M : TwoCheapModel A E) {μ : ℝ} (hμ0 : 0 ≤ μ)
    (hμ : μ * Fintype.card A = Fintype.card E) {S : Finset A}
    (hS : MaxDeficient M μ S) (U : Finset A) :
    μ * U.card ≤ (incidentAllowed (separatedAllowed M S) U).card := by
  by_cases ht : (U ∩ S).Nonempty
  · have hc := (Finset.card_le_card (separated_incident_cover M S U ht)).trans
      (Finset.card_union_le _ _)
    rw [Finset.card_univ] at hc
    have hd := Finset.card_sdiff_add_card_eq_card
      (incident_mono M (Finset.inter_subset_right (s₁ := U) (s₂ := S)))
    have hm := hS (U ∩ S)
    unfold deficiency at hm
    have hn : U.card + S.card ≤ Fintype.card A + (U ∩ S).card := by
      have hi := Finset.card_inter_add_card_union U S
      have hu := Finset.card_le_univ (U ∪ S)
      omega
    have hc' : (Fintype.card E : ℝ) ≤
        (incidentEdges M S \ incidentEdges M (U ∩ S)).card +
          (incidentAllowed (separatedAllowed M S) U).card := by exact_mod_cast hc
    have hd' : ((incidentEdges M S \ incidentEdges M (U ∩ S)).card : ℝ) +
        (incidentEdges M (U ∩ S)).card = (incidentEdges M S).card := by exact_mod_cast hd
    have hn' : (U.card : ℝ) + S.card ≤ Fintype.card A + (U ∩ S).card := by exact_mod_cast hn
    nlinarith
  · have hdisj : Disjoint S U := by
      rw [Finset.disjoint_left]
      intro a ha hu
      exact ht ⟨a, Finset.mem_inter.mpr ⟨hu, ha⟩⟩
    have hc := (Finset.card_le_card (separated_incident_union_subset M S U)).trans
      (Finset.card_union_le _ _)
    have hm := hS (S ∪ U)
    unfold deficiency at hm
    rw [Finset.card_union_of_disjoint hdisj, Nat.cast_add] at hm
    have hc' : ((incidentEdges M (S ∪ U)).card : ℝ) ≤
        (incidentEdges M S).card + (incidentAllowed (separatedAllowed M S) U).card :=
      by exact_mod_cast hc
    nlinarith

theorem separated_confined_bound (M : TwoCheapModel A E) {μ : ℝ} (hμ0 : 0 ≤ μ)
    (hμ : μ * Fintype.card A = Fintype.card E) {S : Finset A}
    (hS : MaxDeficient M μ S) (U : Finset A) :
    (confinedAllowed (separatedAllowed M S) U).card ≤ μ * U.card := by
  by_cases hs : S ⊆ U
  · have hdisj : Disjoint S Uᶜ := by
      rw [Finset.disjoint_left]
      intro a ha hu
      exact (Finset.mem_compl.mp hu) (hs ha)
    have hc := Finset.card_le_card (separated_unconfined_subset M S U)
    have hd := Finset.card_sdiff_add_card_eq_card
      (incident_mono M (Finset.subset_union_left : S ⊆ S ∪ Uᶜ))
    have hm := hS (S ∪ Uᶜ)
    unfold deficiency at hm
    rw [Finset.card_union_of_disjoint hdisj, Nat.cast_add] at hm
    have hc' : ((incidentEdges M (S ∪ Uᶜ) \ incidentEdges M S).card : ℝ) ≤
        ((confinedAllowed (separatedAllowed M S) U)ᶜ).card := by exact_mod_cast hc
    have hd' : ((incidentEdges M (S ∪ Uᶜ) \ incidentEdges M S).card : ℝ) +
        (incidentEdges M S).card = (incidentEdges M (S ∪ Uᶜ)).card := by exact_mod_cast hd
    have hu' : (Uᶜ.card : ℝ) + U.card = Fintype.card A :=
      by exact_mod_cast Finset.card_compl_add_card U
    have he' : (((confinedAllowed (separatedAllowed M S) U)ᶜ).card : ℝ) +
        (confinedAllowed (separatedAllowed M S) U).card = Fintype.card E :=
      by exact_mod_cast Finset.card_compl_add_card (confinedAllowed (separatedAllowed M S) U)
    nlinarith
  · have hc := Finset.card_le_card (separated_confined_subset M S U hs)
    have hd := Finset.card_sdiff_add_card_eq_card
      (incident_mono M (Finset.sdiff_subset : S \ U ⊆ S))
    have hm := hS (S \ U)
    unfold deficiency at hm
    have ha := Finset.card_sdiff_add_card_inter S U
    have hi := Finset.card_le_card (Finset.inter_subset_right (s₁ := S) (s₂ := U))
    have hc' : ((confinedAllowed (separatedAllowed M S) U).card : ℝ) ≤
        (incidentEdges M S \ incidentEdges M (S \ U)).card := by exact_mod_cast hc
    have hd' : ((incidentEdges M S \ incidentEdges M (S \ U)).card : ℝ) +
        (incidentEdges M (S \ U)).card = (incidentEdges M S).card := by exact_mod_cast hd
    have ha' : ((S \ U).card : ℝ) + (S ∩ U).card = S.card := by exact_mod_cast ha
    have hi' : ((S ∩ U).card : ℝ) ≤ U.card := by exact_mod_cast hi
    nlinarith

end ResearchMain.Chores
