import MainTheorems.Chores.PairParity

namespace ResearchMain.Chores

variable {E : Type*} [DecidableEq E]

noncomputable def halfSet (D : Finset E) : Finset E :=
  Classical.choose (Finset.exists_subset_card_eq (Nat.div_le_self D.card 2))

omit [DecidableEq E] in
theorem halfSet_subset (D : Finset E) : halfSet D ⊆ D :=
  (Classical.choose_spec (Finset.exists_subset_card_eq (Nat.div_le_self D.card 2))).1

omit [DecidableEq E] in
theorem halfSet_card (D : Finset E) : (halfSet D).card = D.card / 2 :=
  (Classical.choose_spec (Finset.exists_subset_card_eq (Nat.div_le_self D.card 2))).2

noncomputable def splitFirst (D F : Finset E) : Finset E := halfSet D ∪ halfSet F

noncomputable def splitSecond (D F : Finset E) : Finset E := (D ∪ F) \ splitFirst D F

theorem splitFirst_subset (D F : Finset E) : splitFirst D F ⊆ D ∪ F :=
  Finset.union_subset_union (halfSet_subset D) (halfSet_subset F)

theorem splitFirst_inter_left {D F : Finset E} (hd : Disjoint D F) :
    splitFirst D F ∩ D = halfSet D := by
  rw [Finset.disjoint_left] at hd
  ext e
  simp only [splitFirst, Finset.mem_inter, Finset.mem_union]
  constructor
  · rintro ⟨h | h, he⟩
    · exact h
    · exact False.elim (hd he (halfSet_subset F h))
  · intro h
    exact ⟨Or.inl h, halfSet_subset D h⟩

theorem splitFirst_inter_right {D F : Finset E} (hd : Disjoint D F) :
    splitFirst D F ∩ F = halfSet F := by
  have heq : splitFirst D F = splitFirst F D := by exact Finset.union_comm _ _
  rw [heq]
  exact splitFirst_inter_left hd.symm

theorem splitSecond_inter_left {D F : Finset E} (hd : Disjoint D F) :
    splitSecond D F ∩ D = D \ halfSet D := by
  have hfirst := splitFirst_inter_left hd
  ext e
  have heq := Finset.ext_iff.mp hfirst e
  simp only [splitSecond, Finset.mem_inter, Finset.mem_sdiff, Finset.mem_union] at heq ⊢
  tauto

theorem splitSecond_inter_right {D F : Finset E} (hd : Disjoint D F) :
    splitSecond D F ∩ F = F \ halfSet F := by
  have heq : splitSecond D F = splitSecond F D := by
    unfold splitSecond splitFirst
    rw [Finset.union_comm D F, Finset.union_comm (halfSet D) (halfSet F)]
  rw [heq]
  exact splitSecond_inter_left hd.symm

theorem splitFirst_card {D F : Finset E} (hd : Disjoint D F) :
    (splitFirst D F).card = D.card / 2 + F.card / 2 := by
  have hd' : Disjoint (halfSet D) (halfSet F) := hd.mono (halfSet_subset D) (halfSet_subset F)
  rw [splitFirst, Finset.card_union_of_disjoint hd', halfSet_card, halfSet_card]

theorem splitSecond_card {D F : Finset E} (hd : Disjoint D F) :
    (splitSecond D F).card = (D.card - D.card / 2) + (F.card - F.card / 2) := by
  rw [splitSecond, Finset.card_sdiff_of_subset (splitFirst_subset D F),
    Finset.card_union_of_disjoint hd, splitFirst_card hd]
  have hD := Nat.div_le_self D.card 2
  have hF := Nat.div_le_self F.card 2
  omega

theorem split_even_filler {D F : Finset E} (hd : Disjoint D F) (hF : Even F.card) :
    (splitFirst D F ∩ F).card = F.card / 2 ∧
      (splitSecond D F ∩ F).card = F.card / 2 ∧
      (splitFirst D F).card = (D.card + F.card) / 2 ∧
      (splitSecond D F).card = (D.card + F.card + 1) / 2 := by
  rw [Nat.even_iff] at hF
  rw [splitFirst_inter_right hd, splitSecond_inter_right hd, halfSet_card,
    Finset.card_sdiff_of_subset (halfSet_subset F), halfSet_card,
    splitFirst_card hd, splitSecond_card hd]
  omega

end ResearchMain.Chores
