import MainTheorems.PreorderGamma.CommonCancellation

namespace ResearchMain.PreorderGamma

variable {E : Type*} [Fintype E] [DecidableEq E] [Preorder E]

def OrderedEndpoints (E : Type*) [DecidableEq E] [Preorder E] :=
  {p : Finset E × Finset E // HasOrderMatching p.1 p.2}

structure SeparatedEndpoints (E : Type*) [DecidableEq E] [Preorder E] where
  left : Finset E
  right : Finset E
  common : Finset E
  matched : IsMatchedPair left right
  common_disjoint : Disjoint common (left ∪ right)

omit [Fintype E] in
theorem separatedEndpoints_ext {p q : SeparatedEndpoints E}
    (hl : p.left = q.left) (hr : p.right = q.right) (hc : p.common = q.common) : p = q := by
  cases p
  cases q
  cases hl
  cases hr
  cases hc
  rfl

noncomputable instance : Fintype (OrderedEndpoints E) := by
  classical
  unfold OrderedEndpoints
  infer_instance

instance : Finite (SeparatedEndpoints E) :=
  Finite.of_injective (fun p : SeparatedEndpoints E => (p.left, p.right, p.common))
    (by
      intro p q h
      apply separatedEndpoints_ext
      · exact congrArg Prod.fst h
      · exact congrArg (fun x => x.2.1) h
      · exact congrArg (fun x => x.2.2) h)

noncomputable instance : Fintype (SeparatedEndpoints E) := Fintype.ofFinite _

omit [Fintype E] in
theorem common_union_sdiff (p : SeparatedEndpoints E) :
    (p.left ∪ p.common) \ (p.right ∪ p.common) = p.left := by
  ext a
  simp only [Finset.mem_sdiff, Finset.mem_union]
  have h1 := Finset.disjoint_left.mp p.matched.1
  have h2 := Finset.disjoint_left.mp p.common_disjoint
  constructor
  · rintro ⟨ha | ha, hn⟩
    · exact ha
    · exact False.elim (hn (Or.inr ha))
  · intro ha
    refine ⟨Or.inl ha, ?_⟩
    rintro (hb | hc)
    · exact h1 ha hb
    · exact h2 hc (Finset.mem_union_left _ ha)

omit [Fintype E] in
theorem common_union_sdiff_right (p : SeparatedEndpoints E) :
    (p.right ∪ p.common) \ (p.left ∪ p.common) = p.right := by
  ext a
  simp only [Finset.mem_sdiff, Finset.mem_union]
  have h1 := Finset.disjoint_left.mp p.matched.1
  have h2 := Finset.disjoint_left.mp p.common_disjoint
  constructor
  · rintro ⟨ha | ha, hn⟩
    · exact ha
    · exact False.elim (hn (Or.inr ha))
  · intro ha
    refine ⟨Or.inl ha, ?_⟩
    rintro (hb | hc)
    · exact h1 hb ha
    · exact h2 hc (Finset.mem_union_right _ ha)

omit [Fintype E] in
theorem common_union_inter (p : SeparatedEndpoints E) :
    (p.left ∪ p.common) ∩ (p.right ∪ p.common) = p.common := by
  ext a
  simp only [Finset.mem_inter, Finset.mem_union]
  have h := Finset.disjoint_left.mp p.matched.1
  constructor
  · rintro ⟨hl | hc, hr | hc⟩
    · exact False.elim (h hl hr)
    · exact hc
    · exact hc
    · exact hc
  · intro hc
    exact ⟨Or.inr hc, Or.inr hc⟩

def separateEndpoints (p : OrderedEndpoints E) : SeparatedEndpoints E where
  left := p.val.1 \ p.val.2
  right := p.val.2 \ p.val.1
  common := p.val.1 ∩ p.val.2
  matched := (hasOrderMatching_iff_matched_sdiff _ _).mp p.property
  common_disjoint := by
    apply Finset.disjoint_left.mpr
    intro a ha hb
    obtain ⟨has, hat⟩ := Finset.mem_inter.mp ha
    rcases Finset.mem_union.mp hb with hb | hb
    · exact (Finset.mem_sdiff.mp hb).2 hat
    · exact (Finset.mem_sdiff.mp hb).2 has

def joinEndpoints (p : SeparatedEndpoints E) : OrderedEndpoints E := by
  refine ⟨(p.left ∪ p.common, p.right ∪ p.common), ?_⟩
  apply HasOrderMatching.restore_intersection
  rw [common_union_sdiff, common_union_sdiff_right]
  exact p.matched.2

def endpointDecompositionEquiv : OrderedEndpoints E ≃ SeparatedEndpoints E where
  toFun := separateEndpoints
  invFun := joinEndpoints
  left_inv := by
    intro p
    apply Subtype.ext
    apply Prod.ext
    · exact Finset.sdiff_union_inter p.val.1 p.val.2
    · change p.val.2 \ p.val.1 ∪ p.val.1 ∩ p.val.2 = p.val.2
      simpa only [Finset.inter_comm p.val.1 p.val.2] using
        Finset.sdiff_union_inter p.val.2 p.val.1
  right_inv := by
    intro p
    apply separatedEndpoints_ext
    · exact common_union_sdiff p
    · exact common_union_sdiff_right p
    · exact common_union_inter p

omit [Fintype E] in
theorem separatedEndpoints_support_card (p : SeparatedEndpoints E) :
    (joinEndpoints p).val.1.card = p.left.card + p.common.card := by
  change (p.left ∪ p.common).card = _
  rw [Finset.card_union_of_disjoint]
  apply Finset.disjoint_left.mpr
  intro a hl hc
  exact Finset.disjoint_left.mp p.common_disjoint hc (Finset.mem_union_left _ hl)

end ResearchMain.PreorderGamma
