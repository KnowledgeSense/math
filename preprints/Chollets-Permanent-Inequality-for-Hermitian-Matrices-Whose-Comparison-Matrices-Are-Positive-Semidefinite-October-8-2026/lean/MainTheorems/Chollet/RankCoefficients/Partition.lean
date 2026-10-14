import MainTheorems.Chollet.RankCoefficients.MergeBlocks

noncomputable section

namespace ResearchMain.Chollet.RankCoefficients

variable (I : Type*) [Fintype I] [DecidableEq I]

structure RootedPartition where
  closed : Finset I
  parts : Finset (Finset I)
  phase : Finset I → I → ℂ
  nonempty : ∀ s ∈ parts, s.Nonempty
  disjoint : ∀ s ∈ parts, ∀ t ∈ parts, s ≠ t → Disjoint s t
  closed_disjoint : ∀ s ∈ parts, Disjoint closed s
  cover : ∀ i, i ∈ closed ∨ ∃ s ∈ parts, i ∈ s
  unit : ∀ s ∈ parts, ∀ i ∈ s, ‖phase s i‖ = 1

variable {I}

def RootedPartition.polynomial (p : RootedPartition I) : SquareFree I :=
  monomial p.closed * ∏ s ∈ p.parts, rooted s (p.phase s)

def RootedPartition.initial : RootedPartition I where
  closed := ∅
  parts := Finset.univ.image (fun i : I => ({i} : Finset I))
  phase := fun _ _ => 1
  nonempty := by
    intro s hs
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hs
    exact Finset.singleton_nonempty i
  disjoint := by
    intro s hs t ht hst
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hs
    obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp ht
    have hij : i ≠ j := fun h => hst (by rw [h])
    simpa using hij
  closed_disjoint := by intro s hs; simp
  cover := by
    intro i
    exact Or.inr ⟨{i}, Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩, by simp⟩
  unit := by intro s hs i hi; simp

@[simp] theorem RootedPartition.initial_polynomial :
    (RootedPartition.initial : RootedPartition I).polynomial = 1 := by
  change monomial ∅ * (∏ s ∈ Finset.univ.image (fun i : I => ({i} : Finset I)),
    rooted s (fun _ => 1)) = 1
  rw [monomial_empty, one_mul]
  apply Finset.prod_eq_one
  intro s hs
  obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hs
  simp [rooted]

theorem RootedPartition.initial_card :
    (RootedPartition.initial : RootedPartition I).parts.card = Fintype.card I := by
  change (Finset.univ.image (fun i : I => ({i} : Finset I))).card = _
  rw [Finset.card_image_of_injective _ Finset.singleton_injective, Finset.card_univ]

def RootedPartition.closePart (p : RootedPartition I) (s : Finset I) (hs : s ∈ p.parts) :
    RootedPartition I where
  closed := p.closed ∪ s
  parts := p.parts.erase s
  phase := p.phase
  nonempty := fun t ht => p.nonempty t (Finset.mem_erase.mp ht).2
  disjoint := fun t ht u hu htu =>
    p.disjoint t (Finset.mem_erase.mp ht).2 u (Finset.mem_erase.mp hu).2 htu
  closed_disjoint := by
    intro t ht
    have hts := Finset.mem_erase.mp ht
    exact Finset.disjoint_union_left.mpr
      ⟨p.closed_disjoint t hts.2, p.disjoint s hs t hts.2 (Ne.symm hts.1)⟩
  cover := by
    intro i
    rcases p.cover i with hic | ⟨t, ht, hit⟩
    · exact Or.inl (Finset.mem_union_left _ hic)
    · by_cases hts : t = s
      · subst t
        exact Or.inl (Finset.mem_union_right _ hit)
      · exact Or.inr ⟨t, Finset.mem_erase.mpr ⟨hts, ht⟩, hit⟩
  unit := fun t ht i hi => p.unit t (Finset.mem_erase.mp ht).2 i hi

omit [Fintype I] in
theorem RootedPartition.closePart_card (p : RootedPartition I) (s : Finset I)
    (hs : s ∈ p.parts) : (p.closePart s hs).parts.card + 1 = p.parts.card := by
  have hp : 0 < p.parts.card := Finset.card_pos.mpr ⟨s, hs⟩
  change (p.parts.erase s).card + 1 = _
  rw [Finset.card_erase_of_mem hs]
  omega

omit [Fintype I] in
theorem RootedPartition.polynomial_part (p : RootedPartition I) (s : Finset I)
    (hs : s ∈ p.parts) :
    p.polynomial = rooted s (p.phase s) * monomial p.closed *
      ∏ t ∈ p.parts.erase s, rooted t (p.phase t) := by
  unfold RootedPartition.polynomial
  rw [← Finset.mul_prod_erase p.parts (fun t => rooted t (p.phase t)) hs]
  ring

omit [Fintype I] in
theorem RootedPartition.closePart_polynomial (p : RootedPartition I) (s : Finset I)
    (hs : s ∈ p.parts) :
    (p.closePart s hs).polynomial = monomial s * monomial p.closed *
      ∏ t ∈ p.parts.erase s, rooted t (p.phase t) := by
  change monomial (p.closed ∪ s) *
    (∏ t ∈ p.parts.erase s, rooted t (p.phase t)) = _
  rw [monomial_union _ _ (p.closed_disjoint s hs)]
  ring

omit [Fintype I] in
theorem RootedPartition.closePart_factor (p : RootedPartition I) (s : Finset I)
    (hs : s ∈ p.parts) (L : SquareFree I) (c : ℂ)
    (h : L * rooted s (p.phase s) * monomial p.closed =
      scalar c * monomial s * monomial p.closed) :
    L * p.polynomial = scalar c * (p.closePart s hs).polynomial := by
  rw [p.polynomial_part s hs, p.closePart_polynomial s hs]
  calc
    L * (rooted s (p.phase s) * monomial p.closed *
        ∏ t ∈ p.parts.erase s, rooted t (p.phase t)) =
      (L * rooted s (p.phase s) * monomial p.closed) *
        ∏ t ∈ p.parts.erase s, rooted t (p.phase t) := by ring
    _ = _ := by rw [h]; ring

end ResearchMain.Chollet.RankCoefficients
