import MainTheorems.Chollet.RankCoefficients.Partition

noncomputable section

namespace ResearchMain.Chollet.RankCoefficients

variable {I : Type*} [Fintype I] [DecidableEq I]

omit [Fintype I] in
theorem RootedPartition.union_not_mem_rest (p : RootedPartition I)
    (s t : Finset I) (hs : s ∈ p.parts) :
    s ∪ t ∉ (p.parts.erase s).erase t := by
  intro h
  have hrest := Finset.mem_erase.mp (Finset.mem_erase.mp h).2
  have hd := p.disjoint s hs (s ∪ t) hrest.2 (Ne.symm hrest.1)
  obtain ⟨i, hi⟩ := p.nonempty s hs
  exact Finset.disjoint_left.mp hd hi (Finset.mem_union_left _ hi)

def RootedPartition.mergeParts (p : RootedPartition I)
    (s t : Finset I) (hs : s ∈ p.parts) (ht : t ∈ p.parts)
    (c : I → ℂ) (hc : ∀ i ∈ s ∪ t, ‖c i‖ = 1) : RootedPartition I where
  closed := p.closed
  parts := insert (s ∪ t) ((p.parts.erase s).erase t)
  phase := fun r => if r = s ∪ t then c else p.phase r
  nonempty := by
    intro r hr
    rcases Finset.mem_insert.mp hr with rfl | hr
    · exact (p.nonempty s hs).mono Finset.subset_union_left
    · exact p.nonempty r (Finset.mem_erase.mp (Finset.mem_erase.mp hr).2).2
  disjoint := by
    intro r hr q hq hrq
    rcases Finset.mem_insert.mp hr with rfl | hr
    · have hqr : q ∈ (p.parts.erase s).erase t :=
        (Finset.mem_insert.mp hq).resolve_left (Ne.symm hrq)
      have hqt := Finset.mem_erase.mp hqr
      have hqs := Finset.mem_erase.mp hqt.2
      exact Finset.disjoint_union_left.mpr
        ⟨p.disjoint s hs q hqs.2 (Ne.symm hqs.1),
          p.disjoint t ht q hqs.2 (Ne.symm hqt.1)⟩
    · rcases Finset.mem_insert.mp hq with rfl | hq
      · have hrt := Finset.mem_erase.mp hr
        have hrs := Finset.mem_erase.mp hrt.2
        exact (Finset.disjoint_union_left.mpr
          ⟨p.disjoint s hs r hrs.2 (Ne.symm hrs.1),
            p.disjoint t ht r hrs.2 (Ne.symm hrt.1)⟩).symm
      · exact p.disjoint r (Finset.mem_erase.mp (Finset.mem_erase.mp hr).2).2
          q (Finset.mem_erase.mp (Finset.mem_erase.mp hq).2).2 hrq
  closed_disjoint := by
    intro r hr
    rcases Finset.mem_insert.mp hr with rfl | hr
    · exact Finset.disjoint_union_right.mpr ⟨p.closed_disjoint s hs, p.closed_disjoint t ht⟩
    · exact p.closed_disjoint r (Finset.mem_erase.mp (Finset.mem_erase.mp hr).2).2
  cover := by
    intro i
    rcases p.cover i with hi | ⟨r, hr, hir⟩
    · exact Or.inl hi
    · by_cases hrs : r = s
      · subst r
        exact Or.inr ⟨s ∪ t, Finset.mem_insert_self _ _, Finset.mem_union_left _ hir⟩
      · by_cases hrt : r = t
        · subst r
          exact Or.inr ⟨s ∪ t, Finset.mem_insert_self _ _, Finset.mem_union_right _ hir⟩
        · exact Or.inr ⟨r, Finset.mem_insert_of_mem
            (Finset.mem_erase.mpr ⟨hrt, Finset.mem_erase.mpr ⟨hrs, hr⟩⟩), hir⟩
  unit := by
    intro r hr i hi
    split_ifs with he
    · subst r
      exact hc i hi
    · have hrest := (Finset.mem_insert.mp hr).resolve_left he
      exact p.unit r (Finset.mem_erase.mp (Finset.mem_erase.mp hrest).2).2 i hi

omit [Fintype I] in
theorem RootedPartition.mergeParts_card (p : RootedPartition I)
    (s t : Finset I) (hs : s ∈ p.parts) (ht : t ∈ p.parts) (hst : s ≠ t)
    (c : I → ℂ) (hc : ∀ i ∈ s ∪ t, ‖c i‖ = 1) :
    (p.mergeParts s t hs ht c hc).parts.card + 1 = p.parts.card := by
  have ht' : t ∈ p.parts.erase s := Finset.mem_erase.mpr ⟨Ne.symm hst, ht⟩
  have hn := p.union_not_mem_rest s t hs
  have hp : 0 < (p.parts.erase s).card := Finset.card_pos.mpr ⟨t, ht'⟩
  rw [Finset.card_erase_of_mem hs] at hp
  change (insert (s ∪ t) ((p.parts.erase s).erase t)).card + 1 = _
  rw [Finset.card_insert_of_notMem hn, Finset.card_erase_of_mem ht',
    Finset.card_erase_of_mem hs]
  omega

omit [Fintype I] in
theorem RootedPartition.polynomial_two_parts (p : RootedPartition I)
    (s t : Finset I) (hs : s ∈ p.parts) (ht : t ∈ p.parts) (hst : s ≠ t) :
    p.polynomial = rooted s (p.phase s) * rooted t (p.phase t) * monomial p.closed *
      ∏ r ∈ (p.parts.erase s).erase t, rooted r (p.phase r) := by
  rw [p.polynomial_part s hs]
  have ht' : t ∈ p.parts.erase s := Finset.mem_erase.mpr ⟨Ne.symm hst, ht⟩
  rw [← Finset.mul_prod_erase (p.parts.erase s) (fun r => rooted r (p.phase r)) ht']
  ring

omit [Fintype I] in
theorem RootedPartition.mergeParts_polynomial (p : RootedPartition I)
    (s t : Finset I) (hs : s ∈ p.parts) (ht : t ∈ p.parts)
    (c : I → ℂ) (hc : ∀ i ∈ s ∪ t, ‖c i‖ = 1) :
    (p.mergeParts s t hs ht c hc).polynomial =
      rooted (s ∪ t) c * monomial p.closed *
        ∏ r ∈ (p.parts.erase s).erase t, rooted r (p.phase r) := by
  have hn := p.union_not_mem_rest s t hs
  change monomial p.closed *
    (∏ r ∈ insert (s ∪ t) ((p.parts.erase s).erase t),
      rooted r (if r = s ∪ t then c else p.phase r)) = _
  rw [Finset.prod_insert hn, ite_eq_left rfl]
  have he : (∏ r ∈ (p.parts.erase s).erase t,
      rooted r (if r = s ∪ t then c else p.phase r)) =
      ∏ r ∈ (p.parts.erase s).erase t, rooted r (p.phase r) := by
    apply Finset.prod_congr rfl
    intro r hr
    have hne : r ≠ s ∪ t := by
      intro h
      exact hn (h ▸ hr)
    rw [ite_eq_right hne]
  rw [he]
  ring

end ResearchMain.Chollet.RankCoefficients

