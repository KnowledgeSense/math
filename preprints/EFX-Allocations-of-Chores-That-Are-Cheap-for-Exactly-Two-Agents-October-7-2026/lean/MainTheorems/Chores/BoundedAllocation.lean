import MainTheorems.Chores.CapacityHall

namespace ResearchMain.Chores

open scoped BigOperators

variable {A E : Type*} [Fintype A] [Fintype E] [DecidableEq A] [DecidableEq E]

theorem bounded_allocation (R : E → Finset A) (l u : A → ℕ) (hlu : ∀ a, l a ≤ u a)
    (hl : LowerHall R l) (hu : UpperHall R u) :
    ∃ f : E → A, (∀ e, f e ∈ R e) ∧
      ∀ a, l a ≤ (bundle f a).card ∧ (bundle f a).card ≤ u a := by
  obtain ⟨g, hg, hmem⟩ := expanded_matching R l u hlu hl hu
  let f : E → A := fun e => (g (Sum.inl e)).1
  have hgE : Function.Injective (fun e : E => g (Sum.inl e)) :=
    hg.1.comp Sum.inl_injective
  refine ⟨f, fun e => (mem_slotBlock u (R e) (g (Sum.inl e))).mp (hmem _), ?_⟩
  intro a
  let B := (bundle f a).image (fun e => g (Sum.inl e))
  have hcard : B.card = (bundle f a).card := Finset.card_image_of_injective _ hgE
  have hupper : B ⊆ slotBlock u {a} := by
    intro s hs
    obtain ⟨e, he, rfl⟩ := Finset.mem_image.mp hs
    rw [mem_slotBlock, Finset.mem_singleton]
    exact (mem_bundle f a e).mp he
  have hlower : mandatorySlots l u {a} ⊆ B := by
    intro s hs
    have hsa := (mem_mandatorySlots l u {a} s).mp hs
    have ha : s.1 = a := Finset.mem_singleton.mp hsa.1
    obtain ⟨x, hx⟩ := hg.2 s
    cases x with
    | inl e =>
        refine Finset.mem_image.mpr ⟨e, (mem_bundle f a e).mpr ?_, hx⟩
        exact (congrArg Sigma.fst hx).trans ha
    | inr d =>
        have hop : s ∈ optionalSlots l u := by
          rw [← hx]
          exact hmem (Sum.inr d)
        have hbad := (mem_optionalSlots l u s).mp hop
        omega
  have hlow := Finset.card_le_card hlower
  have hup := Finset.card_le_card hupper
  rw [card_mandatorySlots l u hlu, Finset.sum_singleton, hcard] at hlow
  rw [card_slotBlock, Finset.sum_singleton, hcard] at hup
  exact ⟨hlow, hup⟩

end ResearchMain.Chores
