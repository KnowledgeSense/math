import MainTheorems.Chores.CapacitySlots
import MainTheorems.Chores.Basic
import Mathlib.Data.Finset.Sum

namespace ResearchMain.Chores

open scoped BigOperators

variable {A E : Type*} [Fintype A] [Fintype E] [DecidableEq A] [DecidableEq E]

def incidentAllowed (R : E → Finset A) (U : Finset A) : Finset E :=
  Finset.univ.filter (fun e => ∃ a ∈ U, a ∈ R e)

def confinedAllowed (R : E → Finset A) (U : Finset A) : Finset E :=
  Finset.univ.filter (fun e => R e ⊆ U)

def LowerHall (R : E → Finset A) (l : A → ℕ) : Prop :=
  ∀ U : Finset A, ∑ a ∈ U, l a ≤ (incidentAllowed R U).card

def UpperHall (R : E → Finset A) (u : A → ℕ) : Prop :=
  ∀ U : Finset A, (confinedAllowed R U).card ≤ ∑ a ∈ U, u a

omit [DecidableEq E] in
theorem upperHall_total (R : E → Finset A) (u : A → ℕ) (h : UpperHall R u) :
    Fintype.card E ≤ ∑ a, u a := by
  simpa [confinedAllowed] using h Finset.univ

omit [Fintype A] [DecidableEq E] in
theorem upperHall_neighbor_bound (R : E → Finset A) (u : A → ℕ) (h : UpperHall R u)
    (I : Finset E) : I.card ≤ ∑ a ∈ I.biUnion R, u a := by
  apply (Finset.card_le_card (t := confinedAllowed R (I.biUnion R)) ?_).trans (h _)
  intro e he
  simp only [confinedAllowed, Finset.mem_filter, Finset.mem_univ, true_and]
  intro a ha
  exact Finset.mem_biUnion.mpr ⟨e, he, ha⟩

theorem lowerHall_complement_bound (R : E → Finset A) (l : A → ℕ) (h : LowerHall R l)
    (I : Finset E) : (∑ a ∈ (I.biUnion R)ᶜ, l a) + I.card ≤ Fintype.card E := by
  have hs : incidentAllowed R (I.biUnion R)ᶜ ⊆ Iᶜ := by
    intro e he
    simp only [incidentAllowed, Finset.mem_filter, Finset.mem_univ, true_and] at he
    obtain ⟨a, ha, hae⟩ := he
    rw [Finset.mem_compl]
    intro hei
    exact (Finset.mem_compl.mp ha) (Finset.mem_biUnion.mpr ⟨e, hei, hae⟩)
  have hc := (h (I.biUnion R)ᶜ).trans (Finset.card_le_card hs)
  have hcard := Finset.card_compl_add_card I
  omega

def expandedAllowed (R : E → Finset A) (l u : A → ℕ) :
    E ⊕ Fin ((∑ a, u a) - Fintype.card E) → Finset (Slot u) :=
  Sum.elim (fun e => slotBlock u (R e)) (fun _ => optionalSlots l u)

theorem expanded_hall (R : E → Finset A) (l u : A → ℕ) (hlu : ∀ a, l a ≤ u a)
    (hl : LowerHall R l) (hu : UpperHall R u)
    (S : Finset (E ⊕ Fin ((∑ a, u a) - Fintype.card E))) :
    S.card ≤ (S.biUnion (expandedAllowed R l u)).card := by
  let I := S.toLeft
  let N := S.biUnion (expandedAllowed R l u)
  have hblock : slotBlock u (I.biUnion R) ⊆ N := by
    intro s hs
    obtain ⟨e, he, hae⟩ := Finset.mem_biUnion.mp ((mem_slotBlock u _ s).mp hs)
    exact Finset.mem_biUnion.mpr ⟨Sum.inl e, Finset.mem_toLeft.mp he,
      (mem_slotBlock u (R e) s).mpr hae⟩
  have hcard := S.card_toLeft_add_card_toRight
  by_cases hd : S.toRight = ∅
  · have hc := (upperHall_neighbor_bound R u hu I).trans
      (by simpa only [card_slotBlock] using Finset.card_le_card hblock)
    simp only [hd, Finset.card_empty, add_zero] at hcard
    simpa only [← hcard] using hc
  · obtain ⟨d, hds⟩ := Finset.nonempty_iff_ne_empty.mpr hd
    have ho : optionalSlots l u ⊆ N := by
      intro s hs
      exact Finset.mem_biUnion.mpr ⟨Sum.inr d, Finset.mem_toRight.mp hds, hs⟩
    have hm : mandatorySlots l u (I.biUnion R) ⊆ N := by
      intro s hs
      exact hblock ((mem_slotBlock u _ s).mpr ((mem_mandatorySlots l u _ s).mp hs).1)
    have hc := Finset.card_le_card (Finset.union_subset hm ho)
    rw [mandatory_union_optional_card l u hlu] at hc
    have hopt := card_optionalSlots l u hlu
    have hsum := Finset.sum_add_sum_compl (I.biUnion R) l
    have hlo := lowerHall_complement_bound R l hl I
    have htotal := upperHall_total R u hu
    have hdcard : S.toRight.card ≤ (∑ a, u a) - Fintype.card E := by
      simpa using Finset.card_le_univ S.toRight
    change I.card + S.toRight.card = S.card at hcard
    change S.card ≤ N.card
    omega

theorem expanded_matching (R : E → Finset A) (l u : A → ℕ) (hlu : ∀ a, l a ≤ u a)
    (hl : LowerHall R l) (hu : UpperHall R u) :
    ∃ g : E ⊕ Fin ((∑ a, u a) - Fintype.card E) → Slot u,
      Function.Bijective g ∧ ∀ x, g x ∈ expandedAllowed R l u x := by
  obtain ⟨g, hg, hmem⟩ := (Finset.all_card_le_biUnion_card_iff_existsInjective'
    (expandedAllowed R l u)).mp (expanded_hall R l u hlu hl hu)
  refine ⟨g, (Fintype.bijective_iff_injective_and_card g).mpr ⟨hg, ?_⟩, hmem⟩
  have ht := upperHall_total R u hu
  simp only [Fintype.card_sum, Fintype.card_fin, Fintype.card_sigma]
  omega

end ResearchMain.Chores
