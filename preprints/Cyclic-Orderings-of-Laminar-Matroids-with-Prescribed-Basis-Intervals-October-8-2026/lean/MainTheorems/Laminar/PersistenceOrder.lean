import MainTheorems.Laminar.Persistence

namespace ResearchMain.Laminar

open Classical

theorem persistence_mono {R A : Type*} (next : R → R) (active : R → A → Prop)
    (i : R) (a b : A) (hsupport : ∀ j, active j b → active j a) :
    persistence next active i b ≤ persistence next active i a := by
  by_cases ha : ∃ t : ℕ, ¬active (next^[t + 1] i) a
  · have hnot : ¬active (next^[Nat.find ha + 1] i) b :=
      fun hb => Nat.find_spec ha (hsupport _ hb)
    have hb : ∃ t : ℕ, ¬active (next^[t + 1] i) b := ⟨Nat.find ha, hnot⟩
    have hle : Nat.find hb ≤ Nat.find ha := Nat.find_min' hb hnot
    simp only [persistence, dite_eq_left ha, dite_eq_left hb]
    exact_mod_cast hle
  · simp only [persistence, dite_eq_right ha]
    exact le_top

theorem survives_of_persistence_le {R A : Type*} (next : R → R) (active : R → A → Prop)
    (i : R) (a b : A) (ha : active (next i) a)
    (hle : persistence next active i a ≤ persistence next active i b) : active (next i) b := by
  by_contra hb
  have hz := (persistence_zero_iff next active i b).mpr hb
  rw [hz] at hle
  have hza : persistence next active i a = 0 := le_antisymm hle zero_le
  exact (persistence_zero_iff next active i a).mp hza ha

def precedes {R A : Type*} [LinearOrder A] (next : R → R) (active : R → A → Prop)
    (i : R) (a b : A) : Prop :=
  persistence next active i b < persistence next active i a ∨
    persistence next active i a = persistence next active i b ∧ a < b

theorem precedes_survives {R A : Type*} [LinearOrder A] (next : R → R)
    (active : R → A → Prop) (i : R) (a b : A) (hb : active (next i) b)
    (hab : precedes next active i a b) : active (next i) a := by
  apply survives_of_persistence_le next active i b a hb
  rcases hab with h | ⟨h, _⟩
  · exact le_of_lt h
  · exact h.ge

theorem precedes_step {R A : Type*} [LinearOrder A] (next : R → R)
    (active : R → A → Prop) (i : R) (a b : A)
    (ha : active (next i) a) (hb : active (next i) b) :
    precedes next active i a b ↔ precedes next active (next i) a b := by
  have hfinite : (1 : ℕ∞) ≠ ⊤ := by simp
  have heq : ∀ x y : ℕ∞, x + 1 = y + 1 ↔ x = y := by
    intro x y
    constructor
    · intro h
      exact le_antisymm ((ENat.add_le_add_iff_right hfinite).mp h.le)
        ((ENat.add_le_add_iff_right hfinite).mp h.ge)
    · intro h
      rw [h]
  unfold precedes
  rw [persistence_step next active i a ha, persistence_step next active i b hb]
  simp only [ENat.add_lt_add_iff_right hfinite, heq]

theorem precedes_of_nested_support {R A : Type*} [LinearOrder A] (next : R → R)
    (active : R → A → Prop) (i : R) (a b : A)
    (hsupport : ∀ j, active j b → active j a) (hab : a < b) : precedes next active i a b := by
  rcases lt_or_eq_of_le (persistence_mono next active i a b hsupport) with h | h
  · exact Or.inl h
  · exact Or.inr ⟨h.symm, hab⟩

noncomputable def position {R A : Type*} [LinearOrder A] (next : R → R)
    (rows : R → Finset A) (i : R) (a : A) : ℕ :=
  ((rows i).filter fun b => precedes next (fun j x => x ∈ rows j) i b a).card

theorem position_mono {R A : Type*} [LinearOrder A] (next : R → R)
    (rows : R → Finset A) (i : R) (a : A) (ha : a ∈ rows (next i)) :
    position next rows i a ≤ position next rows (next i) a := by
  apply Finset.card_le_card
  intro b hb
  obtain ⟨_, hba⟩ := Finset.mem_filter.mp hb
  have hbnext := precedes_survives next (fun j x => x ∈ rows j) i b a ha hba
  exact Finset.mem_filter.mpr ⟨hbnext,
    (precedes_step next (fun j x => x ∈ rows j) i b a hbnext ha).mp hba⟩

end ResearchMain.Laminar
