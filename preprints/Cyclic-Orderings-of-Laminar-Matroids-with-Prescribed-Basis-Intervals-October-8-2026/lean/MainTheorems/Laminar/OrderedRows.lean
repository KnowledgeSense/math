import MainTheorems.Laminar.LabelFamilies

namespace ResearchMain.Laminar

open Classical

abbrev Ordering {R E : Type*} (rows : R → Finset E) :=
  ∀ i, Fin (rows i).card ≃ rows i

noncomputable def rowPrefix {R E : Type*} {rows : R → Finset E} (order : Ordering rows)
    (i : R) (t : ℕ) : Finset E :=
  (Finset.univ.filter fun j : Fin (rows i).card => j.val < t).image fun j => (order i j).val

noncomputable def rowSuffix {R E : Type*} {rows : R → Finset E} (order : Ordering rows)
    (i : R) (t : ℕ) : Finset E :=
  (Finset.univ.filter fun j : Fin (rows i).card => t ≤ j.val).image fun j => (order i j).val

noncomputable def window {R E : Type*} {rows : R → Finset E} (order : Ordering rows)
    (next : R → R) (i : R) (t : ℕ) : Finset E := rowSuffix order i t ∪ rowPrefix order (next i) t

theorem ordering_injective {R E : Type*} {rows : R → Finset E} (order : Ordering rows)
    (i : R) : Function.Injective (fun j => (order i j).val) :=
  Subtype.val_injective.comp (order i).injective

theorem prefix_subset {R E : Type*} {rows : R → Finset E} (order : Ordering rows)
    (i : R) (t : ℕ) : rowPrefix order i t ⊆ rows i := by
  intro e he
  obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp he
  exact (order i j).property

theorem suffix_subset {R E : Type*} {rows : R → Finset E} (order : Ordering rows)
    (i : R) (t : ℕ) : rowSuffix order i t ⊆ rows i := by
  intro e he
  obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp he
  exact (order i j).property

theorem mem_prefix {R E : Type*} {rows : R → Finset E} (order : Ordering rows)
    (i : R) (t : ℕ) (j : Fin (rows i).card) : (order i j).val ∈ rowPrefix order i t ↔ j.val < t := by
  simp only [rowPrefix, Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨k, hk, heq⟩
    exact ordering_injective order i heq ▸ hk
  · intro hj
    exact ⟨j, hj, rfl⟩

theorem mem_suffix {R E : Type*} {rows : R → Finset E} (order : Ordering rows)
    (i : R) (t : ℕ) (j : Fin (rows i).card) : (order i j).val ∈ rowSuffix order i t ↔ t ≤ j.val := by
  simp only [rowSuffix, Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨k, hk, heq⟩
    exact ordering_injective order i heq ▸ hk
  · intro hj
    exact ⟨j, hj, rfl⟩

theorem mem_prefix_iff_position {R E : Type*} {rows : R → Finset E} (order : Ordering rows)
    (i : R) (t : ℕ) (e : rows i) :
    e.val ∈ rowPrefix order i t ↔ ((order i).symm e).val < t := by
  simpa only [Equiv.apply_symm_apply] using mem_prefix order i t ((order i).symm e)

theorem mem_suffix_iff_position {R E : Type*} {rows : R → Finset E} (order : Ordering rows)
    (i : R) (t : ℕ) (e : rows i) :
    e.val ∈ rowSuffix order i t ↔ t ≤ ((order i).symm e).val := by
  simpa only [Equiv.apply_symm_apply] using mem_suffix order i t ((order i).symm e)

theorem fin_prefix_card (m t : ℕ) :
    (Finset.univ.filter fun j : Fin m => j.val < t).card = min m t := by
  rw [← Finset.card_range (min m t)]
  apply Finset.card_bij (fun j _ => j.val)
  · intro j hj
    exact Finset.mem_range.mpr (lt_min j.isLt (Finset.mem_filter.mp hj).2)
  · intro a _ b _ hab
    exact Fin.ext hab
  · intro a ha
    have ham := lt_of_lt_of_le (Finset.mem_range.mp ha) (min_le_left m t)
    have hat := lt_of_lt_of_le (Finset.mem_range.mp ha) (min_le_right m t)
    exact ⟨⟨a, ham⟩, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hat⟩, rfl⟩

theorem prefix_card {R E : Type*} {rows : R → Finset E} (order : Ordering rows)
    (i : R) (t : ℕ) : (rowPrefix order i t).card = min (rows i).card t := by
  rw [rowPrefix, Finset.card_image_of_injective _ (ordering_injective order i), fin_prefix_card]

theorem suffix_card {R E : Type*} {rows : R → Finset E} (order : Ordering rows)
    (i : R) (t : ℕ) : (rowSuffix order i t).card = (rows i).card - t := by
  rw [rowSuffix, Finset.card_image_of_injective _ (ordering_injective order i)]
  have hc := Finset.card_filter_add_card_filter_not (s := (Finset.univ : Finset (Fin (rows i).card)))
    (p := fun j => j.val < t)
  simp only [not_lt, Finset.card_univ, Fintype.card_fin, fin_prefix_card] at hc
  omega

theorem prefix_mono {R E : Type*} {rows : R → Finset E} (order : Ordering rows)
    (i : R) {a b : ℕ} (hab : a ≤ b) : rowPrefix order i a ⊆ rowPrefix order i b := by
  intro e he
  obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp he
  exact (mem_prefix order i b j).mpr (lt_of_lt_of_le (Finset.mem_filter.mp hj).2 hab)

theorem suffix_eq_empty {R E : Type*} {rows : R → Finset E} (order : Ordering rows)
    (i : R) {t : ℕ} (ht : (rows i).card ≤ t) : rowSuffix order i t = ∅ := by
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro e he
  obtain ⟨j, hj, _⟩ := Finset.mem_image.mp he
  have := (Finset.mem_filter.mp hj).2
  omega

theorem window_card_le {R E : Type*} {rows : R → Finset E} (order : Ordering rows)
    (next : R → R) (i : R) {c t : ℕ} (hi : (rows i).card ≤ c) (ht : t ≤ c) :
    (window order next i t).card ≤ c := by
  have h := Finset.card_union_le (rowSuffix order i t) (rowPrefix order (next i) t)
  rw [suffix_card, prefix_card] at h
  have hmin := min_le_right (rows (next i)).card t
  unfold window
  omega

end ResearchMain.Laminar
