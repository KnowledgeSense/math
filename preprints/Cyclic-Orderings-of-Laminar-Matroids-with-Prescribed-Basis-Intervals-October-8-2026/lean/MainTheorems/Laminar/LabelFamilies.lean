import MainTheorems.Laminar.RowOrder

namespace ResearchMain.Laminar

open Classical

theorem strictMono_prefix_card {m t : ℕ} (f : Fin m → ℕ) (hf : StrictMono f) (j : Fin m) :
    f j < t ↔ j.val < (Finset.univ.filter fun k => f k < t).card := by
  constructor
  · intro hj
    have hs : Finset.Iic j ⊆ Finset.univ.filter fun k => f k < t := by
      intro k hk
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, lt_of_le_of_lt (hf.monotone
        (Finset.mem_Iic.mp hk)) hj⟩
    have hc := Finset.card_le_card hs
    rw [Fin.card_Iic] at hc
    omega
  · intro hj
    by_contra hnot
    have hs : (Finset.univ.filter fun k => f k < t) ⊆ Finset.Iio j := by
      intro k hk
      apply Finset.mem_Iio.mpr
      apply lt_of_not_ge
      intro hjk
      have := hf.monotone hjk
      have hkt := (Finset.mem_filter.mp hk).2
      omega
    have hc := Finset.card_le_card hs
    rw [Fin.card_Iio] at hc
    omega

noncomputable def familyPrefix {R A : Type*} [LinearOrder A] (next : R → R)
    (rows : R → Finset A) (label : ℕ → A) (m t : ℕ) (i : R) : ℕ :=
  (Finset.univ.filter fun j : Fin m => position next rows i (label j.val) < t).card

theorem family_position_strictMono {R A : Type*} [LinearOrder A] (next : R → R)
    (rows : R → Finset A) (label : ℕ → A) (size : R → ℕ)
    (hsupport : ∀ i j, label j ∈ rows i ↔ j < size i)
    (hlabel : StrictMono label) (i : R) :
    StrictMono (fun j : Fin (size i) => position next rows i (label j.val)) := by
  intro j k hjk
  have hnest : ∀ l, label k.val ∈ rows l → label j.val ∈ rows l := by
    intro l hk
    exact (hsupport l j.val).mpr (lt_trans hjk ((hsupport l k.val).mp hk))
  have hpred := precedes_of_nested_support next (fun l x => x ∈ rows l) i
    (label j.val) (label k.val) hnest (hlabel hjk)
  obtain ⟨a, ha⟩ := rowOrder_surjective next rows i (label j.val)
    ((hsupport i j.val).mpr j.isLt)
  obtain ⟨b, hb⟩ := rowOrder_surjective next rows i (label k.val)
    ((hsupport i k.val).mpr k.isLt)
  change position next rows i (label j.val) < position next rows i (label k.val)
  rw [← ha, ← hb] at hpred ⊢
  rw [position_rowOrder, position_rowOrder]
  exact (rowOrder_precedes_iff next rows i a b).mp hpred

theorem familyPrefix_le {R A : Type*} [LinearOrder A] (next : R → R)
    (rows : R → Finset A) (label : ℕ → A) (m t : ℕ) (i : R) :
    familyPrefix next rows label m t i ≤ m := by
  exact (Finset.card_filter_le _ _).trans_eq (Finset.card_univ.trans (Fintype.card_fin m))

theorem familyPrefix_iff {R A : Type*} [LinearOrder A] (next : R → R)
    (rows : R → Finset A) (label : ℕ → A) (size : R → ℕ)
    (hsupport : ∀ i j, label j ∈ rows i ↔ j < size i)
    (hlabel : StrictMono label) (i : R) (t : ℕ) (j : Fin (size i)) :
    position next rows i (label j.val) < t ↔
      j.val < familyPrefix next rows label (size i) t i :=
  strictMono_prefix_card _ (family_position_strictMono next rows label size hsupport hlabel i) j

theorem familyPrefix_transition {R A : Type*} [LinearOrder A] (next : R → R)
    (rows : R → Finset A) (label : ℕ → A) (size : R → ℕ)
    (hsupport : ∀ i j, label j ∈ rows i ↔ j < size i)
    (hlabel : StrictMono label) (i : R) (t : ℕ) :
    min (familyPrefix next rows label (size (next i)) t (next i)) (size i) ≤
      familyPrefix next rows label (size i) t i := by
  by_contra h
  let a := familyPrefix next rows label (size i) t i
  have hm : a < size i := by omega
  have hb : a < familyPrefix next rows label (size (next i)) t (next i) := by omega
  have hnext : a < size (next i) := lt_of_lt_of_le hb
    (familyPrefix_le next rows label _ t (next i))
  have hposnext := (familyPrefix_iff next rows label size hsupport hlabel (next i) t
    ⟨a, hnext⟩).mpr hb
  have hpos := position_mono next rows i (label a) ((hsupport (next i) a).mpr hnext)
  have hposa := (familyPrefix_iff next rows label size hsupport hlabel i t ⟨a, hm⟩).mp
    (lt_of_le_of_lt hpos hposnext)
  exact (lt_irrefl a) hposa

end ResearchMain.Laminar
