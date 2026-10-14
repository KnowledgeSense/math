import MainTheorems.Laminar.CyclicIndices

namespace ResearchMain.Laminar

open Classical

theorem fin_cast_val {m n : ℕ} (h : m = n) (j : Fin m) :
    ((Equiv.cast (congrArg Fin h)) j).val = j.val := by
  cases h
  rfl

noncomputable def blockOrders {k r : ℕ} {E : Type*} {rows : Fin k → Finset E}
    (order : Ordering rows) (hcard : ∀ i, (rows i).card = r) (i : Fin k) : Fin r ≃ rows i :=
  (Equiv.cast (congrArg Fin (hcard i).symm)).trans (order i)

theorem blockOrders_position {k r : ℕ} {E : Type*} {rows : Fin k → Finset E}
    (order : Ordering rows) (hcard : ∀ i, (rows i).card = r) (i : Fin k) (j : Fin r) :
    ((order i).symm (blockOrders order hcard i j)).val = j.val := by
  simp only [blockOrders, Equiv.trans_apply, Equiv.symm_apply_apply]
  exact fin_cast_val (hcard i).symm j

theorem mem_prefix_block {k r : ℕ} {E : Type*} {rows : Fin k → Finset E}
    (order : Ordering rows) (hcard : ∀ i, (rows i).card = r) (i : Fin k) (t : ℕ) (j : Fin r) :
    (blockOrders order hcard i j).val ∈ rowPrefix order i t ↔ j.val < t := by
  rw [mem_prefix_iff_position, blockOrders_position]

theorem mem_suffix_block {k r : ℕ} {E : Type*} {rows : Fin k → Finset E}
    (order : Ordering rows) (hcard : ∀ i, (rows i).card = r) (i : Fin k) (t : ℕ) (j : Fin r) :
    (blockOrders order hcard i j).val ∈ rowSuffix order i t ↔ t ≤ j.val := by
  rw [mem_suffix_iff_position, blockOrders_position]

noncomputable def flatten {k r : ℕ} {E : Type*} {rows : Fin k → Finset E}
    (order : Ordering rows) (hcard : ∀ i, (rows i).card = r) (s : Fin (k * r)) : E :=
  (blockOrders order hcard (indexRow s) (indexColumn s)).val

theorem flatten_block {k r : ℕ} {E : Type*} {rows : Fin k → Finset E}
    (order : Ordering rows) (hcard : ∀ i, (rows i).card = r) (i : Fin k) (j : Fin r) :
    flatten order hcard (blockIndex i j) = (blockOrders order hcard i j).val := by
  unfold flatten
  rw [(blockIndex_coordinates i j).1, (blockIndex_coordinates i j).2]

noncomputable def cyclicWindow {N : ℕ} {E : Type*} (f : Fin N → E) (s : Fin N) (r : ℕ) : Finset E :=
  (Finset.range r).image fun j => f (cyclicIndex s j)

theorem cyclicWindow_block {k r : ℕ} {E : Type*} {rows : Fin k → Finset E}
    (order : Ordering rows) (hcard : ∀ i, (rows i).card = r) (i : Fin k) (t : Fin r) :
    cyclicWindow (flatten order hcard) (blockIndex i t) r = window order nextRow i t.val := by
  ext e
  constructor
  · intro he
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp he
    let j : Fin r := ⟨a, Finset.mem_range.mp ha⟩
    have hindex := cyclicIndex_block i t j
    change cyclicIndex (blockIndex i t) a = _ at hindex
    rw [hindex]
    split
    · rename_i h
      rw [flatten_block]
      exact Finset.mem_union_left _ ((mem_suffix_block order hcard i t.val _).mpr
        (by change t.val ≤ t.val + j.val; omega))
    · rename_i h
      rw [flatten_block]
      exact Finset.mem_union_right _ ((mem_prefix_block order hcard (nextRow i) t.val _).mpr
        (by change t.val + j.val - r < t.val; have := j.isLt; omega))
  · intro he
    rcases Finset.mem_union.mp he with he | he
    · have hem := suffix_subset order i t.val he
      obtain ⟨j, hj⟩ := (blockOrders order hcard i).surjective ⟨e, hem⟩
      have heq : (blockOrders order hcard i j).val = e := congrArg Subtype.val hj
      have hjt := (mem_suffix_block order hcard i t.val j).mp (heq.symm ▸ he)
      let a : Fin r := ⟨j.val - t.val, by have := j.isLt; omega⟩
      have hcarry : t.val + a.val < r := by dsimp [a]; have := j.isLt; omega
      have hcol : (⟨t.val + a.val, hcarry⟩ : Fin r) = j := by
        apply Fin.ext
        dsimp [a]
        omega
      apply Finset.mem_image.mpr
      refine ⟨a.val, Finset.mem_range.mpr a.isLt, ?_⟩
      rw [cyclicIndex_block, dite_eq_left hcarry, hcol, flatten_block]
      exact heq
    · have hem := prefix_subset order (nextRow i) t.val he
      obtain ⟨j, hj⟩ := (blockOrders order hcard (nextRow i)).surjective ⟨e, hem⟩
      have heq : (blockOrders order hcard (nextRow i) j).val = e := congrArg Subtype.val hj
      have hjt := (mem_prefix_block order hcard (nextRow i) t.val j).mp (heq.symm ▸ he)
      let a : Fin r := ⟨r - t.val + j.val, by have := t.isLt; omega⟩
      have hcarry : ¬t.val + a.val < r := by dsimp [a]; have := t.isLt; omega
      have hcol : (⟨t.val + a.val - r, by have := t.isLt; have := a.isLt; omega⟩ : Fin r) = j := by
        apply Fin.ext
        dsimp [a]
        have := t.isLt
        omega
      apply Finset.mem_image.mpr
      refine ⟨a.val, Finset.mem_range.mpr a.isLt, ?_⟩
      rw [cyclicIndex_block, dite_eq_right hcarry, hcol, flatten_block]
      exact heq

theorem cyclicWindow_eq_window {k r : ℕ} {E : Type*} {rows : Fin k → Finset E}
    (order : Ordering rows) (hcard : ∀ i, (rows i).card = r) (s : Fin (k * r)) :
    cyclicWindow (flatten order hcard) s r = window order nextRow (indexRow s) (indexColumn s).val := by
  rw [← blockIndex_row_column s] at ⊢
  rw [cyclicWindow_block, (blockIndex_coordinates (indexRow s) (indexColumn s)).1,
    (blockIndex_coordinates (indexRow s) (indexColumn s)).2]

end ResearchMain.Laminar
