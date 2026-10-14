import ASR312.PermutationRestriction

namespace ASR312

noncomputable def paddedRowSupport {r : ℕ} (s : Finset (Fin r)) (m : ℕ) : Finset (Fin (r+m)) :=
  s.map (Fin.castAddEmb m) ∪ Finset.univ.map (Fin.natAddEmb r)

theorem paddedRowSupport_card {r : ℕ} (s : Finset (Fin r)) (m : ℕ) :
    (paddedRowSupport s m).card = s.card + m := by
  classical
  unfold paddedRowSupport
  rw [Finset.card_union_of_disjoint]
  · simp
  · apply Finset.disjoint_left.mpr
    intro x hx hy
    obtain ⟨i,_,rfl⟩ := Finset.mem_map.mp hx
    obtain ⟨j,_,he⟩ := Finset.mem_map.mp hy
    have hv := congrArg Fin.val he
    change r + j.val = i.val at hv
    have hi := i.isLt
    omega

theorem paddedRowSupport_mem {r : ℕ} (s : Finset (Fin r)) (m : ℕ) (i : Fin r) :
    Fin.castAdd m i ∈ paddedRowSupport s m ↔ i ∈ s := by
  classical
  unfold paddedRowSupport
  rw [Finset.mem_union]
  have hleft : Fin.castAdd m i ∈ s.map (Fin.castAddEmb m) ↔ i ∈ s := by
    simp only [Finset.mem_map]
    constructor
    · rintro ⟨x,hx,he⟩
      have hxj : x = i := (Fin.castAddEmb m).injective he
      simpa [hxj] using hx
    · exact fun h => ⟨i,h,rfl⟩
  have hright : Fin.castAdd m i ∉ Finset.univ.map (Fin.natAddEmb r) := by
    intro h
    obtain ⟨j,_,he⟩ := Finset.mem_map.mp h
    have hv := congrArg Fin.val he
    change r + j.val = i.val at hv
    have hi := i.isLt
    omega
  simp [hleft,hright]

noncomputable def rowSupportRectangle {r k : ℕ} (s : Finset (Fin r)) (hs : s.card ≤ k) :
    Rectangle r k :=
  permutationRestriction (by omega : r ≤ r+(k-s.card))
    (by have hc := Finset.card_le_univ s; simp only [Fintype.card_fin] at hc; omega)
    (subsetShuffle (paddedRowSupport s (k-s.card)))

theorem rowSupportRectangle_asr {r k : ℕ} (s : Finset (Fin r)) (hs : s.card ≤ k) :
    IsASR (rowSupportRectangle s hs) := permutationRestriction_asr _ _ _

theorem rowSupportRectangle_extendable {r k : ℕ} (s : Finset (Fin r)) (hs : s.card ≤ k) :
    ExtendablyAvoids312 (rowSupportRectangle s hs) :=
  permutationRestriction_extendable _ _ _ (subsetShuffle_avoids _)

theorem rowSupportRectangle_nonempty_iff {r k : ℕ} (s : Finset (Fin r))
    (hs : s.card ≤ k) (i : Fin r) :
    (∃ j, rowSupportRectangle s hs i j ≠ .zero) ↔ i ∈ s := by
  unfold rowSupportRectangle
  rw [permutationRestriction_row_nonempty]
  change (subsetShuffleFun (paddedRowSupport s (k-s.card)) _).val < k ↔ i ∈ s
  have hc : (paddedRowSupport s (k-s.card)).card = k := by
    rw [paddedRowSupport_card]; omega
  have hh := subsetShuffleFun_lt_iff (paddedRowSupport s (k-s.card))
    (Fin.castLE (by omega : r ≤ r+(k-s.card)) i)
  rw [hc] at hh
  rw [hh]
  have hi : Fin.castLE (by omega : r ≤ r+(k-s.card)) i = Fin.castAdd (k-s.card) i := Fin.ext rfl
  rw [hi]
  exact paddedRowSupport_mem s _ i

theorem rowSupportRectangle_nonemptyRows {r k : ℕ} (s : Finset (Fin r)) (hs : s.card ≤ k) :
    nonemptyRows (rowSupportRectangle s hs) = s.card := by
  classical
  unfold nonemptyRows
  congr 1
  ext i
  simp only [Finset.mem_filter,Finset.mem_univ,true_and,rowSupportRectangle_nonempty_iff]

theorem rowSupportRectangle_emptyFirstRow {r k : ℕ} (s : Finset (Fin (r+1)))
    (hs : s.card ≤ k) (hz : (0 : Fin (r+1)) ∉ s) (j : Fin k) :
    rowSupportRectangle s hs 0 j = .zero := by
  by_contra h
  exact hz ((rowSupportRectangle_nonempty_iff s hs 0).mp ⟨j,h⟩)

end ASR312
