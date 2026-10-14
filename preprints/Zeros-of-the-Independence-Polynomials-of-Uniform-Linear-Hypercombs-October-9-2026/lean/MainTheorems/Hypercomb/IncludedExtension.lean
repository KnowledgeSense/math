import MainTheorems.Hypercomb.RootedSets

namespace ResearchMain.Hypercomb

open Classical

variable {V P T : Type*} [DecidableEq V] [DecidableEq P] [DecidableEq T]
  [Fintype P] [Fintype T]

def includedExtension (H : Finset (Finset V)) (r : V) (S : Excluded H r) :
    Included (extensionEdges (P := P) (T := T) H r) (Sum.inr (Sum.inl none)) :=
  ⟨S.val.disjSum (({none} : Finset (Option P)).disjSum (∅ : Finset T)), by
    constructor
    · apply (extension_strongIndependent H r _ _ _).mpr
      rw [Finset.inter_singleton_of_notMem S.property.2]
      simp only [Finset.card_empty, Finset.card_singleton, Finset.inter_self, zero_add, add_zero]
      exact ⟨S.property.1, le_rfl, le_rfl⟩
    · simp⟩

theorem includedExtension_injective (H : Finset (Finset V)) (r : V) :
    Function.Injective (includedExtension (P := P) (T := T) H r) := by
  intro S U he
  have hold := congrArg (fun S => S.val.toLeft) he
  exact Subtype.ext (by simpa only [includedExtension, Finset.toLeft_disjSum] using hold)

theorem includedExtension_surjective (H : Finset (Finset V)) (r : V) :
    Function.Surjective (includedExtension (P := P) (T := T) H r) := by
  intro S
  let O := S.val.toLeft
  let L := S.val.toRight.toLeft
  let U := S.val.toRight.toRight
  have hsplit : S.val = O.disjSum (L.disjSum U) := by
    dsimp only [O, L, U]
    rw [Finset.toLeft_disjSum_toRight, Finset.toLeft_disjSum_toRight]
  have hstrong := S.property.1
  rw [hsplit] at hstrong
  obtain ⟨hO, hOL, hLU⟩ := (extension_strongIndependent H r O L U).mp hstrong
  have hnone : none ∈ L := by
    simpa only [L, Finset.mem_toLeft, Finset.mem_toRight] using S.property.2
  have hLcard : L.card ≤ 1 := by omega
  have hL : L = {none} := by
    ext x
    constructor
    · intro hx
      exact Finset.mem_singleton.mpr (Finset.card_le_one.mp hLcard x hx none hnone)
    · intro hx
      rw [Finset.mem_singleton.mp hx]
      exact hnone
  rw [hL, Finset.inter_self, Finset.card_singleton] at hLU
  have hU : U = ∅ := Finset.card_eq_zero.mp (by omega)
  have hr : r ∉ O := by
    intro hmem
    rw [Finset.inter_singleton_of_mem hmem, Finset.card_singleton, hL, Finset.card_singleton] at hOL
    omega
  refine ⟨⟨O, hO, hr⟩, Subtype.ext ?_⟩
  change O.disjSum (({none} : Finset (Option P)).disjSum (∅ : Finset T)) = S.val
  rw [hsplit, hL, hU]

noncomputable def includedExtensionEquiv (H : Finset (Finset V)) (r : V) :
    Excluded H r ≃ Included (extensionEdges (P := P) (T := T) H r) (Sum.inr (Sum.inl none)) :=
  Equiv.ofBijective (includedExtension H r)
    ⟨includedExtension_injective H r, includedExtension_surjective H r⟩

theorem includedExtension_card (H : Finset (Finset V)) (r : V) (S : Excluded H r) :
    (includedExtension (P := P) (T := T) H r S).val.card = S.val.card + 1 := by
  simp only [includedExtension, Finset.card_disjSum, Finset.card_empty, Finset.card_singleton, add_zero]

end ResearchMain.Hypercomb
