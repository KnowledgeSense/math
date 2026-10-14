import MainTheorems.Hypercomb.RootedSets

namespace ResearchMain.Hypercomb

open Classical

variable {V P T : Type*} [DecidableEq V] [DecidableEq P] [DecidableEq T]
  [Fintype P] [Fintype T]

abbrev ExcludedExtensionData (H : Finset (Finset V)) (r : V) :=
  (Excluded H r × SmallSet P × SmallSet T) ⊕ (Included H r × SmallSet T)

def excludedExtension (H : Finset (Finset V)) (r : V) : ExcludedExtensionData (P := P) (T := T) H r →
    Excluded (extensionEdges (P := P) (T := T) H r) (Sum.inr (Sum.inl none))
  | Sum.inl (S, L, U) =>
      ⟨S.val.disjSum ((L.val.map Function.Embedding.some).disjSum U.val), by
        constructor
        · apply (extension_strongIndependent H r _ _ _).mpr
          have hnone : none ∉ L.val.map Function.Embedding.some := by simp
          rw [Finset.inter_singleton_of_notMem S.property.2,
            Finset.inter_singleton_of_notMem hnone]
          simpa only [Finset.card_empty, zero_add, Finset.card_map] using
            (show StrongIndependent H S.val ∧ L.val.card ≤ 1 ∧ U.val.card ≤ 1 from
              ⟨S.property.1, L.property, U.property⟩)
        · simp⟩
  | Sum.inr (S, U) =>
      ⟨S.val.disjSum ((∅ : Finset (Option P)).disjSum U.val), by
        constructor
        · apply (extension_strongIndependent H r _ _ _).mpr
          rw [Finset.inter_singleton_of_mem S.property.2]
          simp only [Finset.card_singleton, Finset.card_empty, add_zero, Finset.empty_inter, zero_add]
          exact ⟨S.property.1, le_rfl, U.property⟩
        · simp⟩

theorem excludedExtension_injective (H : Finset (Finset V)) (r : V) :
    Function.Injective (excludedExtension (P := P) (T := T) H r) := by
  intro x y he
  have hold := congrArg (fun S => S.val.toLeft) he
  have hprivate := congrArg (fun S => S.val.toRight.toLeft.eraseNone) he
  have htooth := congrArg (fun S => S.val.toRight.toRight) he
  cases x with
  | inl x =>
    obtain ⟨S, L, U⟩ := x
    cases y with
    | inl y =>
      obtain ⟨S', L', U'⟩ := y
      have hs : S = S' := Subtype.ext (by simpa only [excludedExtension, Finset.toLeft_disjSum] using hold)
      have hl : L = L' := Subtype.ext (by
        simpa only [excludedExtension, Finset.toRight_disjSum, Finset.toLeft_disjSum,
          Finset.eraseNone_map_some] using hprivate)
      have hu : U = U' := Subtype.ext (by simpa only [excludedExtension, Finset.toRight_disjSum] using htooth)
      subst S'; subst L'; subst U'
      rfl
    | inr y =>
      obtain ⟨S', U'⟩ := y
      have hs : S.val = S'.val := by simpa only [excludedExtension, Finset.toLeft_disjSum] using hold
      exact False.elim (S.property.2 (hs.symm ▸ S'.property.2))
  | inr x =>
    obtain ⟨S, U⟩ := x
    cases y with
    | inl y =>
      obtain ⟨S', L', U'⟩ := y
      have hs : S.val = S'.val := by simpa only [excludedExtension, Finset.toLeft_disjSum] using hold
      exact False.elim (S'.property.2 (hs ▸ S.property.2))
    | inr y =>
      obtain ⟨S', U'⟩ := y
      have hs : S = S' := Subtype.ext (by simpa only [excludedExtension, Finset.toLeft_disjSum] using hold)
      have hu : U = U' := Subtype.ext (by simpa only [excludedExtension, Finset.toRight_disjSum] using htooth)
      subst S'; subst U'
      rfl

theorem excludedExtension_surjective (H : Finset (Finset V)) (r : V) :
    Function.Surjective (excludedExtension (P := P) (T := T) H r) := by
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
  have hnone : none ∉ L := by
    simpa only [L, Finset.mem_toLeft, Finset.mem_toRight] using S.property.2
  have hU : U.card ≤ 1 := by
    rw [Finset.inter_singleton_of_notMem hnone, Finset.card_empty, zero_add] at hLU
    exact hLU
  by_cases hr : r ∈ O
  · rw [Finset.inter_singleton_of_mem hr, Finset.card_singleton] at hOL
    have hL0 : L = ∅ := Finset.card_eq_zero.mp (by omega)
    refine ⟨Sum.inr (⟨O, hO, hr⟩, ⟨U, hU⟩), Subtype.ext ?_⟩
    change O.disjSum ((∅ : Finset (Option P)).disjSum U) = S.val
    rw [hsplit, hL0]
  · rw [Finset.inter_singleton_of_notMem hr, Finset.card_empty, zero_add] at hOL
    have hsmall : L.eraseNone.card ≤ 1 := (Finset.card_eraseNone_le L).trans hOL
    refine ⟨Sum.inl (⟨O, hO, hr⟩, ⟨L.eraseNone, hsmall⟩, ⟨U, hU⟩), Subtype.ext ?_⟩
    change O.disjSum ((L.eraseNone.map Function.Embedding.some).disjSum U) = S.val
    rw [Finset.map_some_eraseNone, Finset.erase_eq_of_notMem hnone, hsplit]

noncomputable def excludedExtensionEquiv (H : Finset (Finset V)) (r : V) :
    ExcludedExtensionData (P := P) (T := T) H r ≃
      Excluded (extensionEdges (P := P) (T := T) H r) (Sum.inr (Sum.inl none)) :=
  Equiv.ofBijective (excludedExtension H r)
    ⟨excludedExtension_injective H r, excludedExtension_surjective H r⟩

theorem excludedExtension_card_left (H : Finset (Finset V)) (r : V)
    (S : Excluded H r) (L : SmallSet P) (U : SmallSet T) :
    (excludedExtension H r (Sum.inl (S, L, U))).val.card = S.val.card + L.val.card + U.val.card := by
  simp only [excludedExtension, Finset.card_disjSum, Finset.card_map]
  omega

theorem excludedExtension_card_right (H : Finset (Finset V)) (r : V)
    (S : Included H r) (U : SmallSet T) :
    (excludedExtension (P := P) H r (Sum.inr (S, U))).val.card = S.val.card + U.val.card := by
  simp only [excludedExtension, Finset.card_disjSum, Finset.card_empty, zero_add]

end ResearchMain.Hypercomb
