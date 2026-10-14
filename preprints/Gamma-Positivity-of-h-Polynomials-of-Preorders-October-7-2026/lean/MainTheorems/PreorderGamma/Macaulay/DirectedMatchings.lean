import MainTheorems.PreorderGamma.Matching
import MainTheorems.PreorderGamma.Macaulay.FiniteCodes

namespace ResearchMain.PreorderGamma.Macaulay

open scoped BigOperators

variable {E : Type*} [DecidableEq E]

def leftSupport (M : Finset (E × E)) : Finset E := M.image Prod.fst

def rightSupport (M : Finset (E × E)) : Finset E := M.image Prod.snd

theorem leftSupport_mono {M N : Finset (E × E)} (h : N ⊆ M) :
    leftSupport N ⊆ leftSupport M := Finset.image_mono Prod.fst h

theorem rightSupport_mono {M N : Finset (E × E)} (h : N ⊆ M) :
    rightSupport N ⊆ rightSupport M := Finset.image_mono Prod.snd h

def matchingGraph (S T : Finset E) (f : S ≃ T) : Finset (E × E) :=
  S.attach.image fun a : S => ((a : E), (f a : E))

@[simp] theorem mem_matchingGraph {S T : Finset E} (f : S ≃ T) {e : E × E} :
    e ∈ matchingGraph S T f ↔ ∃ a : S, ((a : E), (f a : E)) = e := by
  simp [matchingGraph]

theorem leftSupport_matchingGraph (S T : Finset E) (f : S ≃ T) :
    leftSupport (matchingGraph S T f) = S := by
  ext x
  constructor
  · intro hx
    obtain ⟨e, he, hex⟩ := Finset.mem_image.mp hx
    obtain ⟨a, rfl⟩ := (mem_matchingGraph f).mp he
    exact hex ▸ a.property
  · intro hx
    exact Finset.mem_image.mpr
      ⟨(x, (f ⟨x, hx⟩ : E)), (mem_matchingGraph f).mpr ⟨⟨x, hx⟩, rfl⟩, rfl⟩

theorem rightSupport_matchingGraph (S T : Finset E) (f : S ≃ T) :
    rightSupport (matchingGraph S T f) = T := by
  ext x
  constructor
  · intro hx
    obtain ⟨e, he, hex⟩ := Finset.mem_image.mp hx
    obtain ⟨a, rfl⟩ := (mem_matchingGraph f).mp he
    exact hex ▸ (f a).property
  · intro hx
    let a : S := f.symm ⟨x, hx⟩
    exact Finset.mem_image.mpr
      ⟨((a : E), (f a : E)), (mem_matchingGraph f).mpr ⟨a, rfl⟩,
        congrArg Subtype.val (f.apply_symm_apply ⟨x, hx⟩)⟩

structure IsOrderMatching [Preorder E] (M : Finset (E × E)) : Prop where
  ordered : ∀ e ∈ M, e.1 ≤ e.2
  left_injective : Set.InjOn Prod.fst (M : Set (E × E))
  right_injective : Set.InjOn Prod.snd (M : Set (E × E))
  disjoint : Disjoint (leftSupport M) (rightSupport M)

variable [Preorder E]

theorem IsOrderMatching.subset {M N : Finset (E × E)} (hM : IsOrderMatching M)
    (hNM : N ⊆ M) : IsOrderMatching N where
  ordered e he := hM.ordered e (hNM he)
  left_injective := hM.left_injective.mono hNM
  right_injective := hM.right_injective.mono hNM
  disjoint := hM.disjoint.mono (leftSupport_mono hNM) (rightSupport_mono hNM)

theorem matchingGraph_isOrderMatching {S T : Finset E} (h : IsMatchedPair S T)
    (f : S ≃ T) (hf : ∀ a : S, (a : E) ≤ (f a : E)) :
    IsOrderMatching (matchingGraph S T f) where
  ordered e he := by
    obtain ⟨a, rfl⟩ := (mem_matchingGraph f).mp he
    exact hf a
  left_injective := by
    intro e he d hd hed
    obtain ⟨a, rfl⟩ := (mem_matchingGraph f).mp he
    obtain ⟨b, rfl⟩ := (mem_matchingGraph f).mp hd
    have hab : a = b := Subtype.ext hed
    subst b
    rfl
  right_injective := by
    intro e he d hd hed
    obtain ⟨a, rfl⟩ := (mem_matchingGraph f).mp he
    obtain ⟨b, rfl⟩ := (mem_matchingGraph f).mp hd
    have hab : a = b := f.injective (Subtype.ext hed)
    subst b
    rfl
  disjoint := by
    rw [leftSupport_matchingGraph, rightSupport_matchingGraph]
    exact h.1

noncomputable def leftProjection {M : Finset (E × E)} (hM : IsOrderMatching M) :
    M ≃ leftSupport M :=
  Equiv.ofBijective
    (fun e => ⟨e.val.1, Finset.mem_image.mpr ⟨e.val, e.property, rfl⟩⟩)
    ⟨by
      intro e d hed
      exact Subtype.ext (hM.left_injective e.property d.property (congrArg Subtype.val hed)),
     by
      intro a
      obtain ⟨e, he, hea⟩ := Finset.mem_image.mp a.property
      exact ⟨⟨e, he⟩, Subtype.ext hea⟩⟩

noncomputable def rightProjection {M : Finset (E × E)} (hM : IsOrderMatching M) :
    M ≃ rightSupport M :=
  Equiv.ofBijective
    (fun e => ⟨e.val.2, Finset.mem_image.mpr ⟨e.val, e.property, rfl⟩⟩)
    ⟨by
      intro e d hed
      exact Subtype.ext (hM.right_injective e.property d.property (congrArg Subtype.val hed)),
     by
      intro a
      obtain ⟨e, he, hea⟩ := Finset.mem_image.mp a.property
      exact ⟨⟨e, he⟩, Subtype.ext hea⟩⟩

theorem IsOrderMatching.matchedPair {M : Finset (E × E)} (hM : IsOrderMatching M) :
    IsMatchedPair (leftSupport M) (rightSupport M) := by
  let f : leftSupport M ≃ rightSupport M :=
    (leftProjection hM).symm.trans (rightProjection hM)
  refine ⟨hM.disjoint, f, ?_⟩
  intro a
  let e : M := (leftProjection hM).symm a
  have he : e.val.1 = a.val := congrArg Subtype.val ((leftProjection hM).apply_symm_apply a)
  change a.val ≤ e.val.2
  rw [← he]
  exact hM.ordered e.val e.property

theorem IsOrderMatching.card_leftSupport {M : Finset (E × E)} (hM : IsOrderMatching M) :
    (leftSupport M).card = M.card := Finset.card_image_of_injOn hM.left_injective

theorem IsOrderMatching.card_rightSupport {M : Finset (E × E)} (hM : IsOrderMatching M) :
    (rightSupport M).card = M.card := Finset.card_image_of_injOn hM.right_injective

theorem exists_orderMatching {S T : Finset E} (h : IsMatchedPair S T) :
    ∃ M : Finset (E × E), IsOrderMatching M ∧ leftSupport M = S ∧ rightSupport M = T := by
  obtain ⟨f, hf⟩ := h.2
  exact ⟨matchingGraph S T f, matchingGraph_isOrderMatching h f hf,
    leftSupport_matchingGraph S T f, rightSupport_matchingGraph S T f⟩

end ResearchMain.PreorderGamma.Macaulay
