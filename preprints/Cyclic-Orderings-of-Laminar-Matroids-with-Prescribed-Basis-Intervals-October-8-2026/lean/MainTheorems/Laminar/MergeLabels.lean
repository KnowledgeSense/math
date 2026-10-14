import MainTheorems.Laminar.OrderedRows
import Mathlib.Data.Finset.Union

namespace ResearchMain.Laminar

open Classical

variable {R E U : Type*} [Fintype U] [LinearOrder U]

noncomputable def partitionRows (parts : U → R → Finset E) (i : R) : Finset E :=
  Finset.univ.biUnion fun u => parts u i

noncomputable def mergeLabels (parts : U → R → Finset E) (i : R) : Finset (U ×ₗ ℕ) :=
  Finset.univ.biUnion fun u => (Finset.range (parts u i).card).image fun j => toLex (u, j)

theorem mem_mergeLabels (parts : U → R → Finset E) (i : R) (u : U) (j : ℕ) :
    toLex (u, j) ∈ mergeLabels parts i ↔ j < (parts u i).card := by
  simp only [mergeLabels, Finset.mem_biUnion, Finset.mem_univ, true_and, Finset.mem_image,
    Finset.mem_range, toLex_inj, Prod.mk.injEq]
  constructor
  · rintro ⟨v, l, hl, hv, rfl⟩
    subst v
    exact hl
  · intro hj
    exact ⟨u, j, hj, rfl, rfl⟩

theorem mergeLabel_bound (parts : U → R → Finset E) (i : R) (a : mergeLabels parts i) :
    (ofLex a.val).2 < (parts (ofLex a.val).1 i).card := by
  exact (mem_mergeLabels parts i _ _).mp a.property

noncomputable def mergeValue (parts : U → R → Finset E) (orders : ∀ u, Ordering (parts u))
    (i : R) (a : mergeLabels parts i) : partitionRows parts i :=
  ⟨(orders (ofLex a.val).1 i ⟨(ofLex a.val).2, mergeLabel_bound parts i a⟩).val,
    Finset.mem_biUnion.mpr ⟨_, Finset.mem_univ _,
      (orders (ofLex a.val).1 i ⟨(ofLex a.val).2, mergeLabel_bound parts i a⟩).property⟩⟩

theorem mergeValue_injective (parts : U → R → Finset E)
    (orders : ∀ u, Ordering (parts u))
    (hdisj : ∀ i u v, u ≠ v → Disjoint (parts u i) (parts v i)) (i : R) :
    Function.Injective (mergeValue parts orders i) := by
  intro a b hab
  have he : (orders (ofLex a.val).1 i ⟨(ofLex a.val).2, mergeLabel_bound parts i a⟩).val =
      (orders (ofLex b.val).1 i ⟨(ofLex b.val).2, mergeLabel_bound parts i b⟩).val :=
    congrArg Subtype.val hab
  have hu : (ofLex a.val).1 = (ofLex b.val).1 := by
    by_contra hne
    exact Finset.disjoint_left.mp (hdisj i _ _ hne)
      (orders (ofLex a.val).1 i ⟨(ofLex a.val).2, mergeLabel_bound parts i a⟩).property
      (he ▸ (orders (ofLex b.val).1 i ⟨(ofLex b.val).2, mergeLabel_bound parts i b⟩).property)
  cases a with | mk a hamem =>
    cases b with | mk b hbmem =>
      cases a using Lex.rec
      cases b using Lex.rec
      rename_i aa bb
      rcases aa with ⟨u, j⟩
      rcases bb with ⟨v, l⟩
      change u = v at hu
      subst v
      have hjl : j = l := congrArg Fin.val ((orders u i).injective (Subtype.ext he))
      subst l
      rfl

theorem mergeValue_surjective (parts : U → R → Finset E)
    (orders : ∀ u, Ordering (parts u)) (i : R) : Function.Surjective (mergeValue parts orders i) := by
  intro e
  obtain ⟨u, _, heu⟩ := Finset.mem_biUnion.mp e.property
  let j := (orders u i).symm ⟨e.val, heu⟩
  refine ⟨⟨toLex (u, j.val), (mem_mergeLabels parts i u j.val).mpr j.isLt⟩, ?_⟩
  apply Subtype.ext
  change (orders u i j).val = e.val
  exact congrArg Subtype.val ((orders u i).apply_symm_apply ⟨e.val, heu⟩)

noncomputable def mergeEquiv (parts : U → R → Finset E)
    (orders : ∀ u, Ordering (parts u))
    (hdisj : ∀ i u v, u ≠ v → Disjoint (parts u i) (parts v i)) (i : R) :
    mergeLabels parts i ≃ partitionRows parts i :=
  Equiv.ofBijective (mergeValue parts orders i)
    ⟨mergeValue_injective parts orders hdisj i, mergeValue_surjective parts orders i⟩

theorem mergeLabels_card (parts : U → R → Finset E)
    (orders : ∀ u, Ordering (parts u))
    (hdisj : ∀ i u v, u ≠ v → Disjoint (parts u i) (parts v i)) (i : R) :
    (mergeLabels parts i).card = (partitionRows parts i).card := by
  simpa only [Fintype.card_coe] using Fintype.card_congr (mergeEquiv parts orders hdisj i)

theorem fin_cast_symm_val {m n : ℕ} (h : m = n) (j : Fin n) :
    ((Equiv.cast (congrArg Fin h)).symm j).val = j.val := by
  cases h
  rfl

noncomputable def mergedOrder (next : R → R) (parts : U → R → Finset E)
    (orders : ∀ u, Ordering (parts u))
    (hdisj : ∀ i u v, u ≠ v → Disjoint (parts u i) (parts v i)) :
    Ordering (partitionRows parts) := fun i =>
  (Equiv.cast (congrArg Fin (mergeLabels_card parts orders hdisj i).symm)).trans
    ((sortedRowEquiv next (mergeLabels parts) i).trans (mergeEquiv parts orders hdisj i))

theorem mergedOrder_position (next : R → R) (parts : U → R → Finset E)
    (orders : ∀ u, Ordering (parts u))
    (hdisj : ∀ i u v, u ≠ v → Disjoint (parts u i) (parts v i)) (i : R)
    (a : mergeLabels parts i) :
    (((mergedOrder next parts orders hdisj i).symm (mergeEquiv parts orders hdisj i a)).val) =
      position next (mergeLabels parts) i a.val := by
  simp only [mergedOrder, Equiv.symm_trans_apply, Equiv.symm_apply_apply]
  rw [← sortedRowEquiv_position]
  exact fin_cast_symm_val (mergeLabels_card parts orders hdisj i).symm _

end ResearchMain.Laminar
