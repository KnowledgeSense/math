import MainTheorems.Laminar.CyclicWindows

namespace ResearchMain.Laminar

open Classical

theorem flatten_injective {k r : ℕ} {E : Type*} {rows : Fin k → Finset E}
    (order : Ordering rows) (hcard : ∀ i, (rows i).card = r)
    (hdisj : ∀ i j, i ≠ j → Disjoint (rows i) (rows j)) :
    Function.Injective (flatten order hcard) := by
  intro a b hab
  unfold flatten at hab
  have hrow : indexRow a = indexRow b := by
    by_contra hne
    have ha := (blockOrders order hcard (indexRow a) (indexColumn a)).property
    have hb := (blockOrders order hcard (indexRow b) (indexColumn b)).property
    exact Finset.disjoint_left.mp (hdisj _ _ hne) ha (hab.symm ▸ hb)
  rw [hrow] at hab
  have hcol : indexColumn a = indexColumn b :=
    (blockOrders order hcard (indexRow b)).injective (Subtype.ext hab)
  rw [← blockIndex_row_column a, ← blockIndex_row_column b, hrow, hcol]

theorem flatten_mem_ground {k r : ℕ} {E : Type*} {rows : Fin k → Finset E}
    (M : Matroid E) (order : Ordering rows) (hcard : ∀ i, (rows i).card = r)
    (hbases : ∀ i, M.IsBase (rows i : Set E)) (s : Fin (k * r)) :
    flatten order hcard s ∈ M.E :=
  (hbases (indexRow s)).subset_ground
    (blockOrders order hcard (indexRow s) (indexColumn s)).property

noncomputable def flattenEquiv {k r : ℕ} {E : Type*} {rows : Fin k → Finset E}
    (M : Matroid E) (order : Ordering rows) (hcard : ∀ i, (rows i).card = r)
    (hbases : ∀ i, M.IsBase (rows i : Set E))
    (hdisj : ∀ i j, i ≠ j → Disjoint (rows i) (rows j))
    (hcover : ((Finset.univ.biUnion rows : Finset E) : Set E) = M.E) : Fin (k * r) ≃ M.E :=
  Equiv.ofBijective (fun s => ⟨flatten order hcard s, flatten_mem_ground M order hcard hbases s⟩)
    ⟨fun _ _ h => flatten_injective order hcard hdisj (congrArg Subtype.val h),
      fun e => by
        have he : e.val ∈ Finset.univ.biUnion rows := by
          change e.val ∈ ((Finset.univ.biUnion rows : Finset E) : Set E)
          rw [hcover]
          exact e.property
        obtain ⟨i, _, hei⟩ := Finset.mem_biUnion.mp he
        obtain ⟨j, hj⟩ := (blockOrders order hcard i).surjective ⟨e.val, hei⟩
        refine ⟨blockIndex i j, Subtype.ext ?_⟩
        change flatten order hcard (blockIndex i j) = e.val
        rw [flatten_block]
        exact congrArg Subtype.val hj⟩

theorem prescribed_cyclic_basis_ordering {E : Type*} (M : Matroid E) (hlam : IsLaminar M)
    {k r : ℕ} (hk : 1 ≤ k) (hrank : M.eRank = (r : ℕ∞)) (rows : Fin k → Finset E)
    (hbases : ∀ i, M.IsBase (rows i : Set E))
    (hdisj : ∀ i j, i ≠ j → Disjoint (rows i) (rows j))
    (hcover : ((Finset.univ.biUnion rows : Finset E) : Set E) = M.E) :
    ∃ f : Fin (k * r) ≃ M.E,
      (∀ i, ∃ b : Fin r ≃ rows i, ∀ j, (f (blockIndex i j)).val = (b j).val) ∧
      ∀ s, M.IsBase (cyclicWindow (fun p => (f p).val) s r : Set E) := by
  obtain ⟨order, hwin⟩ := prescribed_basis_blocks M hlam hk hrank rows hbases hdisj hcover
  have hcard : ∀ i, (rows i).card = r := by
    intro i
    have he := (hbases i).encard_eq_eRank
    rw [Set.encard_coe_eq_coe_finsetCard, hrank] at he
    exact_mod_cast he
  refine ⟨flattenEquiv M order hcard hbases hdisj hcover, ?_, ?_⟩
  · intro i
    exact ⟨blockOrders order hcard i, flatten_block order hcard i⟩
  · intro s
    change M.IsBase (cyclicWindow (flatten order hcard) s r : Set E)
    rw [cyclicWindow_eq_window]
    exact hwin (indexRow s) (indexColumn s).val (Nat.le_of_lt (indexColumn s).isLt)

end ResearchMain.Laminar
