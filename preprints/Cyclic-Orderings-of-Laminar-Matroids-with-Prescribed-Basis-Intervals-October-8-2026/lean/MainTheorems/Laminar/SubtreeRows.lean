import MainTheorems.Laminar.CapacitySystems

namespace ResearchMain.Laminar

open Classical

variable {E R : Type*}

noncomputable def childFamily (family : Finset (Finset E)) : Child family → Finset (Finset E)
  | none => ∅
  | some F => properSubfamily family F.val

noncomputable def childCapacity (family : Finset (Finset E)) (ground : Finset E)
    (capacity : Finset E → ℕ) : Child family → ℕ
  | none => (ground \ maximalUnion family).card
  | some F => capacity F.val

theorem partitionRows_inter_children (family : Finset (Finset E)) (ground : Finset E)
    (rows : R → Finset E) (hrows : ∀ i, rows i ⊆ ground) :
    partitionRows (fun u i => rows i ∩ childGround family ground u) = rows := by
  funext i
  apply Finset.Subset.antisymm
  · intro e he
    obtain ⟨u, _, heu⟩ := Finset.mem_biUnion.mp he
    exact (Finset.mem_inter.mp heu).1
  · intro e he
    obtain ⟨u, heu⟩ := exists_childGround e (hrows i he)
    exact Finset.mem_biUnion.mpr ⟨u, Finset.mem_univ _, Finset.mem_inter.mpr ⟨he, heu⟩⟩

theorem window_inter_child (next : R → R) (family : Finset (Finset E)) (ground : Finset E)
    (rows : R → Finset E) (hrows : ∀ i, rows i ⊆ ground)
    (order : Ordering (partitionRows (fun u i => rows i ∩ childGround family ground u)))
    (i : R) (u : Child family) (t : ℕ) :
    window order next i t ∩ childGround family ground u =
      (rowSuffix order i t ∩ (rows i ∩ childGround family ground u)) ∪
        (rowPrefix order (next i) t ∩ (rows (next i) ∩ childGround family ground u)) := by
  have hpart := partitionRows_inter_children family ground rows hrows
  ext e
  simp only [window, Finset.mem_inter, Finset.mem_union]
  constructor
  · rintro ⟨he | he, heu⟩
    · have hr := suffix_subset order i t he
      rw [hpart] at hr
      exact Or.inl ⟨he, hr, heu⟩
    · have hr := prefix_subset order (next i) t he
      rw [hpart] at hr
      exact Or.inr ⟨he, hr, heu⟩
  · rintro (⟨he, _, heu⟩ | ⟨he, _, heu⟩)
    · exact ⟨Or.inl he, heu⟩
    · exact ⟨Or.inr he, heu⟩

theorem capacity_ordering (next : R → R) (family : Finset (Finset E))
    (capacity : Finset E → ℕ) (ground : Finset E) (c : ℕ) (rows : R → Finset E)
    (hlam : LaminarFamily family)
    (hrows : ∀ i, rows i ⊆ ground) (hsize : ∀ i, (rows i).card ≤ c)
    (hfeasible : ∀ i, Feasible family capacity (rows i)) :
    ∃ order : Ordering rows, ∀ i t, t ≤ c → Feasible family capacity (window order next i t) := by
  generalize hn : family.card = n
  induction n using Nat.strong_induction_on generalizing family ground c rows with
  | h n ih =>
    let U := Child family
    let : LinearOrder U := LinearOrder.lift' (Fintype.equivFin U) (Fintype.equivFin U).injective
    let parts : U → R → Finset E := fun u i => rows i ∩ childGround family ground u
    let capacities : U → ℕ := childCapacity family ground capacity
    let property : U → Finset E → Prop := fun u X =>
      X.card ≤ capacities u ∧ Feasible (childFamily family u) capacity X
    have hpartsize : ∀ u i, (parts u i).card ≤ capacities u := by
      intro u i
      cases u with
      | none => exact Finset.card_le_card Finset.inter_subset_right
      | some F => exact hfeasible i F.val (maximalFamily_subset family F.property)
    have hpartfeasible : ∀ u i, Feasible (childFamily family u) capacity (parts u i) := by
      intro u i G hG
      cases u with
      | none => exact False.elim (Finset.notMem_empty G hG)
      | some F =>
        exact (Finset.card_le_card
          (Finset.inter_subset_inter Finset.inter_subset_left (Finset.Subset.refl G))).trans
            (hfeasible i G (Finset.mem_filter.mp hG).1)
    have horders : ∀ u : U, ∃ order : Ordering (parts u),
        ∀ i t, t ≤ capacities u → Feasible (childFamily family u) capacity (window order next i t) := by
      intro u
      cases u with
      | none =>
        refine ⟨arbitraryOrdering (parts none), ?_⟩
        intro i t _ G hG
        exact False.elim (Finset.notMem_empty G hG)
      | some F =>
        apply ih (properSubfamily family F.val).card
          (by rw [← hn]; exact properSubfamily_card_lt (maximalFamily_subset family F.property))
          (properSubfamily family F.val) F.val (capacity F.val) (parts (some F))
          (properSubfamily_laminar hlam F.val)
        · intro i
          exact Finset.inter_subset_right
        · exact hpartsize (some F)
        · exact hpartfeasible (some F)
        · rfl
    let orders : ∀ u, Ordering (parts u) := fun u => Classical.choose (horders u)
    have hmono : ∀ u X Y, X ⊆ Y → property u Y → property u X := by
      intro u X Y hXY hY
      exact ⟨(Finset.card_le_card hXY).trans hY.1, feasible_mono hXY hY.2⟩
    have hdisj : ∀ i u v, u ≠ v → Disjoint (parts u i) (parts v i) := by
      intro i u v hne
      exact (childGround_disjoint hlam ground u v hne).mono
        Finset.inter_subset_right Finset.inter_subset_right
    have hrow : ∀ u i, property u (parts u i) := fun u i =>
      ⟨hpartsize u i, hpartfeasible u i⟩
    have hwin : ∀ u i t, t ≤ capacities u → property u (window (orders u) next i t) := by
      intro u i t ht
      exact ⟨window_card_le (orders u) next i (hpartsize u i) ht,
        Classical.choose_spec (horders u) i t ht⟩
    let order := mergedOrder next parts orders hdisj
    have hpart : partitionRows parts = rows := partitionRows_inter_children family ground rows hrows
    have hresult : ∃ order : Ordering (partitionRows parts),
        ∀ i t, t ≤ c → Feasible family capacity (window order next i t) := by
      refine ⟨order, ?_⟩
      intro i t _ F hF
      obtain ⟨G, hG, hFG⟩ := exists_maximal_superset family F hF
      let u : U := some ⟨G, hG⟩
      have hchild := merged_child_window next parts orders hdisj property hmono capacities
        hpartsize hrow hwin i u t
      rw [← window_inter_child next family ground rows hrows order i u t] at hchild
      change (window order next i t ∩ G).card ≤ capacity G ∧
        Feasible (properSubfamily family G) capacity (window order next i t ∩ G) at hchild
      by_cases hFG_eq : F = G
      · subst F
        exact hchild.1
      · have hproper : F ⊂ G := Finset.ssubset_iff_subset_ne.mpr ⟨hFG, hFG_eq⟩
        have hc := hchild.2 F (Finset.mem_filter.mpr ⟨hF, hproper⟩)
        have hinter : (window order next i t ∩ G) ∩ F = window order next i t ∩ F := by
          rw [Finset.inter_assoc, Finset.inter_eq_right.mpr hFG]
        rwa [hinter] at hc
    exact hpart ▸ hresult

end ResearchMain.Laminar
