import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Finset.Max
import Mathlib.Algebra.BigOperators.Group.Finset.Basic


/-! Independent-set counting on actual finite simple graphs. -/
namespace SphericalTreeFailures
open Finset
variable {V : Type*} [DecidableEq V] (G : SimpleGraph V)

def Independent (s : Finset V) : Prop :=
  ∀ u ∈ s, ∀ v ∈ s, ¬ G.Adj u v

noncomputable def independentSetsWithin (s : Finset V) : Finset (Finset V) := by
  classical
  exact s.powerset.filter (Independent G)

omit [DecidableEq V] in
@[simp] theorem mem_independentSetsWithin {s t : Finset V} :
    t ∈ independentSetsWithin G s ↔ t ⊆ s ∧ Independent G t := by
  classical
  simp [independentSetsWithin]

omit [DecidableEq V] in
@[simp] theorem independent_empty : Independent G ∅ := by simp [Independent]

omit [DecidableEq V] in
theorem Independent.mono {s t : Finset V} (h : Independent G s) (ht : t ⊆ s) :
    Independent G t := fun u hu v hv => h u (ht hu) v (ht hv)

@[simp] theorem independent_insert {s : Finset V} {r : V} :
    Independent G (insert r s) ↔ Independent G s ∧ ∀ v ∈ s, ¬ G.Adj r v := by
  constructor
  · intro h
    exact ⟨h.mono G (subset_insert r s), fun v hv => h r (mem_insert_self _ _) v (mem_insert_of_mem hv)⟩
  · rintro ⟨h, hr⟩ u hu v hv
    rcases mem_insert.mp hu with hur | hu
    · subst u
      rcases mem_insert.mp hv with hvr | hv
      · subst v
        exact G.irrefl
      · exact hr v hv
    · rcases mem_insert.mp hv with hvr | hv
      · subst v
        exact fun huv => hr u hu huv.symm
      · exact h u hu v hv

noncomputable def compatibleVertices (s : Finset V) (r : V) : Finset V := by
  classical
  exact (s.erase r).filter (fun v => ¬ G.Adj r v)

@[simp] theorem mem_compatibleVertices {s : Finset V} {r v : V} :
    v ∈ compatibleVertices G s r ↔ v ≠ r ∧ v ∈ s ∧ ¬ G.Adj r v := by
  classical
  simp [compatibleVertices, and_assoc]

theorem independentSetsWithin_decomposition (s : Finset V) (r : V) (hr : r ∈ s) :
    independentSetsWithin G s = independentSetsWithin G (s.erase r) ∪
      (independentSetsWithin G (compatibleVertices G s r)).image (insert r) := by
  classical
  ext t
  simp only [mem_union, mem_image, mem_independentSetsWithin]
  constructor
  · rintro ⟨ht, hi⟩
    by_cases hrt : r ∈ t
    · right
      refine ⟨t.erase r, ⟨?_, hi.mono G (erase_subset _ _)⟩, insert_erase hrt⟩
      intro v hv
      obtain ⟨hvr, hvt⟩ := mem_erase.mp hv
      exact (mem_compatibleVertices G).mpr ⟨hvr, ht hvt, hi r hrt v hvt⟩
    · left
      exact ⟨fun v hv => mem_erase.mpr ⟨fun h => hrt (h ▸ hv), ht hv⟩, hi⟩
  · rintro (⟨ht, hi⟩ | ⟨u, ⟨hu, hi⟩, rfl⟩)
    · exact ⟨Subset.trans ht (erase_subset _ _), hi⟩
    · refine ⟨?_, (independent_insert G).mpr ⟨hi, ?_⟩⟩
      · intro v hv
        rcases mem_insert.mp hv with rfl | hv
        · exact hr
        · exact ((mem_compatibleVertices G).mp (hu hv)).2.1
      · intro v hv
        exact ((mem_compatibleVertices G).mp (hu hv)).2.2

noncomputable def independentSetCount (s : Finset V) : ℕ := (independentSetsWithin G s).card
noncomputable def independentSetSizeSum (s : Finset V) : ℕ :=
  ∑ t ∈ independentSetsWithin G s, t.card
noncomputable def independenceNumber (s : Finset V) : ℕ :=
  (independentSetsWithin G s).sup Finset.card

omit [DecidableEq V] in
theorem independentSetCount_pos (s : Finset V) : 0 < independentSetCount G s := by
  apply card_pos.mpr
  exact ⟨∅, (mem_independentSetsWithin G).mpr ⟨empty_subset _, independent_empty G⟩⟩

theorem compatible_not_mem (s : Finset V) (r : V) : r ∉ compatibleVertices G s r := by simp

theorem insert_injective_on_compatible (s : Finset V) (r : V) :
    Set.InjOn (insert r) (↑(independentSetsWithin G (compatibleVertices G s r)) : Set (Finset V)) := by
  intro a ha b hb hab
  have ha' : r ∉ a := fun h => compatible_not_mem G s r (((mem_independentSetsWithin G).mp ha).1 h)
  have hb' : r ∉ b := fun h => compatible_not_mem G s r (((mem_independentSetsWithin G).mp hb).1 h)
  have := congrArg (fun t : Finset V => t.erase r) hab
  simpa [ha', hb'] using this

theorem independent_decomposition_disjoint (s : Finset V) (r : V) :
    Disjoint (independentSetsWithin G (s.erase r))
      ((independentSetsWithin G (compatibleVertices G s r)).image (insert r)) := by
  classical
  apply disjoint_left.mpr
  intro t ht hu
  obtain ⟨u, _, rfl⟩ := mem_image.mp hu
  have := ((mem_independentSetsWithin G).mp ht).1 (mem_insert_self r u)
  exact (mem_erase.mp this).1 rfl

theorem independentSetCount_recursion (s : Finset V) (r : V) (hr : r ∈ s) :
    independentSetCount G s = independentSetCount G (s.erase r) +
      independentSetCount G (compatibleVertices G s r) := by
  classical
  unfold independentSetCount
  rw [independentSetsWithin_decomposition G s r hr,
    card_union_of_disjoint (independent_decomposition_disjoint G s r),
    card_image_of_injOn (insert_injective_on_compatible G s r)]

theorem independentSetSizeSum_recursion (s : Finset V) (r : V) (hr : r ∈ s) :
    independentSetSizeSum G s = independentSetSizeSum G (s.erase r) +
      independentSetSizeSum G (compatibleVertices G s r) +
      independentSetCount G (compatibleVertices G s r) := by
  classical
  unfold independentSetSizeSum independentSetCount
  rw [independentSetsWithin_decomposition G s r hr,
    sum_union (independent_decomposition_disjoint G s r),
    sum_image (insert_injective_on_compatible G s r)]
  have he : ∀ t ∈ independentSetsWithin G (compatibleVertices G s r),
      (insert r t).card = t.card + 1 := by
    intro t ht
    apply card_insert_of_notMem
    exact fun h => compatible_not_mem G s r (((mem_independentSetsWithin G).mp ht).1 h)
  simp_rw [sum_congr rfl he, sum_add_distrib]
  simp [Nat.add_assoc]

omit [DecidableEq V] in
theorem independent_card_le (s : Finset V) {t : Finset V}
    (ht : t ⊆ s) (hi : Independent G t) : t.card ≤ independenceNumber G s := by
  exact le_sup ((mem_independentSetsWithin G).mpr ⟨ht, hi⟩)

omit [DecidableEq V] in
theorem exists_maximum_independentSet (s : Finset V) :
    ∃ t, t ⊆ s ∧ Independent G t ∧ t.card = independenceNumber G s := by
  classical
  have hn : (independentSetsWithin G s).Nonempty :=
    ⟨∅, (mem_independentSetsWithin G).mpr ⟨empty_subset _, independent_empty G⟩⟩
  obtain ⟨t, ht, he⟩ := exists_mem_eq_sup (independentSetsWithin G s) hn Finset.card
  exact ⟨t, ((mem_independentSetsWithin G).mp ht).1,
    ((mem_independentSetsWithin G).mp ht).2, he.symm⟩

theorem independenceNumber_recursion (s : Finset V) (r : V) (hr : r ∈ s) :
    independenceNumber G s = max (independenceNumber G (s.erase r))
      (independenceNumber G (compatibleVertices G s r) + 1) := by
  classical
  apply le_antisymm
  · obtain ⟨t, ht, hi, he⟩ := exists_maximum_independentSet G s
    rw [← he]
    by_cases hrt : r ∈ t
    · have hsub : t.erase r ⊆ compatibleVertices G s r := by
        intro v hv
        obtain ⟨hvr, hvt⟩ := mem_erase.mp hv
        exact (mem_compatibleVertices G).mpr ⟨hvr, ht hvt, hi r hrt v hvt⟩
      have hle := independent_card_le G _ hsub (hi.mono G (erase_subset r t))
      have hcard : t.card = (t.erase r).card + 1 := by
        rw [← card_insert_of_notMem (notMem_erase r t), insert_erase hrt]
      rw [hcard]
      exact le_trans (Nat.add_le_add_right hle 1) (le_max_right _ _)
    · exact le_trans (independent_card_le G (s.erase r)
        (fun v hv => mem_erase.mpr ⟨fun h => hrt (h ▸ hv), ht hv⟩) hi) (le_max_left _ _)
  · apply max_le
    · obtain ⟨t, ht, hi, he⟩ := exists_maximum_independentSet G (s.erase r)
      rw [← he]
      exact independent_card_le G s (Subset.trans ht (erase_subset _ _)) hi
    · obtain ⟨t, ht, hi, he⟩ := exists_maximum_independentSet G (compatibleVertices G s r)
      have hrt : r ∉ t := fun h => compatible_not_mem G s r (ht h)
      rw [← he, ← card_insert_of_notMem hrt]
      apply independent_card_le G s
      · intro v hv
        rcases mem_insert.mp hv with rfl | hv
        · exact hr
        · exact ((mem_compatibleVertices G).mp (ht hv)).2.1
      · exact (independent_insert G).mpr ⟨hi, fun v hv =>
          ((mem_compatibleVertices G).mp (ht hv)).2.2⟩

omit [DecidableEq V] in
@[simp] theorem independentSetsWithin_empty : independentSetsWithin G ∅ = {∅} := by
  classical
  ext t
  simp only [mem_independentSetsWithin, subset_empty, mem_singleton]
  constructor
  · exact And.left
  · rintro rfl
    exact ⟨rfl, independent_empty G⟩

omit [DecidableEq V] in
@[simp] theorem independentSetCount_empty : independentSetCount G ∅ = 1 := by simp [independentSetCount]
omit [DecidableEq V] in
@[simp] theorem independentSetSizeSum_empty : independentSetSizeSum G ∅ = 0 := by simp [independentSetSizeSum]
omit [DecidableEq V] in
@[simp] theorem independenceNumber_empty : independenceNumber G ∅ = 0 := by simp [independenceNumber]

end SphericalTreeFailures
