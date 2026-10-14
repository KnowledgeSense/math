import MainTheorems.Laminar.MergeWindows
import Mathlib.Order.Preorder.Finite
import Mathlib.Data.Fintype.EquivFin

namespace ResearchMain.Laminar

open Classical

variable {E : Type*}

def LaminarFamily (family : Finset (Finset E)) : Prop :=
  ∀ F ∈ family, ∀ G ∈ family, Disjoint F G ∨ F ⊆ G ∨ G ⊆ F

noncomputable def Feasible (family : Finset (Finset E)) (capacity : Finset E → ℕ)
    (I : Finset E) : Prop := ∀ F ∈ family, (I ∩ F).card ≤ capacity F

theorem feasible_mono {family : Finset (Finset E)} {capacity : Finset E → ℕ}
    {I J : Finset E} (hIJ : I ⊆ J) (hJ : Feasible family capacity J) : Feasible family capacity I := by
  intro F hF
  exact (Finset.card_le_card (Finset.inter_subset_inter hIJ (Finset.Subset.refl F))).trans (hJ F hF)

noncomputable def maximalFamily (family : Finset (Finset E)) : Finset (Finset E) :=
  family.filter fun F => ∀ G ∈ family, F ⊆ G → G = F

theorem maximalFamily_subset (family : Finset (Finset E)) : maximalFamily family ⊆ family :=
  Finset.filter_subset _ _

theorem exists_maximal_superset (family : Finset (Finset E)) (F : Finset E) (hF : F ∈ family) :
    ∃ G ∈ maximalFamily family, F ⊆ G := by
  obtain ⟨G, hFG, hG, hmax⟩ := family.exists_le_maximal hF
  refine ⟨G, Finset.mem_filter.mpr ⟨hG, ?_⟩, hFG⟩
  intro H hH hGH
  exact Finset.Subset.antisymm (hmax hH hGH) hGH

theorem maximalFamily_disjoint {family : Finset (Finset E)} (hlam : LaminarFamily family)
    (F G : maximalFamily family) (hne : F ≠ G) : Disjoint F.val G.val := by
  obtain ⟨hF, hFm⟩ := Finset.mem_filter.mp F.property
  obtain ⟨hG, hGm⟩ := Finset.mem_filter.mp G.property
  rcases hlam F.val hF G.val hG with hd | hFG | hGF
  · exact hd
  · exact False.elim (hne (Subtype.ext (hFm G.val hG hFG).symm))
  · exact False.elim (hne (Subtype.ext (hGm F.val hF hGF)))

noncomputable def properSubfamily (family : Finset (Finset E)) (ground : Finset E) :
    Finset (Finset E) := family.filter fun F => F ⊂ ground

theorem properSubfamily_card_lt {family : Finset (Finset E)} {F : Finset E} (hF : F ∈ family) :
    (properSubfamily family F).card < family.card := by
  apply Finset.card_lt_card
  apply Finset.ssubset_iff_subset_ne.mpr
  refine ⟨Finset.filter_subset _ _, ?_⟩
  intro heq
  have hmem : F ∈ properSubfamily family F := heq.symm ▸ hF
  have hss := (Finset.mem_filter.mp hmem).2
  exact (Finset.ssubset_iff_subset_ne.mp hss).2 rfl

theorem properSubfamily_laminar {family : Finset (Finset E)} (hlam : LaminarFamily family)
    (F : Finset E) : LaminarFamily (properSubfamily family F) := by
  intro G hG H hH
  exact hlam G (Finset.mem_filter.mp hG).1 H (Finset.mem_filter.mp hH).1

noncomputable def maximalUnion (family : Finset (Finset E)) : Finset E :=
  (maximalFamily family).biUnion id

abbrev Child (family : Finset (Finset E)) := Option (maximalFamily family)

noncomputable def childGround (family : Finset (Finset E)) (ground : Finset E) :
    Child family → Finset E
  | none => ground \ maximalUnion family
  | some F => F.val

theorem childGround_subset {family : Finset (Finset E)} {ground : Finset E}
    (hground : ∀ F ∈ family, F ⊆ ground) (u : Child family) : childGround family ground u ⊆ ground := by
  cases u with
  | none => exact Finset.sdiff_subset
  | some F => exact hground F.val (maximalFamily_subset family F.property)

theorem childGround_disjoint {family : Finset (Finset E)} (hlam : LaminarFamily family)
    (ground : Finset E) (u v : Child family) (hne : u ≠ v) :
    Disjoint (childGround family ground u) (childGround family ground v) := by
  cases u with
  | none =>
    cases v with
    | none => exact False.elim (hne rfl)
    | some F =>
      apply Finset.disjoint_left.mpr
      intro e he hF
      exact (Finset.mem_sdiff.mp he).2
        (Finset.mem_biUnion.mpr ⟨F.val, F.property, hF⟩)
  | some F =>
    cases v with
    | none =>
      apply Finset.disjoint_left.mpr
      intro e hF he
      exact (Finset.mem_sdiff.mp he).2
        (Finset.mem_biUnion.mpr ⟨F.val, F.property, hF⟩)
    | some G =>
      exact maximalFamily_disjoint hlam F G (fun h => hne (congrArg Option.some h))

theorem exists_childGround {family : Finset (Finset E)} {ground : Finset E}
    (e : E) (he : e ∈ ground) : ∃ u : Child family, e ∈ childGround family ground u := by
  by_cases hU : e ∈ maximalUnion family
  · obtain ⟨F, hF, heF⟩ := Finset.mem_biUnion.mp hU
    exact ⟨some ⟨F, hF⟩, heF⟩
  · exact ⟨none, Finset.mem_sdiff.mpr ⟨he, hU⟩⟩

noncomputable def arbitraryOrdering {R : Type*} (rows : R → Finset E) : Ordering rows :=
  fun i => (rows i).equivFin.symm

end ResearchMain.Laminar
