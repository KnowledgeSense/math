import MainTheorems.PreorderGamma.RootExposedFaces
import Mathlib.Analysis.Convex.KreinMilman

namespace ResearchMain.PreorderGamma

open scoped BigOperators

variable {E : Type*} [Fintype E] [DecidableEq E] [Preorder E]

abbrev RootAmbient (E : Type*) := (Option E → ℝ) × (Option E → ℝ)

def tightRootVertices (d : RootSupportingData E) : Set (RootAmbient E) :=
  {v ∈ rootVertices (E := E) | rootSupportingMap d v = d.maximum}

theorem tightRootVertices_eq_image (d : RootSupportingData E) :
    tightRootVertices d =
      (fun e : AugmentedEdge E => rootVertex e.val.1 e.val.2) '' (tightEdges d : Set _) := by
  ext v
  constructor
  · rintro ⟨⟨e, rfl⟩, he⟩
    exact ⟨e, (mem_tightEdges d e).mpr (by rwa [rootSupportingMap_vertex] at he), rfl⟩
  · rintro ⟨e, he, rfl⟩
    refine ⟨⟨e, rfl⟩, ?_⟩
    rw [rootSupportingMap_vertex]
    exact (mem_tightEdges d e).mp he

theorem rootExposedFace_eq_convexHull (d : RootSupportingData E) :
    rootExposedFace d = convexHull ℝ (tightRootVertices d) := by
  have he := rootExposedFace_isExposed d
  have hcompact := he.isCompact (rootPolytope_compact (E := E))
  have hconvex := he.convex (rootPolytope_convex (E := E))
  have hex : (rootExposedFace d).extremePoints ℝ ⊆ tightRootVertices d := by
    intro x hx
    refine ⟨?_, (extremePoints_subset hx).2⟩
    exact extremePoints_convexHull_subset (he.isExtreme.extremePoints_subset_extremePoints hx)
  have hfinite : ((rootExposedFace d).extremePoints ℝ).Finite :=
    rootVertices_finite.subset (fun x hx => (hex hx).1)
  have hrep : convexHull ℝ ((rootExposedFace d).extremePoints ℝ) = rootExposedFace d := by
    have h := closure_convexHull_extremePoints hcompact hconvex
    rwa [(hfinite.isCompact_convexHull ℝ).isClosed.closure_eq] at h
  apply Set.Subset.antisymm
  · rw [← hrep]
    exact convexHull_mono hex
  · apply convexHull_min ?_ hconvex
    rintro x ⟨hx, heq⟩
    exact ⟨subset_convexHull ℝ _ hx, heq⟩

theorem rootExposedFace_eq_polytope_iff (d : RootSupportingData E) :
    rootExposedFace d = rootPolytope (E := E) ↔ tightEdges d = Finset.univ := by
  constructor
  · intro h
    apply Finset.eq_univ_of_forall
    intro e
    apply (rootVertex_mem_rootExposedFace d e).mp
    rw [h]
    exact rootVertex_mem_rootPolytope e
  · intro h
    rw [rootExposedFace_eq_convexHull, tightRootVertices_eq_image, h]
    simp only [Finset.coe_univ, Set.image_univ, rootPolytope, rootVertices]

theorem rootExposedFace_nonempty_iff (d : RootSupportingData E) :
    (rootExposedFace d).Nonempty ↔ (tightEdges d).Nonempty := by
  rw [rootExposedFace_eq_convexHull, convexHull_nonempty_iff, tightRootVertices_eq_image]
  simp only [Set.image_nonempty, Finset.coe_nonempty]

noncomputable def supportingDataOfLinearMap
    (f : RootAmbient E →ₗ[ℝ] ℝ) (m : ℝ)
    (hf : ∀ i j, augmentedRelation i j → f (rootVertex i j) ≤ m) :
    RootSupportingData E where
  left := fun i => f (Pi.single i 1, 0)
  right := fun j => f (0, Pi.single j 1)
  maximum := m
  bound := by
    intro i j hij
    rw [← f.map_add]
    simpa [rootVertex] using hf i j hij

theorem supportingDataOfLinearMap_apply
    (f : RootAmbient E →ₗ[ℝ] ℝ) (m : ℝ)
    (hf : ∀ i j, augmentedRelation i j → f (rootVertex i j) ≤ m)
    (x : RootAmbient E) : rootSupportingMap (supportingDataOfLinearMap f m hf) x = f x := by
  let fl := f.comp (LinearMap.inl ℝ (Option E → ℝ) (Option E → ℝ))
  let fr := f.comp (LinearMap.inr ℝ (Option E → ℝ) (Option E → ℝ))
  have hbasis : ∀ i : Option E,
      (fun j => if i = j then (1 : ℝ) else 0) = Pi.single i 1 := by
    intro i
    funext j
    simp [Pi.single_apply, eq_comm]
  have hl : f (x.1, 0) = ∑ i, f (Pi.single i 1, 0) * x.1 i := by
    have h := fl.pi_apply_eq_sum_univ x.1
    simp_rw [hbasis] at h
    simpa [fl, mul_comm] using h
  have hr : f (0, x.2) = ∑ j, f (0, Pi.single j 1) * x.2 j := by
    have h := fr.pi_apply_eq_sum_univ x.2
    simp_rw [hbasis] at h
    simpa [fr, mul_comm] using h
  change (∑ i, f (Pi.single i 1, 0) * x.1 i) +
    (∑ j, f (0, Pi.single j 1) * x.2 j) = f x
  rw [← hl, ← hr, ← f.map_add]
  congr 1
  ext <;> simp

theorem exposedFace_eq_rootExposedFace {s : Set (RootAmbient E)}
    (hs : IsExposed ℝ (rootPolytope (E := E)) s) (hn : s.Nonempty) :
    ∃ d : RootSupportingData E, s = rootExposedFace d := by
  obtain ⟨l, hl⟩ := hs hn
  obtain ⟨z, hz⟩ := hn
  rw [hl] at hz
  have hb : ∀ i j, augmentedRelation i j → l (rootVertex i j) ≤ l z := by
    intro i j hij
    exact hz.2 _ (rootVertex_mem_rootPolytope ⟨(i, j), hij⟩)
  let d := supportingDataOfLinearMap l.toLinearMap (l z) hb
  refine ⟨d, ?_⟩
  rw [hl]
  ext x
  change (x ∈ rootPolytope (E := E) ∧ ∀ y ∈ rootPolytope (E := E), l y ≤ l x) ↔
    x ∈ rootPolytope (E := E) ∧ rootSupportingMap d x = l z
  rw [supportingDataOfLinearMap_apply]
  constructor
  · rintro ⟨hx, hmax⟩
    exact ⟨hx, le_antisymm (hz.2 _ hx) (hmax _ hz.1)⟩
  · rintro ⟨hx, heq⟩
    refine ⟨hx, ?_⟩
    intro y hy
    change l.toLinearMap y ≤ l.toLinearMap x
    rw [heq]
    exact hz.2 _ hy

def IsGeometricRootFacet (s : Set (RootAmbient E)) : Prop :=
  s.Nonempty ∧ IsExposed ℝ (rootPolytope (E := E)) s ∧
    s ≠ rootPolytope (E := E) ∧
      ∀ t : Set (RootAmbient E), IsExposed ℝ (rootPolytope (E := E)) t →
        s ⊆ t → t ≠ rootPolytope (E := E) → s = t

theorem geometricRootFacet_iff (d : RootSupportingData E) :
    IsGeometricRootFacet (rootExposedFace d) ↔ IsRootFacet d := by
  constructor
  · rintro ⟨hn, he, hp, hm⟩
    refine ⟨(rootExposedFace_nonempty_iff d).mp hn,
      fun h => hp ((rootExposedFace_eq_polytope_iff d).mpr h), ?_⟩
    intro d' ht hp'
    have hs : rootExposedFace d ⊆ rootExposedFace d' := by
      rw [rootExposedFace_eq_convexHull, rootExposedFace_eq_convexHull]
      apply convexHull_mono
      rw [tightRootVertices_eq_image, tightRootVertices_eq_image]
      exact Set.image_mono ht
    have hfaces := hm _ (rootExposedFace_isExposed d') hs
      (fun h => hp' ((rootExposedFace_eq_polytope_iff d').mp h))
    ext e
    rw [← rootVertex_mem_rootExposedFace d e, hfaces, rootVertex_mem_rootExposedFace d' e]
  · rintro ⟨hn, hp, hm⟩
    refine ⟨(rootExposedFace_nonempty_iff d).mpr hn, rootExposedFace_isExposed d,
      fun h => hp ((rootExposedFace_eq_polytope_iff d).mp h), ?_⟩
    intro t ht hs hp'
    obtain ⟨d', rfl⟩ := exposedFace_eq_rootExposedFace ht
      ((rootExposedFace_nonempty_iff d).mpr hn |>.mono hs)
    have hsub : tightEdges d ⊆ tightEdges d' := by
      intro e he
      exact (rootVertex_mem_rootExposedFace d' e).mp
        (hs ((rootVertex_mem_rootExposedFace d e).mpr he))
    have heq := hm d' hsub (fun h => hp' ((rootExposedFace_eq_polytope_iff d').mpr h))
    rw [rootExposedFace_eq_convexHull, rootExposedFace_eq_convexHull,
      tightRootVertices_eq_image, tightRootVertices_eq_image, heq]

theorem geometricRootFacet_unique_missing_diagonal {s : Set (RootAmbient E)}
    (hs : IsGeometricRootFacet s) :
    ∃! i : Option E, rootVertex i i ∉ s := by
  obtain ⟨d, rfl⟩ := exposedFace_eq_rootExposedFace hs.2.1 hs.1
  have hd := (geometricRootFacet_iff d).mp hs
  simpa only [diagonal_mem_rootExposedFace] using rootFacet_unique_missing_diagonal d hd

end ResearchMain.PreorderGamma
