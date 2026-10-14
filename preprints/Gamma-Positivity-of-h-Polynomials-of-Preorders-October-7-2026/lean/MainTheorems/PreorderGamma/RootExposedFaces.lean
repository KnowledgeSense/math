import MainTheorems.PreorderGamma.RootFacets
import Mathlib.Analysis.Convex.Exposed
import Mathlib.Topology.Algebra.Module.FiniteDimension

namespace ResearchMain.PreorderGamma

open scoped BigOperators

variable {E : Type*} [Fintype E] [DecidableEq E] [Preorder E]

noncomputable def rootSupportingMap (d : RootSupportingData E) :
    ((Option E → ℝ) × (Option E → ℝ)) →ₗ[ℝ] ℝ where
  toFun := fun x => (∑ i, d.left i * x.1 i) + ∑ i, d.right i * x.2 i
  map_add' := by
    intro x y
    simp [mul_add, Finset.sum_add_distrib]
    ring
  map_smul' := by
    intro c x
    simp [smul_eq_mul, mul_left_comm, ← Finset.mul_sum]
    ring

theorem rootSupportingMap_vertex (d : RootSupportingData E) (i j : Option E) :
    rootSupportingMap d (rootVertex i j) = d.left i + d.right j := by
  cases i <;> cases j <;>
    simp [rootSupportingMap, rootVertex, Pi.single_apply, mul_ite, eq_comm]

theorem rootSupportingMap_le (d : RootSupportingData E)
    {x : (Option E → ℝ) × (Option E → ℝ)} (hx : x ∈ rootPolytope (E := E)) :
    rootSupportingMap d x ≤ d.maximum := by
  change x ∈ convexHull ℝ (rootVertices (E := E)) at hx
  apply convexHull_min ?_ (convex_halfSpace_le (rootSupportingMap d).isLinear d.maximum) hx
  rintro v ⟨e, rfl⟩
  change rootSupportingMap d (rootVertex e.val.1 e.val.2) ≤ d.maximum
  rw [rootSupportingMap_vertex]
  exact d.bound e.val.1 e.val.2 e.property

def rootExposedFace (d : RootSupportingData E) :
    Set ((Option E → ℝ) × (Option E → ℝ)) :=
  {x ∈ rootPolytope (E := E) | rootSupportingMap d x = d.maximum}

theorem rootExposedFace_isExposed (d : RootSupportingData E) :
    IsExposed ℝ (rootPolytope (E := E)) (rootExposedFace d) := by
  intro hnonempty
  refine ⟨(rootSupportingMap d).toContinuousLinearMap, ?_⟩
  ext x
  constructor
  · rintro ⟨hx, heq⟩
    refine ⟨hx, ?_⟩
    intro y hy
    change rootSupportingMap d y ≤ rootSupportingMap d x
    rw [heq]
    exact rootSupportingMap_le d hy
  · rintro ⟨hx, hmax⟩
    obtain ⟨z, hz, heq⟩ := hnonempty
    refine ⟨hx, le_antisymm (rootSupportingMap_le d hx) ?_⟩
    have h := hmax z hz
    change rootSupportingMap d z ≤ rootSupportingMap d x at h
    rwa [heq] at h

omit [Fintype E] in
theorem rootVertex_mem_rootPolytope (e : AugmentedEdge E) :
    rootVertex e.val.1 e.val.2 ∈ rootPolytope (E := E) :=
  subset_convexHull ℝ _ ⟨e, rfl⟩

theorem rootVertex_mem_rootExposedFace (d : RootSupportingData E) (e : AugmentedEdge E) :
    rootVertex e.val.1 e.val.2 ∈ rootExposedFace d ↔ e ∈ tightEdges d := by
  simp only [rootExposedFace, Set.mem_ofPred_eq, rootVertex_mem_rootPolytope,
    true_and, rootSupportingMap_vertex, mem_tightEdges]

theorem diagonal_mem_rootExposedFace (d : RootSupportingData E) (i : Option E) :
    rootVertex i i ∈ rootExposedFace d ↔ diagonalEdge i ∈ tightEdges d :=
  rootVertex_mem_rootExposedFace d (diagonalEdge i)

theorem rootFacet_real_unique_missing_diagonal (d : RootSupportingData E) (hd : IsRootFacet d) :
    IsExposed ℝ (rootPolytope (E := E)) (rootExposedFace d) ∧
      ∃! i : Option E, rootVertex i i ∉ rootExposedFace d := by
  refine ⟨rootExposedFace_isExposed d, ?_⟩
  simpa only [diagonal_mem_rootExposedFace] using rootFacet_unique_missing_diagonal d hd

end ResearchMain.PreorderGamma
