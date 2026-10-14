import Mathlib.Analysis.Convex.Topology
import Mathlib.LinearAlgebra.AffineSpace.FiniteDimensional
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.Pi
import Mathlib.LinearAlgebra.StdBasis
import Mathlib.Tactic

namespace ResearchMain.PreorderGamma

open scoped BigOperators

variable {E : Type*} [Fintype E] [DecidableEq E] [Preorder E]

def augmentedRelation : Option E → Option E → Prop
  | none, _ => True
  | _, none => True
  | some a, some b => b ≤ a

def AugmentedEdge (E : Type*) [Preorder E] :=
  {p : Option E × Option E // augmentedRelation p.1 p.2}

noncomputable instance : Fintype (AugmentedEdge E) := by
  classical
  unfold AugmentedEdge
  infer_instance

def rootVertex (i j : Option E) : (Option E → ℝ) × (Option E → ℝ) :=
  (Pi.single i 1, Pi.single j 1)

def rootVertices : Set ((Option E → ℝ) × (Option E → ℝ)) :=
  Set.range fun e : AugmentedEdge E => rootVertex e.val.1 e.val.2

def rootPolytope : Set ((Option E → ℝ) × (Option E → ℝ)) :=
  convexHull ℝ (rootVertices (E := E))

def rootProjection : ((Option E → ℝ) × (Option E → ℝ)) →ₗ[ℝ] (E → ℝ) where
  toFun := fun x a => x.1 (some a) - x.2 (some a)
  map_add' := by intro x y; ext a; simp; ring
  map_smul' := by intro c x; ext a; simp; ring

def quotientVertices : Set (E → ℝ) :=
  rootProjection '' rootVertices (E := E)

def quotientPolytope : Set (E → ℝ) :=
  convexHull ℝ (quotientVertices (E := E))

omit [Fintype E] [Preorder E] in
theorem rootProjection_vertex_none_none :
    rootProjection (rootVertex (none : Option E) none) = 0 := by
  ext a
  simp [rootProjection, rootVertex]

omit [Fintype E] [Preorder E] in
theorem rootProjection_vertex_some_none (a : E) :
    rootProjection (rootVertex (some a) none) = Pi.single a (1 : ℝ) := by
  ext b
  simp [rootProjection, rootVertex, Pi.single_apply]

omit [Fintype E] [Preorder E] in
theorem rootProjection_vertex_none_some (a : E) :
    rootProjection (rootVertex none (some a)) = -Pi.single a (1 : ℝ) := by
  ext b
  simp [rootProjection, rootVertex, Pi.single_apply]

omit [Fintype E] [Preorder E] in
theorem rootProjection_vertex_some_some (a b : E) :
    rootProjection (rootVertex (some a) (some b)) =
      Pi.single a (1 : ℝ) - Pi.single b (1 : ℝ) := by
  ext c
  simp [rootProjection, rootVertex, Pi.single_apply]

omit [Fintype E] in
theorem mem_quotientVertices (x : E → ℝ) :
    x ∈ quotientVertices (E := E) ↔
      x = 0 ∨ (∃ a, x = Pi.single a 1) ∨ (∃ a, x = -Pi.single a 1) ∨
        ∃ a b, b ≤ a ∧ x = Pi.single a 1 - Pi.single b 1 := by
  constructor
  · rintro ⟨v, ⟨e, rfl⟩, rfl⟩
    rcases e with ⟨⟨i, j⟩, h⟩
    cases i with
    | none =>
      cases j with
      | none => exact Or.inl rootProjection_vertex_none_none
      | some b => exact Or.inr (Or.inr (Or.inl ⟨b, rootProjection_vertex_none_some b⟩))
    | some a =>
      cases j with
      | none => exact Or.inr (Or.inl ⟨a, rootProjection_vertex_some_none a⟩)
      | some b => exact Or.inr (Or.inr (Or.inr ⟨a, b, h,
          rootProjection_vertex_some_some a b⟩))
  · intro h
    rcases h with rfl | ⟨a, rfl⟩ | ⟨a, rfl⟩ | ⟨a, b, hab, rfl⟩
    · exact ⟨rootVertex none none, ⟨⟨(none, none), trivial⟩, rfl⟩,
        rootProjection_vertex_none_none⟩
    · exact ⟨rootVertex (some a) none, ⟨⟨(some a, none), trivial⟩, rfl⟩,
        rootProjection_vertex_some_none a⟩
    · exact ⟨rootVertex none (some a), ⟨⟨(none, some a), trivial⟩, rfl⟩,
        rootProjection_vertex_none_some a⟩
    · exact ⟨rootVertex (some a) (some b), ⟨⟨(some a, some b), hab⟩, rfl⟩,
        rootProjection_vertex_some_some a b⟩

omit [Fintype E] in
theorem rootProjection_polytope :
    rootProjection '' rootPolytope (E := E) = quotientPolytope (E := E) :=
  rootProjection.image_convexHull _

theorem rootVertices_finite : (rootVertices (E := E)).Finite :=
  Set.finite_range _

theorem quotientVertices_finite : (quotientVertices (E := E)).Finite :=
  rootVertices_finite.image rootProjection

theorem rootPolytope_compact : IsCompact (rootPolytope (E := E)) :=
  rootVertices_finite.isCompact_convexHull ℝ

theorem quotientPolytope_compact : IsCompact (quotientPolytope (E := E)) :=
  quotientVertices_finite.isCompact_convexHull ℝ

omit [Fintype E] in
theorem rootPolytope_convex : Convex ℝ (rootPolytope (E := E)) :=
  convex_convexHull ℝ _

omit [Fintype E] in
theorem quotientPolytope_convex : Convex ℝ (quotientPolytope (E := E)) :=
  convex_convexHull ℝ _

omit [Fintype E] in
theorem zero_mem_quotientPolytope : (0 : E → ℝ) ∈ quotientPolytope (E := E) :=
  subset_convexHull ℝ _ ((mem_quotientVertices _).mpr (Or.inl rfl))

omit [Fintype E] in
theorem single_mem_quotientPolytope (a : E) :
    Pi.single a (1 : ℝ) ∈ quotientPolytope (E := E) :=
  subset_convexHull ℝ _ ((mem_quotientVertices _).mpr (Or.inr (Or.inl ⟨a, rfl⟩)))

omit [Fintype E] in
theorem neg_single_mem_quotientPolytope (a : E) :
    -Pi.single a (1 : ℝ) ∈ quotientPolytope (E := E) :=
  subset_convexHull ℝ _ ((mem_quotientVertices _).mpr
    (Or.inr (Or.inr (Or.inl ⟨a, rfl⟩))))

theorem quotientPolytope_affineSpan :
    affineSpan ℝ (quotientPolytope (E := E)) = ⊤ := by
  let s := affineSpan ℝ (quotientPolytope (E := E))
  have hz : (0 : E → ℝ) ∈ s := subset_affineSpan ℝ _ zero_mem_quotientPolytope
  have hu : ∀ a, Pi.single a (1 : ℝ) ∈ s.direction := by
    intro a
    simpa using AffineSubspace.vsub_mem_direction
      (subset_affineSpan ℝ _ (single_mem_quotientPolytope a)) hz
  have hd : s.direction = ⊤ := by
    apply top_unique
    intro x hx
    rw [← Finset.univ_sum_single x]
    apply Submodule.sum_mem
    intro a ha
    have heq : Pi.single a (x a) = x a • Pi.single a (1 : ℝ) := by
      ext b
      simp [Pi.single_apply]
    rw [heq]
    exact s.direction.smul_mem (x a) (hu a)
  exact (AffineSubspace.direction_eq_top_iff_of_nonempty ⟨0, hz⟩).mp hd

theorem quotientPolytope_dimension :
    Module.finrank ℝ (affineSpan ℝ (quotientPolytope (E := E))).direction =
      Fintype.card E := by
  rw [quotientPolytope_affineSpan, AffineSubspace.direction_top, finrank_top]
  simp

omit [Fintype E] [Preorder E] in
theorem diagonalRootVertices_affineIndependent :
    AffineIndependent ℝ (fun i : Option E => rootVertex i i) := by
  apply AffineIndependent.of_comp
    (LinearMap.fst ℝ (Option E → ℝ) (Option E → ℝ)).toAffineMap
  simpa [rootVertex, Function.comp_def] using
    (Pi.linearIndependent_single_one (Option E) ℝ).affineIndependent

omit [Preorder E] in
theorem diagonalRootVertices_dimension :
    Module.finrank ℝ
      (affineSpan ℝ (Set.range fun i : Option E => rootVertex i i)).direction =
        Fintype.card E := by
  rw [direction_affineSpan]
  exact diagonalRootVertices_affineIndependent.finrank_vectorSpan (by simp)

end ResearchMain.PreorderGamma
