import MainTheorems.PreorderGamma.SpecialSimplex
import Mathlib.Algebra.Polynomial.Basic

namespace ResearchMain.PreorderGamma.SimplicialRealization

open scoped BigOperators

variable {E : Type*} [Fintype E] [DecidableEq E] [Preorder E]

def QuotientIndex (E : Type*) [Fintype E] [DecidableEq E] [Preorder E] :=
  {v : E → ℝ // v ∈ quotientVertices (E := E)}

noncomputable instance : Fintype (QuotientIndex E) :=
  quotientVertices_finite.fintype

noncomputable def zeroIndex : QuotientIndex E :=
  ⟨0, (mem_quotientVertices _).mpr (Or.inl rfl)⟩

noncomputable def unitIndex (a : E) : QuotientIndex E :=
  ⟨Pi.single a 1, (mem_quotientVertices _).mpr (Or.inr (Or.inl ⟨a, rfl⟩))⟩

noncomputable def negUnitIndex (a : E) : QuotientIndex E :=
  ⟨-Pi.single a 1,
    (mem_quotientVertices _).mpr (Or.inr (Or.inr (Or.inl ⟨a, rfl⟩)))⟩

noncomputable def projectiveVertex (height : QuotientIndex E → ℝ)
    (v : QuotientIndex E) : E → ℝ := (height v)⁻¹ • v.val

noncomputable def projectiveVertices (height : QuotientIndex E → ℝ) : Set (E → ℝ) :=
  Set.range (projectiveVertex height)

noncomputable def projectivePolytope (height : QuotientIndex E → ℝ) : Set (E → ℝ) :=
  convexHull ℝ (projectiveVertices height)

theorem projectiveVertices_finite (height : QuotientIndex E → ℝ) :
    (projectiveVertices height).Finite := Set.finite_range _

theorem projectivePolytope_compact (height : QuotientIndex E → ℝ) :
    IsCompact (projectivePolytope height) :=
  (projectiveVertices_finite height).isCompact_convexHull ℝ

theorem projectivePolytope_convex (height : QuotientIndex E → ℝ) :
    Convex ℝ (projectivePolytope height) := convex_convexHull ℝ _

theorem projectiveVertex_mem (height : QuotientIndex E → ℝ) (v : QuotientIndex E) :
    projectiveVertex height v ∈ projectivePolytope height :=
  subset_convexHull ℝ _ ⟨v, rfl⟩

@[simp] theorem projectiveVertex_zero (height : QuotientIndex E → ℝ) :
    projectiveVertex height zeroIndex = 0 := by simp [projectiveVertex, zeroIndex]

theorem zero_mem_projectivePolytope (height : QuotientIndex E → ℝ) :
    (0 : E → ℝ) ∈ projectivePolytope height := by
  simpa only [projectiveVertex_zero] using projectiveVertex_mem height zeroIndex

theorem projectivePolytope_affineSpan (height : QuotientIndex E → ℝ)
    (hheight : ∀ v, 0 < height v) : affineSpan ℝ (projectivePolytope height) = ⊤ := by
  let s := affineSpan ℝ (projectivePolytope height)
  have hz : (0 : E → ℝ) ∈ s := subset_affineSpan ℝ _ (zero_mem_projectivePolytope height)
  have hu : ∀ a : E, Pi.single a (1 : ℝ) ∈ s.direction := by
    intro a
    have hv : projectiveVertex height (unitIndex a) ∈ s.direction := by
      simpa using AffineSubspace.vsub_mem_direction
        (subset_affineSpan ℝ _ (projectiveVertex_mem height (unitIndex a))) hz
    have hscale : height (unitIndex a) • projectiveVertex height (unitIndex a) =
        Pi.single a (1 : ℝ) := by
      change height (unitIndex a) • ((height (unitIndex a))⁻¹ • Pi.single a (1 : ℝ)) = _
      rw [smul_smul, mul_inv_cancel₀ (ne_of_gt (hheight (unitIndex a))), one_smul]
    rw [← hscale]
    exact s.direction.smul_mem _ hv
  have hd : s.direction = ⊤ := by
    apply top_unique
    intro x _
    rw [← Finset.univ_sum_single x]
    apply Submodule.sum_mem
    intro a ha
    have heq : Pi.single a (x a) = x a • Pi.single a (1 : ℝ) := by
      ext b
      simp [Pi.single_apply]
    rw [heq]
    exact s.direction.smul_mem _ (hu a)
  exact (AffineSubspace.direction_eq_top_iff_of_nonempty ⟨0, hz⟩).mp hd

theorem projectivePolytope_dimension (height : QuotientIndex E → ℝ)
    (hheight : ∀ v, 0 < height v) :
    Module.finrank ℝ (affineSpan ℝ (projectivePolytope height)).direction = Fintype.card E := by
  rw [projectivePolytope_affineSpan height hheight, AffineSubspace.direction_top, finrank_top]
  simp

theorem projectivePolytope_empty [IsEmpty E] (height : QuotientIndex E → ℝ) :
    projectivePolytope height = {0} := by
  apply Set.Subset.antisymm
  · intro x hx
    have h : x = (0 : E → ℝ) := Subsingleton.elim _ _
    exact Set.mem_singleton_iff.mpr h
  · intro x hx
    rw [Set.mem_singleton_iff] at hx
    rw [hx]
    exact zero_mem_projectivePolytope height

def IsBoundaryVertexFace (height : QuotientIndex E → ℝ)
    (s : Finset (QuotientIndex E)) : Prop :=
  s = ∅ ∨ ∃ l : (E → ℝ) →ₗ[ℝ] ℝ, l ≠ 0 ∧ ∃ m : ℝ,
    (∀ v, l (projectiveVertex height v) ≤ m) ∧
    (∀ v, v ∈ s ↔ l (projectiveVertex height v) = m) ∧ s.Nonempty

noncomputable def boundaryVertexFaces (height : QuotientIndex E → ℝ) :
    Finset (Finset (QuotientIndex E)) := by
  classical
  exact Finset.univ.filter (IsBoundaryVertexFace height)

@[simp] theorem mem_boundaryVertexFaces (height : QuotientIndex E → ℝ)
    (s : Finset (QuotientIndex E)) :
    s ∈ boundaryVertexFaces height ↔ IsBoundaryVertexFace height s := by
  classical
  simp [boundaryVertexFaces]

def HasSimplicialBoundary (height : QuotientIndex E → ℝ) : Prop :=
  ∀ s ∈ boundaryVertexFaces height,
    AffineIndependent ℝ (fun v : s => projectiveVertex height v.val)

noncomputable def boundaryHPolynomial (height : QuotientIndex E → ℝ) : Polynomial ℤ :=
  ∑ s ∈ boundaryVertexFaces height,
    Polynomial.X ^ s.card * (1 - Polynomial.X) ^ (Fintype.card E - s.card)

end ResearchMain.PreorderGamma.SimplicialRealization
