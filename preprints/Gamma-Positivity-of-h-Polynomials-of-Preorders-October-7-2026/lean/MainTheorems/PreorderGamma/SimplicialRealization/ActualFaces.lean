import MainTheorems.PreorderGamma.SimplicialRealization.BoundaryDimension
import Mathlib.Analysis.Convex.Combination
import Mathlib.Analysis.Convex.Exposed
import Mathlib.Topology.Algebra.Module.FiniteDimension

namespace ResearchMain.PreorderGamma.SimplicialRealization

open scoped BigOperators

variable {E : Type*} [Fintype E] [DecidableEq E] [Preorder E]

def projectiveSupportingFace (height : QuotientIndex E → ℝ)
    (l : (E → ℝ) →ₗ[ℝ] ℝ) (m : ℝ) : Set (E → ℝ) :=
  {x ∈ projectivePolytope height | l x = m}

theorem projectiveSupportingMap_le (height : QuotientIndex E → ℝ)
    (l : (E → ℝ) →ₗ[ℝ] ℝ) (m : ℝ)
    (hb : ∀ v, l (projectiveVertex height v) ≤ m)
    {x : E → ℝ} (hx : x ∈ projectivePolytope height) : l x ≤ m := by
  apply convexHull_min ?_ (convex_halfSpace_le l.isLinear m) hx
  rintro v ⟨i, rfl⟩
  exact hb i

theorem projectiveSupportingFace_isExposed (height : QuotientIndex E → ℝ)
    (l : (E → ℝ) →ₗ[ℝ] ℝ) (m : ℝ)
    (hb : ∀ v, l (projectiveVertex height v) ≤ m) :
    IsExposed ℝ (projectivePolytope height) (projectiveSupportingFace height l m) := by
  intro hn
  refine ⟨l.toContinuousLinearMap, ?_⟩
  ext x
  constructor
  · rintro ⟨hx, heq⟩
    refine ⟨hx, ?_⟩
    intro y hy
    change l y ≤ l x
    rw [heq]
    exact projectiveSupportingMap_le height l m hb hy
  · rintro ⟨hx, hmax⟩
    obtain ⟨z, hz, heq⟩ := hn
    refine ⟨hx, le_antisymm (projectiveSupportingMap_le height l m hb hx) ?_⟩
    have h := hmax z hz
    change l z ≤ l x at h
    rwa [heq] at h

theorem projectivePolytope_weights (height : QuotientIndex E → ℝ)
    {x : E → ℝ} (hx : x ∈ projectivePolytope height) :
    ∃ w : QuotientIndex E → ℝ, (∀ v, 0 ≤ w v) ∧ (∑ v, w v) = 1 ∧
      (∑ v, w v • projectiveVertex height v) = x := by
  classical
  rw [projectivePolytope, projectiveVertices,
    convexHull_range_eq_exists_affineCombination] at hx
  obtain ⟨s, w, hw, hs, hx⟩ := hx
  refine ⟨fun v => if v ∈ s then w v else 0, ?_, ?_, ?_⟩
  · intro v
    change 0 ≤ (if v ∈ s then w v else 0)
    split_ifs with hv
    · exact hw v hv
    · exact le_rfl
  · simpa only [Finset.sum_ite_mem_eq] using hs
  · simp only [ite_smul, zero_smul, Finset.sum_ite_mem_eq]
    rw [← Finset.affineCombination_eq_linear_combination s (projectiveVertex height) w hs]
    exact hx

theorem projectiveSupportingFace_convexHull (height : QuotientIndex E → ℝ)
    (l : (E → ℝ) →ₗ[ℝ] ℝ) (m : ℝ) (s : Finset (QuotientIndex E))
    (hb : ∀ v, l (projectiveVertex height v) ≤ m)
    (ht : ∀ v, v ∈ s ↔ l (projectiveVertex height v) = m) :
    projectiveSupportingFace height l m =
      convexHull ℝ (Set.range fun v : s => projectiveVertex height v.val) := by
  classical
  apply Set.Subset.antisymm
  · rintro x ⟨hx, hlx⟩
    obtain ⟨w, hw, hw1, hwx⟩ := projectivePolytope_weights height hx
    have hdef : (∑ v, w v * (m - l (projectiveVertex height v))) = 0 := by
      calc
        _ = (∑ v, w v) * m - l (∑ v, w v • projectiveVertex height v) := by
          simp [mul_sub, Finset.sum_sub_distrib, Finset.sum_mul,
            map_sum, map_smul, smul_eq_mul]
        _ = 0 := by rw [hw1, hwx, hlx]; ring
    have hout : ∀ v ∉ s, w v = 0 := by
      intro v hv
      have hvne : l (projectiveVertex height v) ≠ m := fun h => hv ((ht v).mpr h)
      have hterm := (Finset.sum_eq_zero_iff_of_nonneg
        (fun v _ => mul_nonneg (hw v) (sub_nonneg.mpr (hb v)))).mp hdef v (Finset.mem_univ _)
      have hgap : m - l (projectiveVertex height v) ≠ 0 := sub_ne_zero.mpr hvne.symm
      exact (mul_eq_zero.mp hterm).resolve_right hgap
    have hws : (∑ v : s, w v.val) = 1 := by
      rw [Finset.sum_coe_sort]
      calc
        _ = ∑ v, w v := Finset.sum_subset (Finset.subset_univ s) (fun v _ hv => hout v hv)
        _ = 1 := hw1
    have hwxs : (∑ v : s, w v.val • projectiveVertex height v.val) = x := by
      rw [Finset.sum_coe_sort s (fun v => w v • projectiveVertex height v)]
      calc
        _ = ∑ v, w v • projectiveVertex height v :=
          Finset.sum_subset (Finset.subset_univ s) (fun v _ hv => by rw [hout v hv, zero_smul])
        _ = x := hwx
    exact mem_convexHull_of_exists_fintype (fun v : s => w v.val)
      (fun v : s => projectiveVertex height v.val) (fun v => hw v.val) hws
      (fun v => Set.mem_range_self v) hwxs
  · apply convexHull_min ?_
      ((projectivePolytope_convex height).inter (convex_hyperplane l.isLinear m))
    rintro x ⟨v, rfl⟩
    exact ⟨projectiveVertex_mem height v.val, (ht v.val).mp v.property⟩

theorem actual_boundary_face_simplex (height : QuotientIndex E → ℝ)
    (hheight : ∀ v, 0 < height v) (hsimp : HasSimplicialBoundary height)
    (s : Finset (QuotientIndex E)) (hs : s ∈ boundaryVertexFaces height) (hn : s.Nonempty) :
    ∃ l : (E → ℝ) →ₗ[ℝ] ℝ, l ≠ 0 ∧ ∃ m : ℝ,
      0 < m ∧ IsExposed ℝ (projectivePolytope height) (projectiveSupportingFace height l m) ∧
        projectiveSupportingFace height l m =
          convexHull ℝ (Set.range fun v : s => projectiveVertex height v.val) ∧
        AffineIndependent ℝ (fun v : s => projectiveVertex height v.val) ∧ s.card ≤ Fintype.card E := by
  have hf := (mem_boundaryVertexFaces height s).mp hs
  rcases hf with hzero | ⟨l, hl, m, hb, ht, hn'⟩
  · subst s
    simp at hn
  · exact ⟨l, hl, m, projective_support_value_pos height hheight l hl m hb,
      projectiveSupportingFace_isExposed height l m hb,
      projectiveSupportingFace_convexHull height l m s hb ht,
      hsimp s hs, boundary_face_card_le_dimension height hheight hsimp s hs⟩

end ResearchMain.PreorderGamma.SimplicialRealization
