import MainTheorems.PreorderGamma.SimplicialRealization.ActualFaces
import Mathlib.Analysis.Convex.Gauge
import Mathlib.Analysis.LocallyConvex.Separation
import Mathlib.Analysis.Normed.Affine.AddTorsorBases

namespace ResearchMain.PreorderGamma.SimplicialRealization

open scoped BigOperators Pointwise

variable {E : Type*} [Fintype E] [DecidableEq E] [Preorder E]

theorem projectivePolytope_interior_nonempty (height : QuotientIndex E → ℝ)
    (hheight : ∀ v, 0 < height v) : (interior (projectivePolytope height)).Nonempty :=
  ((projectivePolytope_convex height).interior_nonempty_iff_affineSpan_eq_top).mpr
    (projectivePolytope_affineSpan height hheight)

theorem zero_mem_projectivePolytope_interior (height : QuotientIndex E → ℝ)
    (hheight : ∀ v, 0 < height v) : (0 : E → ℝ) ∈ interior (projectivePolytope height) := by
  by_contra hzero
  obtain ⟨l, hl, hb⟩ := geometric_hahn_banach_of_nonempty_interior_point
    (projectivePolytope_convex height) hzero
    (projectivePolytope_interior_nonempty height hheight)
  have hl' : l.toLinearMap ≠ 0 := by
    intro h
    apply hl
    ext x
    exact congrArg (fun f : (E → ℝ) →ₗ[ℝ] ℝ => f x) h
  have hp := projective_support_value_pos height hheight l.toLinearMap hl' 0
    (fun v => by simpa using hb _ (projectiveVertex_mem height v))
  exact (lt_irrefl (0 : ℝ)) hp

theorem radial_boundary_point (height : QuotientIndex E → ℝ)
    (hheight : ∀ v, 0 < height v) (x : E → ℝ) (hx : x ≠ 0) :
    ∃ a : ℝ, 0 < a ∧ a⁻¹ • x ∈ frontier (projectivePolytope height) := by
  let P := projectivePolytope height
  have hnhds : P ∈ nhds (0 : E → ℝ) :=
    mem_interior_iff_mem_nhds.mp (zero_mem_projectivePolytope_interior height hheight)
  have habs : Absorbent ℝ P := absorbent_nhds_zero hnhds
  have ha : 0 < gauge P x := (gauge_pos habs
    ((projectivePolytope_compact height).isVonNBounded ℝ)).mpr hx
  refine ⟨gauge P x, ha, ?_⟩
  apply mem_frontier_of_gauge_eq_one (projectivePolytope_convex height)
    (zero_mem_projectivePolytope height) habs
  rw [gauge_smul_of_nonneg (inv_nonneg.mpr ha.le), smul_eq_mul,
    inv_mul_cancel₀ (ne_of_gt ha)]

theorem boundary_point_support (height : QuotientIndex E → ℝ)
    (hheight : ∀ v, 0 < height v) (x : E → ℝ)
    (hx : x ∈ frontier (projectivePolytope height)) :
    ∃ l : (E → ℝ) →ₗ[ℝ] ℝ, l ≠ 0 ∧
      (∀ v, l (projectiveVertex height v) ≤ l x) ∧ 0 < l x := by
  obtain ⟨l, hl, hb⟩ := geometric_hahn_banach_of_nonempty_interior_point
    (projectivePolytope_convex height) hx.2
    (projectivePolytope_interior_nonempty height hheight)
  have hl' : l.toLinearMap ≠ 0 := by
    intro h
    apply hl
    ext y
    exact congrArg (fun f : (E → ℝ) →ₗ[ℝ] ℝ => f y) h
  have hb' : ∀ v, l.toLinearMap (projectiveVertex height v) ≤ l.toLinearMap x :=
    fun v => hb _ (projectiveVertex_mem height v)
  exact ⟨l.toLinearMap, hl', hb',
    projective_support_value_pos height hheight l.toLinearMap hl' _ hb'⟩

end ResearchMain.PreorderGamma.SimplicialRealization
