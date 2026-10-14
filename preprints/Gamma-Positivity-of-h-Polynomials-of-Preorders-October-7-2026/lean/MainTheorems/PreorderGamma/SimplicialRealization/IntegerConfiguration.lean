import MainTheorems.PreorderGamma.SimplicialRealization.ProjectivePolytope
import MainTheorems.PreorderGamma.SimplicialRealization.NetworkDeterminants

namespace ResearchMain.PreorderGamma.SimplicialRealization

open scoped BigOperators

variable {E : Type*} [Fintype E] [DecidableEq E] [Preorder E]

theorem quotientIndex_has_edge (v : QuotientIndex E) :
    ∃ e : AugmentedEdge E, rootProjection (rootVertex e.val.1 e.val.2) = v.val := by
  obtain ⟨x, ⟨e, rfl⟩, h⟩ := v.property
  exact ⟨e, h⟩

noncomputable def quotientEdge (v : QuotientIndex E) : AugmentedEdge E :=
  Classical.choose (quotientIndex_has_edge v)

theorem quotientEdge_projection (v : QuotientIndex E) :
    rootProjection (rootVertex (quotientEdge v).val.1 (quotientEdge v).val.2) = v.val :=
  Classical.choose_spec (quotientIndex_has_edge v)

noncomputable def integerQuotientVertex (v : QuotientIndex E) : E → ℤ :=
  fun i => networkUnit (quotientEdge v).val.1 i - networkUnit (quotientEdge v).val.2 i

theorem integerQuotientVertex_cast (v : QuotientIndex E) :
    (fun i => (integerQuotientVertex v i : ℝ)) = v.val := by
  rw [← quotientEdge_projection v]
  funext i
  unfold integerQuotientVertex
  rcases h : (quotientEdge v).val with ⟨a, b⟩
  cases a <;> cases b <;>
    simp [networkUnit, rootProjection, rootVertex, Pi.single_apply]

@[simp] theorem integerQuotientVertex_cast_apply (v : QuotientIndex E) (i : E) :
    (integerQuotientVertex v i : ℝ) = v.val i :=
  congrFun (integerQuotientVertex_cast v) i

noncomputable def quotientIntegerMatrix : Matrix E (QuotientIndex E) ℤ :=
  fun i v => integerQuotientVertex v i

theorem quotientIntegerMatrix_network (v : QuotientIndex E) :
    IsNetworkColumn (fun i => quotientIntegerMatrix (E := E) i v) :=
  ⟨(quotientEdge v).val.1, (quotientEdge v).val.2, fun _ => rfl⟩

theorem quotientIntegerMatrix_totallyUnimodular :
    (quotientIntegerMatrix (E := E)).IsTotallyUnimodular :=
  networkMatrix_totallyUnimodular _ quotientIntegerMatrix_network

theorem quotientIntegerBasis_det_abs
    (f : Fin (Fintype.card E) → QuotientIndex E) :
    ((quotientIntegerMatrix (E := E)).submatrix (Fintype.equivFin E).symm f).det.natAbs ≤ 1 :=
  networkMatrix_det_abs _ _ (fun j =>
    (quotientIntegerMatrix_network (f j)).pullback (Fintype.equivFin E).symm
      (Fintype.equivFin E).symm.injective)

theorem quotientIntegerBasis_unimodular
    (f : Fin (Fintype.card E) → QuotientIndex E)
    (hf : ((quotientIntegerMatrix (E := E)).submatrix (Fintype.equivFin E).symm f).det ≠ 0) :
    ((quotientIntegerMatrix (E := E)).submatrix (Fintype.equivFin E).symm f).det.natAbs = 1 := by
  have h := quotientIntegerBasis_det_abs f
  have hpos : 0 <
      ((quotientIntegerMatrix (E := E)).submatrix (Fintype.equivFin E).symm f).det.natAbs :=
    Int.natAbs_pos.mpr hf
  omega

end ResearchMain.PreorderGamma.SimplicialRealization
