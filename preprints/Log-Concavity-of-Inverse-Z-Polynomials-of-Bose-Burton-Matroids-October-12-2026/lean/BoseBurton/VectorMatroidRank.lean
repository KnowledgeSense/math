import BoseBurton.VectorMatroid
import Mathlib.Combinatorics.Matroid.Rank.ENat

noncomputable section
namespace BoseBurton
open Set Submodule Module
variable {K V α : Type*} [Field K] [AddCommGroup V] [Module K V]
  [Module.Finite K V] [Finite α]

theorem vectorMatroid_basis_span (v : α → V) {I X : Set α}
    (hI : (vectorMatroid (K := K) v).IsBasis I X) :
    vectorSpan (K := K) v I = vectorSpan (K := K) v X := by
  apply le_antisymm (span_mono (Set.image_mono hI.subset))
  apply span_le.mpr
  rintro _ ⟨e, heX, rfl⟩
  by_contra he
  have hi : (vectorMatroid (K := K) v).Indep (insert e I) := hI.indep.insert he
  have heI := hI.mem_of_insert_indep heX hi
  exact he (subset_span ⟨e, heI, rfl⟩)

/-- Every subset has the rank of the vector space spanned by its actual representatives. -/
theorem vectorMatroid_eRk (v : α → V) (X : Set α) :
    (vectorMatroid (K := K) v).eRk X = (finrank K (vectorSpan (K := K) v X) : ℕ∞) := by
  obtain ⟨I, hI⟩ := (vectorMatroid (K := K) v).exists_isBasis X (subset_univ _)
  rw [hI.eRk_eq_encard, ← vectorMatroid_basis_span v hI,
    vectorSpan_finrank_of_indep v hI.indep, (Set.toFinite I).cast_ncard_eq]

/-- Matroid closure is precisely membership of the representative in the vector span. -/
theorem vectorMatroid_mem_closure (v : α → V) (X : Set α) (e : α) :
    e ∈ (vectorMatroid (K := K) v).closure X ↔ v e ∈ vectorSpan (K := K) v X := by
  obtain ⟨I, hI⟩ := (vectorMatroid (K := K) v).exists_isBasis X (subset_univ _)
  rw [← hI.closure_eq_closure, ← vectorMatroid_basis_span v hI,
    hI.indep.mem_closure_iff']
  constructor
  · rintro ⟨_, h⟩
    by_contra he
    have heI := h (hI.indep.insert he)
    exact he (subset_span ⟨e, heI, rfl⟩)
  · intro he
    refine ⟨by trivial, ?_⟩
    intro hi
    by_contra heI
    have hv : LinearIndepOn K v (insert e I) := hi
    exact ((linearIndepOn_insert heI).mp hv).2 he

end BoseBurton
