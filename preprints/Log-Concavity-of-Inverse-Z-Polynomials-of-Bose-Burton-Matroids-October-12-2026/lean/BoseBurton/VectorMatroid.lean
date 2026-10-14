import Mathlib.Combinatorics.Matroid.IndepAxioms
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.LinearIndependent.Lemmas

noncomputable section
namespace BoseBurton
open Set Submodule Module
variable {K V α : Type*} [Field K] [AddCommGroup V] [Module K V]
  [Module.Finite K V] [Finite α]

/-- The vector span of the representatives indexed by a set of points. -/
def vectorSpan (v : α → V) (I : Set α) : Submodule K V := span K (v '' I)

omit [Module.Finite K V] in
theorem vectorSpan_finrank_of_indep (v : α → V) {I : Set α}
    (hI : LinearIndepOn K v I) : finrank K (vectorSpan (K := K) v I) = I.ncard := by
  let : Fintype I := Fintype.ofFinite I
  rw [vectorSpan, Set.image_eq_range, finrank_span_eq_card hI]
  exact Set.fintypeCard_eq_ncard I

theorem vector_indep_augment (v : α → V) {I J : Set α}
    (hI : LinearIndepOn K v I) (hJ : LinearIndepOn K v J)
    (hcard : I.encard < J.encard) :
    ∃ e ∈ J, e ∉ I ∧ LinearIndepOn K v (insert e I) := by
  have hnot : ¬ v '' J ⊆ vectorSpan (K := K) v I := by
    intro h
    have hs : vectorSpan (K := K) v J ≤ vectorSpan (K := K) v I := span_le.mpr h
    have hd := Submodule.finrank_mono hs
    rw [vectorSpan_finrank_of_indep v hJ, vectorSpan_finrank_of_indep v hI] at hd
    have he : J.encard ≤ I.encard := by
      rw [← (Set.toFinite J).cast_ncard_eq, ← (Set.toFinite I).cast_ncard_eq]
      exact_mod_cast hd
    exact (not_le_of_gt hcard) he
  obtain ⟨_, ⟨e, heJ, rfl⟩, he⟩ := Set.not_subset.mp hnot
  refine ⟨e, heJ, ?_, hI.insert he⟩
  intro heI
  exact he (subset_span ⟨e, heI, rfl⟩)

/-- The finite represented matroid, with augmentation proved from vector-space dimension. -/
def vectorMatroid (v : α → V) : Matroid α :=
  (IndepMatroid.ofBddAugment univ (LinearIndepOn K v)
    (linearIndepOn_empty K v)
    (fun _ _ hJ hIJ => hJ.mono hIJ)
    (fun _ _ hI hJ hcard => vector_indep_augment (K := K) v hI hJ hcard)
    ⟨Nat.card α, fun I _ => by
      rw [← (Set.toFinite I).cast_ncard_eq]
      exact_mod_cast Set.ncard_le_card I⟩
    (fun _ _ => subset_univ _)).matroid

@[simp] theorem vectorMatroid_ground (v : α → V) : (vectorMatroid (K := K) v).E = univ := rfl
@[simp] theorem vectorMatroid_indep (v : α → V) (I : Set α) :
    (vectorMatroid (K := K) v).Indep I ↔ LinearIndepOn K v I := Iff.rfl

end BoseBurton
