import Dowling.JointContraction

noncomputable section
namespace Dowling
open scoped Classical
variable {G : Type*} [Group G] [Fintype G] {n : ℕ}

omit [Fintype G] in
theorem jointPartition_code_none (i j : Fin n) :
    (jointPartition (G := G) i).code j=none ↔ j=i := by
  rw [jointPartition_code]
  by_cases h : j=i <;> simp [h]

omit [Fintype G] in
theorem jointPartition_code_some_root (i j r : Fin n) (g : G)
    (h : (jointPartition (G := G) i).code j=some (r,g)) : j=r := by
  rw [jointPartition_code] at h
  split at h
  · cases h
  · exact (Prod.mk.inj (Option.some.inj h)).1

omit [Fintype G] in
theorem flatEdges_jointPartition {X : Set (Fin n)} (i : Fin n) (hi : i∈X) :
    flatEdges X (jointPartition (G := G) i)={Sum.inl i} := by
  ext e
  cases e with
  | inl j =>
    rw [flatEdges_joint,jointPartition_code_none]
    simp only [Set.mem_singleton_iff,Sum.inl.injEq]
    exact ⟨fun h => h.2,fun h => ⟨h ▸ hi,h⟩⟩
  | inr e =>
    rw [flatEdges_link]
    simp only [Set.mem_singleton_iff,Sum.inr_ne_inl,iff_false]
    rintro (⟨ht,hh⟩ | ⟨r,a,b,ht,hh,_⟩)
    · exact e.ordered.ne (((jointPartition_code_none i e.tail).mp ht).trans
        ((jointPartition_code_none i e.head).mp hh).symm)
    · exact e.ordered.ne ((jointPartition_code_some_root i e.tail r a ht).trans
        (jointPartition_code_some_root i e.head r b hh).symm)

theorem joint_isFlat {X : Set (Fin n)} (i : Fin n) (hi : i∈X) :
    (matroid G n X).IsFlat {Sum.inl i} := by
  rw [← flatEdges_jointPartition (G := G) i hi]
  exact flatEdges_isFlat X _ (jointPartition_admissible i hi)

omit [Fintype G] in
/-- Restricting the available joints changes no link equations. -/
theorem flatEdges_remove_joint (X : Set (Fin n)) (p : GainPartition G n) (i : Fin n) :
    flatEdges (X\{i}) p=flatEdges X p\{Sum.inl i} := by
  ext e
  cases e with
  | inl j => simp only [flatEdges_joint,Set.mem_sdiff,Set.mem_singleton_iff,Sum.inl.injEq]; tauto
  | inr e => simp only [flatEdges_link,Set.mem_sdiff,Set.mem_singleton_iff,Sum.inr_ne_inl,not_false_eq_true,and_true]

end Dowling
