import Dowling.ReleaseSingletonFlats

noncomputable section
namespace Dowling
open scoped Classical
variable {G : Type*} [Group G] [Fintype G] {n : ℕ}

/-- If the deleted-joint equations still realize the same zero block, that
joint lies in the original closure and its removal cannot be an old flat. -/
theorem remove_joint_not_flat_of_admissible (X : Set (Fin n)) (p : GainPartition G n)
    (i : Fin n) (hiX : i∈X) (hi : p.code i=none)
    (hp : Admissible (X\{i}) p) :
    ¬ (matroid G n X).IsFlat (flatEdges X p\{Sum.inl i}) := by
  intro hflat
  have he : Sum.inl i ∈ (matroid G n X).closure (flatEdges X p\{Sum.inl i}) := by
    apply (matroid_mem_closure X _
      (Set.Subset.trans Set.sdiff_subset (flatEdges_subset_ground X p)) _).mpr
    refine ⟨?_,hiX⟩
    intro x hx
    rw [← flatEdges_remove_joint,flatEdges_solutions _ _ hp] at hx
    exact ((p.mem_solutionSet x).mp hx).1 i hi
  rw [hflat.closure] at he
  exact he.2 (Set.mem_singleton _)

omit [Fintype G] in
theorem admissible_remove_joint_nontrivial [Nontrivial G] (X : Set (Fin n))
    (p : GainPartition G n) (i : Fin n) (hi : p.code i=none)
    (hj : ∃ j, j≠i ∧ p.code j=none) : Admissible (X\{i}) p := by
  obtain ⟨j,hji,hj⟩ := hj
  intro a _
  right
  refine ⟨inferInstance,?_⟩
  by_cases hai : a=i
  · exact ⟨j,by simpa only [hai] using hji,hj⟩
  · exact ⟨i,Ne.symm hai,hi⟩

/-- Complete correction-flat classification for every nontrivial finite gain
group. No outside balanced block is silently omitted from this set. -/
theorem joint_correction_flats_nontrivial [Nontrivial G]
    (X : Set (Fin n)) (p : GainPartition G n) (i : Fin n) (hiX : i∈X) :
    (Sum.inl i ∈ flatEdges X p ∧
      ¬ (matroid G n X).IsFlat (flatEdges X p\{Sum.inl i})) ↔
      p.code i=none ∧ ∃ j, j≠i ∧ p.code j=none := by
  constructor
  · rintro ⟨hmem,hnflat⟩
    have hi := ((flatEdges_joint X p i).mp hmem).2
    refine ⟨hi,?_⟩
    by_contra h
    have hz : ∀ j, p.code j=none → j=i := by
      intro j hj
      by_contra hji
      exact h ⟨j,hji,hj⟩
    apply hnflat
    rw [← flatEdges_releaseSingleton p i hi hz X]
    exact flatEdges_isFlat X _ (p.releaseSingleton_admissible i hi hz X)
  · rintro ⟨hi,hj⟩
    exact ⟨(flatEdges_joint X p i).mpr ⟨hiX,hi⟩,
      remove_joint_not_flat_of_admissible X p i hiX hi
        (admissible_remove_joint_nontrivial X p i hi hj)⟩

end Dowling
