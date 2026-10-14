import Dowling.ReleaseZeroBlockFlats

noncomputable section
namespace Dowling
open scoped Classical
variable {G : Type*} [Group G] [Subsingleton G] [Fintype G] {n : ℕ}

/-- The complete order-one correction set uses another retained mark, rather
than the size-two zero-block condition valid for nontrivial gain groups. -/
theorem joint_correction_flats_trivial (X : Set (Fin n)) (p : GainPartition G n)
    (i : Fin n) (hiX : i∈X) :
    (Sum.inl i ∈ flatEdges X p ∧
      ¬ (matroid G n X).IsFlat (flatEdges X p\{Sum.inl i})) ↔
      p.code i=none ∧ ∃ j∈X, j≠i ∧ p.code j=none := by
  constructor
  · rintro ⟨hmem,hnflat⟩
    have hi := ((flatEdges_joint X p i).mp hmem).2
    refine ⟨hi,?_⟩
    by_contra h
    have hmark : ∀ j∈X, p.code j=none → j=i := by
      intro j hjX hj
      by_contra hji
      exact h ⟨j,hjX,hji,hj⟩
    obtain ⟨r,hr,hmin⟩ := p.exists_least_zero ⟨i,hi⟩
    apply hnflat
    rw [← flatEdges_releaseZeroBlock p r hr hmin X i hmark]
    apply flatEdges_isFlat
    intro j hj
    exact False.elim (p.releaseZeroBlock_no_zero r hr hmin j hj)
  · rintro ⟨hi,j,hjX,hji,hj⟩
    refine ⟨(flatEdges_joint X p i).mpr ⟨hiX,hi⟩,?_⟩
    apply remove_joint_not_flat_of_admissible X p i hiX hi
    intro a _
    exact Or.inl ⟨j,⟨hjX,hji⟩,hj⟩

end Dowling
