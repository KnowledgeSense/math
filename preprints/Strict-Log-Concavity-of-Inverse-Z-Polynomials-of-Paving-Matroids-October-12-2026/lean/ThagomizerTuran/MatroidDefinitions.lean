import ThagomizerTuran.IncidenceDefinitions

/-! Attach the interval construction to the actual flats of a finite matroid. -/
namespace MatroidInverseZ

variable {α : Type*} [Fintype α]

/-- The actual flat poset; no proposed coefficient formula is part of this object. -/
abbrev Flat (M : Matroid α) := {F : Set α // M.IsFlat F}

noncomputable instance flatFintype (M : Matroid α) : Fintype (Flat M) :=
  Fintype.ofFinite _

noncomputable instance flatDecidableEq (M : Matroid α) : DecidableEq (Flat M) :=
  Classical.decEq _

noncomputable instance flatLocallyFiniteOrder (M : Matroid α) : LocallyFiniteOrder (Flat M) := by
  classical
  exact Fintype.toLocallyFiniteOrder

/-- The finite rank of an actual flat. -/
noncomputable def flatRank (M : Matroid α) (F : Flat M) : ℕ :=
  (M.eRk F.val).toNat

/-- Least actual flat, retaining the correct convention for loops. -/
noncomputable def bottomFlat (M : Matroid α) : Flat M :=
  ⟨M.closure ∅, M.isFlat_closure ∅⟩

/-- Greatest actual flat. -/
def topFlat (M : Matroid α) : Flat M := ⟨M.E, M.ground_isFlat⟩

/-- The recursive inverse-Z construction evaluated on the actual flat lattice.
Its equivalence with the full KL characterization remains a separate proof obligation. -/
noncomputable def matroidInverseZ (M : Matroid α) : Polynomial ℤ :=
  inverseZ (flatRank M) (bottomFlat M) (topFlat M)

end MatroidInverseZ
