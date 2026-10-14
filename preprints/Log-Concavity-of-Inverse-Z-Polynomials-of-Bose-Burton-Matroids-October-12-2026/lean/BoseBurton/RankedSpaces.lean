import BoseBurton.ProjectiveOrder

noncomputable section
namespace BoseBurton
open Submodule Module
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V] [Finite V]

noncomputable instance subspaceFintype : Fintype (Submodule K V) := Fintype.ofFinite _
noncomputable instance subspaceLocallyFiniteOrder : LocallyFiniteOrder (Submodule K V) := by
  classical
  exact Fintype.toLocallyFiniteOrder
noncomputable instance flatSpanFintype (W : Submodule K V) : Fintype (FlatSpan W) := Fintype.ofFinite _
noncomputable instance flatSpanLocallyFiniteOrder (W : Submodule K V) : LocallyFiniteOrder (FlatSpan W) := by
  classical
  exact Fintype.toLocallyFiniteOrder

variable [Module.Finite K V]

/-- The rank on the proved Bose–Burton flat-span model. -/
def spanRank (W : Submodule K V) (U : FlatSpan W) : ℕ := finrank K U.1

def spanTop (W : Submodule K V) (hW : W ≠ ⊤) : FlatSpan W :=
  ⟨⊤, Or.inr (by simpa using hW)⟩

omit [Finite V] [Module.Finite K V] in
@[simp] theorem spanRank_bot (W : Submodule K V) : spanRank W ⊥ = 0 := finrank_bot K V
omit [Finite V] [Module.Finite K V] in
@[simp] theorem spanRank_top (W : Submodule K V) (hW : W ≠ ⊤) :
    spanRank W (spanTop W hW) = finrank K V := finrank_top K V

omit [Finite V] in
theorem spanRank_strictMono (W : Submodule K V) : StrictMono (spanRank W) :=
  flatSpanRank_strictMono W

/-- The actual interval inverse-Z, now on its proved rank-preserving subspace model. -/
def spanY (W : Submodule K V) (hW : W ≠ ⊤) : Polynomial ℤ := by
  classical
  exact MatroidInverseZ.inverseZ (spanRank W) ⊥ (spanTop W hW)

def spanP (W : Submodule K V) (hW : W ≠ ⊤) : Polynomial ℤ := by
  classical
  exact MatroidInverseZ.kl (spanRank W) (spanTop W hW) ⊥

/-- Projective interval invariants, including the zero-dimensional quotient. -/
def projectiveY (K V : Type*) [Field K] [AddCommGroup V] [Module K V]
    [Module.Finite K V] [Finite V] : Polynomial ℤ := by
  classical
  exact MatroidInverseZ.inverseZ (fun U : Submodule K V => finrank K U) ⊥ ⊤

def projectiveP (K V : Type*) [Field K] [AddCommGroup V] [Module K V]
    [Module.Finite K V] [Finite V] : Polynomial ℤ := by
  classical
  exact MatroidInverseZ.kl (fun U : Submodule K V => finrank K U) ⊤ ⊥

end BoseBurton
