import BoseBurton.FlatOrder
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

noncomputable section
namespace BoseBurton
open Set Submodule Module
open scoped LinearAlgebra.Projectivization
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]

/-- With no deleted projective point, all vector subspaces occur. -/
def unpuncturedSpanOrderIso : FlatSpan (⊥ : Submodule K V) ≃o Submodule K V where
  toFun U := U.1
  invFun U := ⟨U, by by_cases h : U = ⊥; exact Or.inl h; exact Or.inr (by simpa using h)⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_rel_iff' := Iff.rfl

@[simp] theorem survivingPoints_bot : survivingPoints (⊥ : Submodule K V) = univ := by
  ext p
  simp [survivingPoints, Projectivization.rep_nonzero]

variable [Module.Finite K V] [Finite V]

@[simp] theorem matroid_bot : matroid (⊥ : Submodule K V) = projectiveMatroid K V := by
  rw [matroid, survivingPoints_bot]
  change (projectiveMatroid K V).restrict (projectiveMatroid K V).E = _
  exact Matroid.restrict_ground_eq_self _

/-- The genuine projective matroid flat lattice is the full vector-subspace lattice. -/
def projectiveFlatOrderIso : MatroidInverseZ.Flat (projectiveMatroid K V) ≃o Submodule K V := by
  rw [← matroid_bot]
  exact (flatSpanOrderIso (⊥ : Submodule K V)).trans unpuncturedSpanOrderIso

omit [Finite V] in

theorem flatSpanRank_strictMono (W : Submodule K V) :
    StrictMono (fun U : FlatSpan W => finrank K U.1) := by
  intro U T h
  exact Submodule.finrank_lt_finrank_of_lt h

end BoseBurton
