import BoseBurton.RankedSpaces

noncomputable section
namespace BoseBurton
open Finset Submodule Module
open scoped Classical
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V] [Finite V]
variable {R : Type*} [AddCommMonoid R]

/-- The flat sum separates the empty flat from precisely the subspaces not deleted. -/
theorem sum_flatSpan (W : Submodule K V) (f : Submodule K V → R) :
    (∑ F : FlatSpan W, f F.1) = f ⊥ + ∑ U ∈ univ.filter (fun U => ¬ U ≤ W), f U := by
  classical
  rw [← Finset.sum_subtype (p := fun U : Submodule K V => U = ⊥ ∨ ¬ U ≤ W)
    (univ.filter (fun U => U = ⊥ ∨ ¬ U ≤ W)) (by simp) f]
  have hf : univ.filter (fun U : Submodule K V => U = ⊥ ∨ ¬ U ≤ W) =
      insert ⊥ (univ.filter (fun U => ¬ U ≤ W)) := by
    ext U
    simp
  rw [hf, sum_insert (by simp)]

/-- Subspaces contained in `W` are counted by their actual subspaces inside `W`. -/
theorem sum_subspaces_contained (W : Submodule K V) (f : Submodule K V → R) :
    (∑ U ∈ univ.filter (fun U => U ≤ W), f U) =
      ∑ T : Submodule K W, f (T.map W.subtype) := by
  classical
  rw [Finset.sum_subtype (p := fun U : Submodule K V => U ≤ W)
    (univ.filter (fun U => U ≤ W)) (by simp) f]
  exact ((MapSubtype.orderIso W).toEquiv.sum_comp (fun U => f U.1)).symm

end BoseBurton
