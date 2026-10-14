import BoseBurton.RankedSpaces
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.LinearAlgebra.Dual.Basis
import BoseBurton.ZIncidenceConvolution

noncomputable section
namespace BoseBurton
open Submodule Module Finset Polynomial
variable (K V : Type*) [Field K] [AddCommGroup V] [Module K V] [Module.Finite K V]

def projectiveSelfDualEquiv : V ≃ₗ[K] Dual K V :=
  (Module.Free.chooseBasis K V).toDualEquiv

/-- An actual bijection of subspaces reversing dimension, from annihilator duality. -/
def projectiveRankReverse : Submodule K V ≃ Submodule K V :=
  (Subspace.orderIsoFiniteDimensional (K:=K) (V:=V)).toEquiv.trans
    (Submodule.orderIsoMapComap (projectiveSelfDualEquiv K V).symm).toEquiv

theorem projectiveRankReverse_finrank (U : Submodule K V) :
    finrank K (projectiveRankReverse K V U)=finrank K V-finrank K U := by
  change finrank K (U.dualAnnihilator.map (projectiveSelfDualEquiv K V).symm.toLinearMap)=_
  rw [← ((projectiveSelfDualEquiv K V).symm.submoduleMap U.dualAnnihilator).finrank_eq]
  have h := Subspace.finrank_add_finrank_dualAnnihilator_eq U
  omega

variable [Finite V]

def projectiveRankEnumerator : Polynomial ℤ := ∑ U : Submodule K V,X^(finrank K U)

theorem projectiveRankEnumerator_reflect :
    reflect (finrank K V) (projectiveRankEnumerator K V)=projectiveRankEnumerator K V := by
  classical
  rw [projectiveRankEnumerator,MatroidInverseZ.reflect_finset_sum]
  have he := (projectiveRankReverse K V).sum_comp (fun U : Submodule K V=>(X:Polynomial ℤ)^(finrank K U))
  rw [← he]
  apply sum_congr rfl
  intro U _
  rw [reflect_monomial,revAt_le (Submodule.finrank_le U),projectiveRankReverse_finrank]

end BoseBurton
