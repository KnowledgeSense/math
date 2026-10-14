import BoseBurton.FlatOrder
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

noncomputable section
namespace BoseBurton
open Submodule Module
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V] [Module.Finite K V]

instance quotientFinite (U : Submodule K V) [Finite V] : Finite (V ⧸ U) :=
  Finite.of_surjective U.mkQ U.mkQ_surjective

/-- The quotient correspondence preserves interval rank differences. -/
theorem finrank_comap_mkQ (U : Submodule K V) (S : Submodule K (V ⧸ U)) :
    finrank K (S.comap U.mkQ) = finrank K S + finrank K U := by
  let T := S.comap U.mkQ
  have h := (U.mkQ.domRestrict T).finrank_range_add_finrank_ker
  rw [LinearMap.range_domRestrict, LinearMap.ker_domRestrict, Submodule.ker_mkQ] at h
  have hmap : T.map U.mkQ = S := Submodule.map_comap_eq_self (by simp)
  rw [hmap, (Submodule.comapSubtypeEquivOfLe (Submodule.le_comap_mkQ U S)).finrank_eq] at h
  exact h.symm

theorem finrank_comap_mkQ_sub (U : Submodule K V) (S T : Submodule K (V ⧸ U)) :
    finrank K (T.comap U.mkQ) - finrank K (S.comap U.mkQ) =
      finrank K T - finrank K S := by
  rw [finrank_comap_mkQ, finrank_comap_mkQ, Nat.add_sub_add_right]

end BoseBurton
