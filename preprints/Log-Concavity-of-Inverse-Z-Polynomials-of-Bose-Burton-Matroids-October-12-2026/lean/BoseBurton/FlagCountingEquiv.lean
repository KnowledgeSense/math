import BoseBurton.RankEnumeratorCoefficients
import BoseBurton.QuotientRanks

noncomputable section
namespace BoseBurton
open Submodule Module
variable {K V V' : Type*} [Field K] [AddCommGroup V] [Module K V]
  [AddCommGroup V'] [Module K V']

/-- Linear isomorphisms preserve the actual sets of subspaces of each dimension. -/
def linearEquivRankSubspaces (e : V ≃ₗ[K] V') (h : ℕ) :
    {U : Submodule K V // finrank K U = h} ≃
      {T : Submodule K V' // finrank K T = h} :=
  (Submodule.orderIsoMapComap e).toEquiv.subtypeEquiv (fun U => by
    change finrank K U = h ↔ finrank K (U.map e.toLinearMap) = h
    rw [← (e.submoduleMap U).finrank_eq])

/-- Subspaces inside `U` correspond to ambient subspaces contained in `U`, with rank intact. -/
def containedRankEquiv (U : Submodule K V) (h : ℕ) :
    {S : Submodule K U // finrank K S = h} ≃
      {I : Submodule K V // I ≤ U ∧ finrank K I = h} :=
  ((MapSubtype.orderIso U).toEquiv.subtypeEquiv
    (q := fun T : {T : Submodule K V // T ≤ U} => finrank K T.1 = h) (fun S => by
    change finrank K S = h ↔ finrank K (S.map U.subtype) = h
    rw [← (Submodule.equivMapOfInjective U.subtype U.subtype_injective S).finrank_eq])).trans
    { toFun := fun S => ⟨S.1.1, S.1.2, S.2⟩
      invFun := fun I => ⟨⟨I.1, I.2.1⟩, I.2.2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }

/-- The deleted subspace inside a restriction is literally the ambient intersection. -/
def deletedIntersectionEquiv (W U : Submodule K V) : (W.comap U.subtype) ≃ₗ[K] ↥(U ⊓ W) where
  toFun x := ⟨x.1.1, x.1.2, x.2⟩
  invFun x := ⟨⟨x.1, x.2.1⟩, x.2.2⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- The inner cardinality in the source flag count counts actual `I ≤ U ∩ W`. -/
def intersectionRankEquiv (W U : Submodule K V) (h : ℕ) :
    {S : Submodule K (W.comap U.subtype) // finrank K S = h} ≃
      {I : Submodule K V // I ≤ W ∧ I ≤ U ∧ finrank K I = h} :=
  ((linearEquivRankSubspaces (deletedIntersectionEquiv W U) h).trans
    (containedRankEquiv (U ⊓ W) h)).trans
      (Equiv.subtypeEquivRight (fun I => by simp only [le_inf_iff]; tauto))

end BoseBurton
