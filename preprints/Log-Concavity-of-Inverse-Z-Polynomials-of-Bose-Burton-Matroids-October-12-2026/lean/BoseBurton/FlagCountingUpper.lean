import BoseBurton.FlagCountingPairs

noncomputable section
namespace BoseBurton
open Submodule Module
open scoped Classical
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V] [Module.Finite K V]

abbrev UpperRankSubspace (I : Submodule K V) (d : ℕ) :=
  {U : Submodule K V // I ≤ U ∧ finrank K U = d}
abbrev ContainedUpperRank (W I : Submodule K V) (d : ℕ) :=
  {U : Submodule K V // I ≤ U ∧ U ≤ W ∧ finrank K U = d}

/-- Genuine quotient subspaces enumerate every upper flag of a prescribed rank. -/
def upperRankEquiv (I : Submodule K V) (d : ℕ) (hd : finrank K I ≤ d) :
    {S : Submodule K (V ⧸ I) // finrank K S = d-finrank K I} ≃ UpperRankSubspace I d :=
  ((I.comapMkQRelIso).toEquiv.subtypeEquiv
    (q := fun T : Set.Ici I => finrank K T.1 = d) (fun S => by
      change finrank K S = d-finrank K I ↔ finrank K (S.comap I.mkQ) = d
      rw [finrank_comap_mkQ]
      omega)).trans
    { toFun := fun S => ⟨S.1.1, S.1.2, S.2⟩
      invFun := fun U => ⟨⟨U.1, U.2.1⟩, U.2.2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }

/-- Flags contained in `W` are precisely the corresponding upper flags inside `W`. -/
def containedUpperRankEquiv (W I : Submodule K V) (hIW : I ≤ W) (d : ℕ) :
    UpperRankSubspace (I.comap W.subtype) d ≃ ContainedUpperRank W I d :=
  ((MapSubtype.orderIso W).toEquiv.subtypeEquiv
    (q := fun T : {T : Submodule K V // T ≤ W} => I ≤ T.1 ∧ finrank K T.1 = d)
    (fun S => by
      have he : (I.comap W.subtype).map W.subtype = I := by
        rw [map_comap_subtype, inf_eq_right.mpr hIW]
      change (I.comap W.subtype ≤ S ∧ finrank K S = d) ↔
        (I ≤ S.map W.subtype ∧ finrank K (S.map W.subtype) = d)
      rw [← he, map_le_map_iff_of_injective W.subtype_injective,
        ← (Submodule.equivMapOfInjective W.subtype W.subtype_injective S).finrank_eq]
      rw [Submodule.comap_map_eq_of_injective W.subtype_injective])).trans
    { toFun := fun S => ⟨S.1.1, S.2.1, S.1.2, S.2.2⟩
      invFun := fun U => ⟨⟨U.1, U.2.2.1⟩, U.2.1, U.2.2.2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }

/-- The removed upper flags and surviving upper flags partition all upper flags. -/
def upperRankPartitionEquiv (W I : Submodule K V) (d : ℕ) :
    UpperRankSubspace I d ≃ ContainedUpperRank W I d ⊕ UpperNondeletedRank W I d where
  toFun U := if h : U.1 ≤ W then Sum.inl ⟨U.1, U.2.1, h, U.2.2⟩
    else Sum.inr ⟨U.1, U.2.1, U.2.2, h⟩
  invFun
    | Sum.inl U => ⟨U.1, U.2.1, U.2.2.2⟩
    | Sum.inr U => ⟨U.1, U.2.1, U.2.2.1⟩
  left_inv U := by
    by_cases h : U.1 ≤ W
    · simp only [dite_eq_left h]
    · simp only [dite_eq_right h]
  right_inv U := by
    cases U with
    | inl U => simp only [dite_eq_left U.2.2.1]
    | inr U => simp only [dite_eq_right U.2.2.2]

end BoseBurton
