import BoseBurton.FlagCountingEquiv

noncomputable section
namespace BoseBurton
open Submodule Module Finset
open scoped Classical
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]

abbrev NondeletedRankSubspace (W : Submodule K V) (d : ℕ) :=
  {U : Submodule K V // finrank K U = d ∧ ¬ U ≤ W}
abbrev DeletedRankSubspace (W : Submodule K V) (h : ℕ) :=
  {I : Submodule K V // I ≤ W ∧ finrank K I = h}
abbrev UpperNondeletedRank (W I : Submodule K V) (d : ℕ) :=
  {U : Submodule K V // I ≤ U ∧ finrank K U = d ∧ ¬ U ≤ W}

/-- Counting the same actual flag `(I,U)` by its upper or lower subspace. -/
def flagPairEquiv (W : Submodule K V) (d h : ℕ) :
    (Σ U : NondeletedRankSubspace W d,
      {S : Submodule K (W.comap U.1.subtype) // finrank K S = h}) ≃
    (Σ I : DeletedRankSubspace W h, UpperNondeletedRank W I.1 d) :=
  (Equiv.sigmaCongrRight (fun U : NondeletedRankSubspace W d => intersectionRankEquiv W U.1 h)).trans
    { toFun := fun p => ⟨⟨p.2.1, p.2.2.1, p.2.2.2.2⟩,
        ⟨p.1.1, p.2.2.2.1, p.1.2.1, p.1.2.2⟩⟩
      invFun := fun p => ⟨⟨p.2.1, p.2.2.2.1, p.2.2.2.2⟩,
        ⟨p.1.1, p.1.2.1, p.2.2.1, p.1.2.2⟩⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }

variable [Finite V]

theorem flag_pair_count (W : Submodule K V) (d h : ℕ) :
    (∑ U : NondeletedRankSubspace W d,
      Nat.card {S : Submodule K (W.comap U.1.subtype) // finrank K S = h}) =
    ∑ I : DeletedRankSubspace W h, Nat.card (UpperNondeletedRank W I.1 d) := by
  have he := Nat.card_congr (flagPairEquiv W d h)
  rw [Nat.card_sigma, Nat.card_sigma] at he
  exact he

end BoseBurton
