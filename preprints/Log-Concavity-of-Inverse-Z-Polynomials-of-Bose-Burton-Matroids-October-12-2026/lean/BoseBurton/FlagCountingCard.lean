import BoseBurton.FlagCountingUpper
import BoseBurton.SubspaceCountingSums

noncomputable section
namespace BoseBurton
open Submodule Module Finset
open scoped Classical
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
  [Fintype K] [Module.Finite K V] [Finite V]

 theorem upper_rank_count (I : Submodule K V) (d : ℕ) (hd : finrank K I ≤ d) :
    (Nat.card (UpperRankSubspace I d) : ℝ) =
      gaussian (Fintype.card K : ℝ) (finrank K V-finrank K I) (d-finrank K I) := by
  rw [← Nat.card_congr (upperRankEquiv I d hd), subspace_count_gaussian_all]
  have h := Submodule.finrank_quotient_add_finrank I
  congr 1
  omega

theorem contained_upper_rank_count (W I : Submodule K V) (hIW : I ≤ W)
    (d : ℕ) (hd : finrank K I ≤ d) :
    (Nat.card (ContainedUpperRank W I d) : ℝ) =
      gaussian (Fintype.card K : ℝ) (finrank K W-finrank K I) (d-finrank K I) := by
  have hr := (Submodule.comapSubtypeEquivOfLe hIW).finrank_eq
  rw [← Nat.card_congr (containedUpperRankEquiv W I hIW d),
    upper_rank_count (I.comap W.subtype) d (by rw [hr]; exact hd), hr]

theorem upper_nondeleted_rank_count (W I : Submodule K V) (hIW : I ≤ W)
    (d : ℕ) (hd : finrank K I ≤ d) :
    (Nat.card (UpperNondeletedRank W I d) : ℝ) =
      gaussian (Fintype.card K : ℝ) (finrank K V-finrank K I) (d-finrank K I) -
      gaussian (Fintype.card K : ℝ) (finrank K W-finrank K I) (d-finrank K I) := by
  have he := Nat.card_congr (upperRankPartitionEquiv W I d)
  rw [Nat.card_sum] at he
  have heR := congrArg (fun n : ℕ => (n : ℝ)) he
  rw [Nat.cast_add, upper_rank_count I d hd, contained_upper_rank_count W I hIW d hd] at heR
  linarith

theorem deleted_rank_count (W : Submodule K V) (h : ℕ) :
    (Nat.card (DeletedRankSubspace W h) : ℝ) = gaussian (Fintype.card K : ℝ) (finrank K W) h := by
  rw [← Nat.card_congr (containedRankEquiv W h), subspace_count_gaussian_all]

theorem nondeleted_rank_count (W : Submodule K V) (d : ℕ) :
    (Nat.card (NondeletedRankSubspace W d) : ℝ) =
      gaussian (Fintype.card K : ℝ) (finrank K V) d -
      gaussian (Fintype.card K : ℝ) (finrank K W) d := by
  have e : NondeletedRankSubspace W d ≃ UpperNondeletedRank W ⊥ d :=
    Equiv.subtypeEquivRight (fun U => by simp)
  rw [Nat.card_congr e, upper_nondeleted_rank_count W ⊥ bot_le d (by simp)]
  simp

/-- The source's flag-pair identity with its actual multiplicities, including zero cases. -/
theorem flag_pair_gaussian (W : Submodule K V) (d h : ℕ) (hhd : h ≤ d) :
    (∑ U : NondeletedRankSubspace W d,
      (Nat.card {S : Submodule K (W.comap U.1.subtype) // finrank K S = h} : ℝ)) =
      gaussian (Fintype.card K : ℝ) (finrank K W) h *
        (gaussian (Fintype.card K : ℝ) (finrank K V-h) (d-h) -
          gaussian (Fintype.card K : ℝ) (finrank K W-h) (d-h)) := by
  have he := congrArg (fun n : ℕ => (n : ℝ)) (flag_pair_count W d h)
  simp only [Nat.cast_sum] at he
  rw [he]
  calc
    _ = ∑ _I : DeletedRankSubspace W h,
        (gaussian (Fintype.card K : ℝ) (finrank K V-h) (d-h) -
          gaussian (Fintype.card K : ℝ) (finrank K W-h) (d-h)) := by
      apply sum_congr rfl
      intro I _
      rw [upper_nondeleted_rank_count W I.1 I.2.1 d (by rw [I.2.2]; exact hhd), I.2.2]
    _ = _ := by
      rw [sum_const, nsmul_eq_mul, card_univ, ← Nat.card_eq_fintype_card, deleted_rank_count]

end BoseBurton
