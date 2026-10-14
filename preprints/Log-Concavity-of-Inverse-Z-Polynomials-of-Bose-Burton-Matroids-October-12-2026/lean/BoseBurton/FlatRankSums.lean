import BoseBurton.FlagCountingPairs

noncomputable section
namespace BoseBurton
open Finset Submodule Module
open scoped Classical
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
  [Module.Finite K V] [Finite V]

omit [Finite V] in
theorem nondeleted_rank_pos (W U : Submodule K V) (hU : ¬ U ≤ W) : 0 < finrank K U := by
  have hne : U ≠ ⊥ := fun h => hU (h ▸ bot_le)
  simpa only [finrank_bot] using
    Submodule.finrank_lt_finrank_of_lt (bot_lt_iff_ne_bot.mpr hne)

/-- Group the complete actual surviving-flat sum by its genuine rank. -/
theorem nondeleted_sum_by_rank {R : Type*} [AddCommMonoid R]
    (W : Submodule K V) (f : Submodule K V → R) :
    (∑ U ∈ univ.filter (fun U : Submodule K V => ¬ U ≤ W), f U) =
      ∑ d ∈ Icc 1 (finrank K V), ∑ U : NondeletedRankSubspace W d, f U.1 := by
  have hm : ∀ U ∈ univ.filter (fun U : Submodule K V => ¬ U ≤ W),
      finrank K U ∈ Icc 1 (finrank K V) := by
    intro U hU
    exact mem_Icc.mpr ⟨nondeleted_rank_pos W U (mem_filter.mp hU).2, Submodule.finrank_le U⟩
  rw [← sum_fiberwise_of_maps_to hm f]
  apply sum_congr rfl
  intro d _
  have he : (univ.filter (fun U : Submodule K V => ¬ U ≤ W)).filter (fun U : Submodule K V => finrank K U = d) =
      univ.filter (fun U : Submodule K V => finrank K U = d ∧ ¬ U ≤ W) := by
    ext U
    simp [and_comm]
  rw [he]
  exact Finset.sum_subtype _ (by simp) f

end BoseBurton
